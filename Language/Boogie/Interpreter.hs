{-# LANGUAGE FlexibleContexts, Rank2Types #-}

-- | Interpreter for Boogie 2
module Language.Boogie.Interpreter (
  -- * Executing programs
  executeProgramDet,
  executeProgram,
  executeProgramGeneric,
  -- * Run-time failures
  FailureSource (..),
  -- InternalCode,
  StackFrame (..),
  StackTrace,
  RuntimeFailure (..),  
  runtimeFailureDoc,
  FailureKind (..),
  failureKind,
  -- * Execution outcomes
  TestCase (..),
  isPass,
  isInvalid,
  isNonexecutable,
  isFail,
  testCaseSummary,  
  finalStateDoc,
  Summary (..),
  testSessionSummary,
  summaryDoc,
  -- * Executing parts of programs
  eval,
  exec,
  execProcedure,
  preprocess
  ) where

import Language.Boogie.Environment  
import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Heap
import Language.Boogie.Generator
import Language.Boogie.Intervals
import Language.Boogie.Position
import Language.Boogie.Tokens (nonIdChar)
import Language.Boogie.PrettyPrinter
import Language.Boogie.TypeChecker
import Language.Boogie.NormalForm
import Language.Boogie.BasicBlocks
import Data.Maybe
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad.Error hiding (join)
import Control.Applicative hiding (empty)
import Control.Monad.State hiding (join)
import Control.Monad.Identity hiding (join)
import Control.Monad.Stream
import Control.Lens hiding (Context, at)
import Text.PrettyPrint

{- Interface -}

-- | 'executeProgram' @p tc entryPoint@ :
-- Execute program @p@ /non-deterministically/ in type context @tc@ starting from procedure @entryPoint@ 
-- and return an infinite list of possible outcomes (each either runtime failure or the final variable store).
-- Whenever a value is unspecified, all values of the required type are tried exhaustively.
executeProgram :: Program -> Context -> Generator Stream -> Maybe Integer -> Id -> [TestCase]
executeProgram p tc gen qbound entryPoint = toList $ executeProgramGeneric p tc gen qbound entryPoint

-- | 'executeProgramDet' @p tc entryPoint@ :
-- Execute program @p@ /deterministically/ in type context @tc@ starting from procedure @entryPoint@ 
-- and return a single outcome.
-- Whenever a value is unspecified, a default value of the required type is used.
executeProgramDet :: Program -> Context -> Maybe Integer -> Id -> TestCase
executeProgramDet p tc qbound entryPoint = runIdentity $ executeProgramGeneric p tc defaultGenerator qbound entryPoint
      
-- | 'executeProgramGeneric' @p tc generator qbound entryPoint@ :
-- Execute program @p@ in type context @tc@ with input generator @generator@, starting from procedure @entryPoint@,
-- and return the outcome(s) embedded into the generator's monad.
executeProgramGeneric :: (Monad m, Functor m) => Program -> Context -> Generator m -> Maybe Integer -> Id -> m (TestCase)
executeProgramGeneric p tc generator qbound entryPoint = result <$> runStateT (runErrorT programExecution) (initEnv tc generator qbound)
  where
    programExecution = do
      execUnsafely $ preprocess p
      execRootCall
    sig = procSig entryPoint tc
    execRootCall = do
      let params = psigParams sig
      let defaultBinding = M.fromList $ zip (psigTypeVars sig) (repeat defaultType)
      let paramTypes = map (typeSubst defaultBinding) (map itwType params)
      envTypeContext %= setLocals (M.fromList $ zip (map itwId params) paramTypes)
      execCallBySig (assumePreconditions sig) (map itwId (psigRets sig)) (map (gen . Var . itwId) (psigArgs sig)) noPos
    defaultType = BoolType      
    result (Left err, env) = TestCase sig (env^.envMemory) (Just err)
    result (_, env)      = TestCase sig (env^.envMemory) Nothing    
            
{- Executions -}

-- | Computations with 'Environment' as state, which can result in either @a@ or 'RuntimeFailure'
type Execution m a = ErrorT RuntimeFailure (StateT (Environment m) m) a

-- | Computations with 'Environment' as state, which always result in @a@
type SafeExecution m a = StateT (Environment m) m a

-- | 'execUnsafely' @computation@ : Execute a safe @computation@ in an unsafe environment
execUnsafely :: (Monad m, Functor m) => SafeExecution m a -> Execution m a
execUnsafely computation = ErrorT (Right <$> computation)

-- | 'execSafely' @computation handler@ : Execute an unsafe @computation@ in a safe environment, handling errors that occur in @computation@ with @handler@
execSafely :: (Monad m, Functor m) => Execution m a -> (RuntimeFailure -> SafeExecution m a) -> SafeExecution m a
execSafely computation handler = do
  eres <- runErrorT computation
  either handler return eres
  
-- | Computations that perform a cleanup at the end
class Monad s => Finalizer s where
  finally :: s a -> s () -> s a
    
instance Monad m => Finalizer (StateT s m) where
  finally main cleanup = do
    res <- main
    cleanup
    return res

instance (Error e, Monad m) => Finalizer (ErrorT e m) where
  finally main cleanup = do
    res <- main `catchError` (\err -> cleanup >> throwError err)
    cleanup
    return res
    
-- | Run execution in the old environment
old :: (Monad m, Functor m) => Execution m a -> Execution m a
old execution = do
  oldEnv <- get
  envMemory.memGlobals .= oldEnv^.envMemory.memOld
  envInOld .= True            
  res <- execution
  env <- get
  envMemory.memOld .= env^.envMemory.memGlobals
  envMemory.memGlobals .= (oldEnv^.envMemory.memGlobals) `M.union` (env^.envMemory.memGlobals)   -- Include freshly initialized globals into both old and new states
  envInOld .= oldEnv^.envInOld                      
  return res

-- | Save current values of global variables in memOld, return the previous memory
saveOld :: (Monad m, Functor m) => Execution m Memory 
saveOld = do
  mem <- use envMemory
  let globals = mem^.memGlobals
  envMemory.memOld .= globals
  mapM_ incRefCountValue (M.elems globals) -- Each value stored in globals is now pointed by an additional (old) variable
  return $ mem

-- | 'restoreOld' @oldMem@ : reset 'memOld' to its value from @oldMem@
restoreOld :: (Monad m, Functor m) => Memory -> Execution m ()  
restoreOld oldMem = do
  mem <- use envMemory
  let (oldOlds, newOlds) = M.partitionWithKey (\var _ -> M.member var (oldMem^.memGlobals)) (mem^.memOld)
  envMemory.memOld .= (oldMem^.memOld) `M.union` newOlds -- Add old values for freshly initialized globals (they are valid up until the program entry point, so could be accessed until the end of the program)
  mapM_ decRefCountValue (M.elems oldOlds) -- Old values for previously initialized varibles go out of scope
    
-- | Enter local scope (apply localTC to the type context and assign actuals to formals),
-- execute computation,
-- then restore type context and local variables to their initial values
executeLocally :: (MonadState (Environment m) s, Finalizer s) => (Context -> Context) -> [Id] -> [Id] -> [Value] -> AbstractStore -> s a -> s a
executeLocally localTC locals formals actuals localConstraints computation = do
  oldEnv <- get
  envTypeContext %= localTC
  envMemory.memLocals %= deleteAll locals
  envConstraints.amLocals .= localConstraints
  zipWithM_ (setVar memLocals) formals actuals -- All formals are fresh, can use emptyStore for current values
  computation `finally` unwind oldEnv
  where
    -- | Restore type context and the values of local variables 
    unwind oldEnv = do
      mapM_ (unsetVar memLocals) locals
      env <- get
      envTypeContext .= oldEnv^.envTypeContext
      envMemory.memLocals .= deleteAll locals (env^.envMemory.memLocals) `M.union` (oldEnv^.envMemory.memLocals)
      envConstraints.amLocals .= oldEnv^.envConstraints.amLocals -- Constraints cannot be initialized in a nested context, so here we can just restore old locals
                              
{- Runtime failures -}

data FailureSource = 
  SpecViolation SpecClause |          -- ^ Violation of user-defined specification
  DivisionByZero |                    -- ^ Division by zero  
  UnsupportedConstruct String |       -- ^ Language construct is not yet supported (should disappear in later versions)
  InfiniteDomain Id Interval |        -- ^ Quantification over an infinite set
  MapEquality Value Value |           -- ^ Equality of two maps cannot be determined
  InternalException InternalCode      -- ^ Must be cought inside the interpreter and never reach the user
  deriving Eq

-- | Information about a procedure or function call  
data StackFrame = StackFrame {
  callPos :: SourcePos,    -- ^ Source code position of the call
  callName :: Id           -- ^ Name of procedure or function
} deriving Eq

type StackTrace = [StackFrame]

-- | Failures that occur during execution
data RuntimeFailure = RuntimeFailure {
  rtfSource :: FailureSource,   -- ^ Source of the failure
  rtfPos :: SourcePos,          -- ^ Location where the failure occurred
  rtfMemory :: Memory,          -- ^ Memory state at the time of failure
  rtfTrace :: StackTrace        -- ^ Stack trace from the program entry point to the procedure where the failure occurred
}

-- | Throw a run-time failure
throwRuntimeFailure source pos = do
  mem <- use envMemory
  throwError (RuntimeFailure source pos mem [])

-- | Push frame on the stack trace of a runtime failure
addStackFrame frame (RuntimeFailure source pos mem trace) = throwError (RuntimeFailure source pos mem (frame : trace))

-- | Kinds of run-time failures
data FailureKind = Error | -- ^ Error state reached (assertion violation)
  Unreachable | -- ^ Unreachable state reached (assumption violation)
  Nonexecutable -- ^ The state is OK in Boogie semantics, but the execution cannot continue due to the limitations of the interpreter
  deriving Eq

-- | Kind of a run-time failure
failureKind :: RuntimeFailure -> FailureKind
failureKind err = case rtfSource err of
  SpecViolation (SpecClause _ True _) -> Unreachable
  SpecViolation (SpecClause _ False _) -> Error
  DivisionByZero -> Error
  _ -> Nonexecutable
  
instance Error RuntimeFailure where
  noMsg    = RuntimeFailure (UnsupportedConstruct "unknown") noPos emptyMemory []
  strMsg s = RuntimeFailure (UnsupportedConstruct s) noPos emptyMemory []
  
-- | Pretty-printed run-time failure
runtimeFailureDoc debug err = 
  let store = (if debug then id else userStore ((rtfMemory err)^.memHeap)) (M.filterWithKey (\k _ -> isRelevant k) (visibleVariables (rtfMemory err)))
      sDoc = storeDoc store 
  in failureSourceDoc (rtfSource err) <+> posDoc (rtfPos err) <+> 
  (if isEmpty sDoc then empty else text "with") $+$ nest 2 sDoc $+$
  vsep (map stackFrameDoc (reverse (rtfTrace err)))
  where
    failureSourceDoc (SpecViolation (SpecClause specType isFree e)) = text (clauseName specType isFree) <+> doubleQuotes (exprDoc e) <+> defPosition specType e <+> text "violated"
    failureSourceDoc (DivisionByZero) = text "Division by zero"
    failureSourceDoc (InfiniteDomain var int) = text "Variable" <+> text var <+> text "quantified over an infinite domain" <+> text (show int)
    failureSourceDoc (MapEquality m1 m2) = text "Cannot determine equality of map values" <+> valueDoc m1 <+> text "and" <+> valueDoc m2
    failureSourceDoc (UnsupportedConstruct s) = text "Unsupported construct" <+> text s
    
    clauseName Inline isFree = if isFree then "Assumption" else "Assertion"  
    clauseName Precondition isFree = if isFree then "Free precondition" else "Precondition"  
    clauseName Postcondition isFree = if isFree then "Free postcondition" else "Postcondition"  
    clauseName LoopInvariant isFree = if isFree then "Free loop invariant" else "Loop invariant"  
    clauseName Where True = "Where clause"  -- where clauses cannot be non-free  
    clauseName Axiom True = "Axiom"  -- axioms cannot be non-free  
    
    defPosition Inline _ = empty
    defPosition LoopInvariant _ = empty
    defPosition _ e = text "defined" <+> posDoc (position e)
    
    isRelevant k = case rtfSource err of
      SpecViolation (SpecClause _ _ expr) -> k `elem` freeVars expr
      _ -> False
    
    stackFrameDoc f = text "in call to" <+> text (callName f) <+> posDoc (callPos f)
    posDoc pos
      | pos == noPos = text "from the environment"
      | otherwise = text "at" <+> text (sourceName pos) <+> text "line" <+> int (sourceLine pos)

instance Show RuntimeFailure where
  show err = show (runtimeFailureDoc True err)
  
-- | Do two runtime failures represent the same fault?
-- Yes if the same property failed at the same program location
-- or, for preconditions, for the same caller   
sameFault f f' = rtfSource f == rtfSource f' && 
  case rtfSource f of
    SpecViolation (SpecClause Precondition False _) -> last (rtfTrace f) == last (rtfTrace f')
    _ -> rtfPos f == rtfPos f'    
  
instance Eq RuntimeFailure where
  f == f' = sameFault f f'
    
-- | Internal error codes 
data InternalCode = NotLinear | UnderConstruction Int
  deriving Eq

throwInternalException code = throwRuntimeFailure (InternalException code) noPos

{- Execution results -}
    
-- | Description of an execution
data TestCase = TestCase {
  tcProcedure :: PSig,              -- ^ Root procedure (entry point) of the execution
  tcMemory :: Memory,               -- ^ Final memory state (at the exit from the root procedure) 
  tcFailure :: Maybe RuntimeFailure -- ^ Failure the execution eded with, or Nothing if the execution ended in a valid state
}

-- | 'isPass' @tc@: Does @tc@ end in a valid state?
isPass :: TestCase -> Bool
isPass (TestCase _ _ Nothing) =  True
isPass _ =          False

-- | 'isInvalid' @tc@: Does @tc@ and in an unreachable state?
isInvalid :: TestCase -> Bool 
isInvalid (TestCase _ _ (Just err))
  | failureKind err == Unreachable = True
isInvalid _                        = False

-- | 'isNonexecutable' @tc@: Does @tc@ end in a non-executable state?
isNonexecutable :: TestCase -> Bool 
isNonexecutable (TestCase _ _ (Just err))
  | failureKind err == Nonexecutable  = True
isNonexecutable _                     = False

-- | 'isFail' @tc@: Does @tc@ end in an error state?
isFail :: TestCase -> Bool
isFail tc = not (isPass tc || isInvalid tc || isNonexecutable tc)

-- | 'testCaseSummary' @debug tc@ : Summary of @tc@'s inputs and outcome,
-- displayed in user or debug format depending on 'debug'
testCaseSummary :: Bool -> TestCase -> Doc
testCaseSummary debug tc@(TestCase sig mem mErr) = text (psigName sig) <> 
  parens (commaSep (map (inDoc . itwId) (psigArgs sig))) <>
  (if M.null globalInputsRepr then empty else parens (commaSep (map globDoc (M.toList globalInputsRepr)))) <+>
  outcomeDoc tc
  where
    storeRepr store = if debug then store else userStore (mem^.memHeap) store
    removeEmptyMaps store = M.filter (\val -> val /= MapValue emptyMap) store
    localsRepr = storeRepr $ mem^.memLocals
    globalInputsRepr = removeEmptyMaps . storeRepr $ (mem^.memOld) `M.union` (mem^.memConstants)
    inDoc name = valueDoc $ localsRepr ! name    
    globDoc (name, val) = text name <+> text "=" <+> valueDoc val
    outcomeDoc tc 
      | isPass tc = text "passed"
      | isInvalid tc = text "invalid"
      | isNonexecutable tc = text "non-executable"
      | otherwise = text "failed"
      
-- | 'finalStateDoc' @debug tc@ : outputs of @tc@, 
-- displayed in user or debug format depending on 'debug' 
finalStateDoc :: Bool -> TestCase -> Doc
finalStateDoc debug tc@(TestCase sig mem mErr) = vsep $
    (if M.null outsRepr then [] else [text "Outs:" <+> storeDoc outsRepr]) ++
    (if M.null globalsRepr then [] else [text "Globals:" <+> storeDoc globalsRepr]) ++ 
    (if debug then [text "Heap:" <+> heapDoc (mem^.memHeap)] else [])
  where
    storeRepr store = if debug then store else userStore (mem^.memHeap) store
    outNames = map itwId (psigRets sig)
    outsRepr = storeRepr $ M.filterWithKey (\k _ -> k `elem` outNames) (mem^.memLocals)
    globalsRepr = storeRepr $ mem^.memGlobals
    
-- | Test cases are considered equivalent from a user perspective
-- | if they are testing the same procedure and result in the same outcome
equivalent tc1 tc2 = tcProcedure tc1 == tcProcedure tc2 && tcFailure tc1 == tcFailure tc2      

-- | Test session summary
data Summary = Summary {
  sPassCount :: Int,            -- ^ Number of passing test cases
  sFailCount :: Int,            -- ^ Number of failing test cases
  sInvalidCount :: Int,         -- ^ Number of invalid test cases
  sNonExecutableCount :: Int,   -- ^ Number of nonexecutable test cases
  sUniqueFailures :: [TestCase] -- ^ Unique failing test cases
}

totalCount s = sPassCount s + sFailCount s + sInvalidCount s + sNonExecutableCount s

-- | Pretty-printed test session summary
summaryDoc :: Summary -> Doc
summaryDoc summary = 
  text "Test cases:" <+> int (totalCount summary) $+$
  text "Passed:" <+> int (sPassCount summary) $+$
  text "Invalid:" <+> int (sInvalidCount summary) $+$
  text "Non executable:" <+> int (sNonExecutableCount summary) $+$
  text "Failed:" <+> int (sFailCount summary) <+> parens (int (length (sUniqueFailures summary)) <+> text "unique") <>
  (if null (sUniqueFailures summary) then empty else newline)
  
instance Show Summary where show s = show (summaryDoc s)

-- | Summary of a set of test cases   
testSessionSummary :: [TestCase] -> Summary
testSessionSummary tcs = let 
  passing = filter isPass tcs
  failing = filter isFail tcs
  invalid = filter isInvalid tcs
  nexec = filter isNonexecutable tcs
  in Summary {
    sPassCount = length passing,
    sFailCount = length failing,
    sInvalidCount = length invalid,  
    sNonExecutableCount = length nexec,
    sUniqueFailures = nubBy equivalent failing
  }    

{- Basic executions -}      

-- | 'generate' @f@ : computation that extracts @f@ from the generator
generate :: (Monad m, Functor m) => (Generator m -> m a) -> Execution m a
generate f = do    
  gen <- use envGenerator
  lift (lift (f gen))
      
-- | 'generateValue' @t pos@ : choose a value of type @t@ at source position @pos@;
-- fail if @t@ is a type variable
generateValue :: (Monad m, Functor m) => Type -> SourcePos -> Execution m Value
generateValue t pos = case t of
  IdType x [] | isTypeVar [] x -> throwRuntimeFailure (UnsupportedConstruct ("choice of a value from unknown type " ++ show t)) pos
  -- Maps are initializaed lazily, allocate an empty map on the heap:
  MapType _ _ _ -> allocate $ MapValue emptyMap
  BoolType -> BoolValue <$> generate genBool
  IntType -> IntValue <$> generate genInteger
  IdType id _ -> do
    n <- gets $ lookupCustomCount id
    i <- generate (`genIndex` (n + 1))
    when (i == n) $ modify (setCustomCount id (n + 1))
    return $ CustomValue id i
  
-- | 'generateValueLike' @v@ : choose a value of the same type as @v@
generateValueLike :: (Monad m, Functor m) => Value -> Execution m Value
generateValueLike (BoolValue _) = generateValue BoolType noPos
generateValueLike (IntValue _) = generateValue IntType noPos
generateValueLike (CustomValue t _) = generateValue (IdType t []) noPos
generateValueLike (Reference _) = allocate $ MapValue emptyMap
generateValueLike (MapValue _) = internalError "Attempt to generateValueLike a map value directly"
        
-- | 'incRefCountValue' @val@ : if @val@ is a reference, increase its count
incRefCountValue val = case val of
  Reference r -> envMemory.memHeap %= incRefCount r
  _ -> return ()    

-- | 'decRefCountValue' @val@ : if @val@ is a reference, decrease its count  
decRefCountValue val = case val of
  Reference r -> envMemory.memHeap %= decRefCount r
  _ -> return ()     
    
-- | 'unsetVar' @getter name@ : if @name@ was associated with a reference in @getter@, decrease its reference count
unsetVar getter name = do
  store <- use $ envMemory.getter
  case M.lookup name store of    
    Just (Reference r) -> do          
      envMemory.memHeap %= decRefCount r
    _ -> return ()

-- | 'setVar' @setter name val@ : set value of variable @name@ to @val@ using @setter@
setVar setter name val = do
  incRefCountValue val
  envMemory.setter %= M.insert name val

-- | 'resetVar' @lens name val@ : set value of variable @name@ to @val@ using @lens@;
-- if @name@ was associated with a reference, decrease its reference count
resetVar :: (Monad m, Functor m) => StoreLens -> Id -> Value -> Execution m ()  
resetVar lens name val = do
  unsetVar lens name
  setVar lens name val
            
-- | 'resetAnyVar' @name val@ : set value of a constant, global or local variable @name@ to @val@
resetAnyVar name val = do
  tc <- use envTypeContext
  if M.member name (localScope tc)
    then resetVar memLocals name val
    else if M.member name (ctxGlobals tc)
      then resetVar memGlobals name val
      else resetVar memConstants name val
      
-- | 'forgetVar' @lens name@ : forget value of variable @name@ in @lens@;
-- if @name@ was associated with a reference, decrease its reference count      
forgetVar :: (Monad m, Functor m) => StoreLens -> Id -> Execution m ()
forgetVar lens name = do
  unsetVar lens name
  envMemory.lens %= M.delete name
      
-- | 'forgetAnyVar' @name@ : forget value of a constant, global or local variable @name@ to @val@      
forgetAnyVar name = do
  tc <- use envTypeContext
  if M.member name (localScope tc)
    then forgetVar memLocals name
    else if M.member name (ctxGlobals tc)
      then forgetVar memGlobals name
      else forgetVar memConstants name
      
-- | 'setMapValue' @r index val@ : map @index@ to @val@ in the map referenced by @r@
-- (@r@ has to be a source map)
setMapValue r index val = do
  MapValue (Source baseVals) <- readHeap r
  envMemory.memHeap %= update r (MapValue (Source (M.insert index val baseVals)))
  incRefCountValue val
  
-- | 'forgetMapValue' @r index@ : forget value at @index@ in the map referenced by @r@  
-- (@r@ has to be a source map)
forgetMapValue r index = do
  MapValue (Source baseVals) <- readHeap r
  case M.lookup index baseVals of
    Nothing -> return ()
    Just val -> do
      decRefCountValue val
      envMemory.memHeap %= update r (MapValue (Source (M.delete index baseVals)))
        
-- | 'readHeap' @r@: current value of reference @r@ in the heap
readHeap r = flip at r <$> use (envMemory.memHeap)
    
-- | 'allocate' @v@: store @v@ at a fresh location in the heap and return that location
allocate :: (Monad m, Functor m) => Value -> Execution m Value
allocate v = Reference <$> (state . withHeap . alloc) v
  
-- | Remove all unused references from the heap  
collectGarbage :: (Monad m, Functor m) => Execution m ()  
collectGarbage = do
  h <- use (envMemory.memHeap)
  when (hasGarbage h) (do
    r <- state $ withHeap dealloc
    let MapValue repr = h `at` r
    case repr of
      Source _ -> return ()
      Derived base _ -> envMemory.memHeap %= decRefCount base
    mapM_ decRefCountValue (M.elems $ stored repr)
    envConstraints.amHeap %= M.delete r
    collectGarbage)

{- Expressions -}

-- | Semantics of unary operators
unOp :: UnOp -> Value -> Value
unOp Neg (IntValue n)   = IntValue (-n)
unOp Not (BoolValue b)  = BoolValue (not b)

-- | Semi-strict semantics of binary operators:
-- 'binOpLazy' @op lhs@ : returns the value of @lhs op@ if already defined, otherwise Nothing 
binOpLazy :: BinOp -> Value -> Maybe Value
binOpLazy And     (BoolValue False) = Just $ BoolValue False
binOpLazy Or      (BoolValue True)  = Just $ BoolValue True
binOpLazy Implies (BoolValue False) = Just $ BoolValue True
binOpLazy Explies (BoolValue True)  = Just $ BoolValue True
binOpLazy _ _                       = Nothing

-- | Strict semantics of binary operators
binOp :: (Monad m, Functor m) => SourcePos -> BinOp -> Value -> Value -> Execution m Value 
binOp pos Plus    (IntValue n1) (IntValue n2)   = return $ IntValue (n1 + n2)
binOp pos Minus   (IntValue n1) (IntValue n2)   = return $ IntValue (n1 - n2)
binOp pos Times   (IntValue n1) (IntValue n2)   = return $ IntValue (n1 * n2)
binOp pos Div     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                then throwRuntimeFailure DivisionByZero pos
                                                else return $ IntValue (fst (n1 `euclidean` n2))
binOp pos Mod     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                then throwRuntimeFailure DivisionByZero pos
                                                else return $ IntValue (snd (n1 `euclidean` n2))
binOp pos Leq     (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 <= n2)
binOp pos Ls      (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 < n2)
binOp pos Geq     (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 >= n2)
binOp pos Gt      (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 > n2)
binOp pos And     (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 && b2)
binOp pos Or      (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 || b2)
binOp pos Implies (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 <= b2)
binOp pos Explies (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 >= b2)
binOp pos Equiv   (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 == b2)
binOp pos Eq      v1 v2                         = evalEquality v1 v2
binOp pos Neq     v1 v2                         = vnot <$> evalEquality v1 v2
binOp pos Lc      v1 v2                         = throwRuntimeFailure (UnsupportedConstruct "orders") pos

-- | Euclidean division used by Boogie for integer division and modulo
euclidean :: Integer -> Integer -> (Integer, Integer)
a `euclidean` b =
  case a `quotRem` b of
    (q, r) | r >= 0    -> (q, r)
           | b >  0    -> (q - 1, r + b)
           | otherwise -> (q + 1, r - b)
         
-- | Evaluate an expression;
-- can have a side-effect of initializing variables that were not previously defined
eval :: (Monad m, Functor m) => Expression -> Execution m Value
eval expr = case node expr of
  TT -> return $ BoolValue True
  FF -> return $ BoolValue False
  Numeral n -> return $ IntValue n
  Var name -> evalVar name (position expr)
  Application name args -> evalMapSelection (functionExpr name) args (position expr)
  MapSelection m args -> evalMapSelection m args (position expr)
  MapUpdate m args new -> evalMapUpdate m args new (position expr)
  Old e -> old $ eval e
  IfExpr cond e1 e2 -> evalIf cond e1 e2
  Coercion e t -> eval e
  UnaryExpression op e -> unOp op <$> eval e
  BinaryExpression op e1 e2 -> evalBinary op e1 e2
  Quantified Lambda _ _ _ -> throwRuntimeFailure (UnsupportedConstruct "lambda expressions") (position expr)
  Quantified Forall tv vars e -> vnot <$> evalExists tv vars (enot e) (position expr)
  Quantified Exists tv vars e -> evalExists tv vars e (position expr)
  where
    functionExpr name = gen . Var $ functionConst name
  
evalVar :: (Monad m, Functor m) => Id -> SourcePos -> Execution m Value  
evalVar name pos = do
  tc <- use envTypeContext
  case M.lookup name (localScope tc) of
    Just t -> evalVarWith t memLocals False
    Nothing -> case M.lookup name (ctxGlobals tc) of
      Just t -> do
        inOld <- use envInOld
        evalVarWith t memGlobals (not inOld) -- Unless we are evaluating and old expression, also initialize the old value of the global
      Nothing -> case M.lookup name (ctxConstants tc) of
        Just t -> evalVarWith t memConstants False
        Nothing -> (internalError . show) (text "Encountered unknown identifier during execution:" <+> text name) 
  where  
    evalVarWith :: (Monad m, Functor m) => Type -> StoreLens -> Bool -> Execution m Value
    evalVarWith t lens initOld = do
      s <- use $ envMemory.lens
      case M.lookup name s of         -- Lookup a cached value
        Just val -> wellDefined val
        Nothing -> do                 -- If not found, look for an applicable definition
          definedValue <- checkNameDefinitions name t pos
          case definedValue of
            Just val -> do
              setVar lens name val
              checkNameConstraints name pos
              forgetVar lens name
              return val
            Nothing -> do             -- If not found, choose a value non-deterministically
              chosenValue <- generateValue t pos
              setVar lens name chosenValue
              when initOld $ setVar memOld name chosenValue
              checkNameConstraints name pos
              return chosenValue
        
rejectMapIndex pos idx = case idx of
  Reference r -> throwRuntimeFailure (UnsupportedConstruct "map as an index") pos
  _ -> return ()
      
evalMapSelection m args pos = do   
  argsV <- mapM eval args  
  Reference r <- eval m  
  h <- use $ envMemory.memHeap
  let (s, vals) = flattenMap h r
  case M.lookup argsV vals of    -- Lookup a cached value
    Just val -> wellDefined val
    Nothing -> do                           -- If not found, look for an applicable definition
      tc <- use envTypeContext
      let mapType = exprType tc m    
      definedValue <- checkMapDefinitions s mapType args argsV pos
      case definedValue of
        Just val -> do
          setMapValue s argsV val
          checkMapConstraints s mapType args argsV pos
          forgetMapValue s argsV
          return val
        Nothing -> do                       -- If not found, choose a value non-deterministically
          mapM_ (rejectMapIndex pos) argsV
          let rangeType = exprType tc (gen $ MapSelection m args)
          chosenValue <- generateValue rangeType pos
          setMapValue s argsV chosenValue
          checkMapConstraints s mapType args argsV pos
          return chosenValue  
        
evalMapUpdate m args new pos = do
  Reference r <- eval m
  argsV <- mapM eval args
  mapM_ (rejectMapIndex pos) argsV
  newV <- eval new
  MapValue repr <- readHeap r
  let 
    (newSource, newRepr) = case repr of 
      Source _ -> (r, Derived r (M.singleton argsV newV))
      Derived base override -> (base, Derived base (M.insert argsV newV override))
  mapM_ incRefCountValue (M.elems $ stored newRepr)
  envMemory.memHeap %= incRefCount newSource
  allocate $ MapValue newRepr
  
evalIf cond e1 e2 = do
  v <- eval cond
  case v of
    BoolValue True -> eval e1    
    BoolValue False -> eval e2    
      
evalBinary op e1 e2 = do
  left <- eval e1
  case binOpLazy op left of
    Just result -> return result
    Nothing -> do
      right <- eval e2
      binOp (position e1) op left right

-- | Finite domain      
type Domain = [Value]      

evalExists :: (Monad m, Functor m) => [Id] -> [IdType] -> Expression -> SourcePos -> Execution m Value      
evalExists tv vars e pos = let Quantified Exists tv' vars' e' = node $ normalize (attachPos pos $ Quantified Exists tv vars e)
  in evalExists' tv' vars' e'

evalExists' :: (Monad m, Functor m) => [Id] -> [IdType] -> Expression -> Execution m Value    
evalExists' tv vars e = do
  localConstraints <- use $ envConstraints.amLocals
  BoolValue <$> executeLocally (enterQuantified tv vars) (map fst vars) [] [] localConstraints evalWithDomains
  where
    evalWithDomains = do
      doms <- domains e varNames
      evalForEach varNames doms
    -- | evalForEach vars domains: evaluate e for each combination of possible values of vars, drown from respective domains
    evalForEach :: (Monad m, Functor m) => [Id] -> [Domain] -> Execution m Bool
    evalForEach [] [] = unValueBool <$> eval e
    evalForEach (var : vars) (dom : doms) = anyM (fixOne vars doms var) dom
    -- | Fix the value of var to val, then evaluate e for each combination of values for the rest of vars
    fixOne :: (Monad m, Functor m) => [Id] -> [Domain] -> Id -> Value -> Execution m Bool
    fixOne vars doms var val = do
      resetVar memLocals var val
      evalForEach vars doms
    varNames = map fst vars
      
{- Statements -}

-- | Execute a basic statement
-- (no jump, if or while statements allowed)
exec :: (Monad m, Functor m) => Statement -> Execution m ()
exec stmt = case node stmt of
    Predicate specClause -> execPredicate specClause (position stmt)
    Havoc ids -> execHavoc ids (position stmt)
    Assign lhss rhss -> execAssign lhss rhss
    Call lhss name args -> execCall name lhss args (position stmt)
    CallForall name args -> return ()
  >> collectGarbage
  
execPredicate specClause pos = do
  b <- eval $ specExpr specClause
  case b of 
    BoolValue True -> return ()
    BoolValue False -> throwRuntimeFailure (SpecViolation specClause) pos      
    
execHavoc names pos = do
  mapM_ havoc names 
  where
    havoc name = do
      tc <- use envTypeContext
      let t = exprType tc . gen . Var $ name
      definedValue <- checkNameDefinitions name t pos
      case definedValue of
        Just val -> do
          resetAnyVar name val
          checkNameConstraints name pos
        Nothing -> do
          chosenValue <- generateValue t pos
          resetAnyVar name chosenValue
          checkNameConstraints name pos
    
execAssign lhss rhss = do
  rVals <- mapM eval rhss'
  zipWithM_ resetAnyVar lhss' rVals
  where
    lhss' = map fst (zipWith simplifyLeft lhss rhss)
    rhss' = map snd (zipWith simplifyLeft lhss rhss)
    simplifyLeft (id, []) rhs = (id, rhs)
    simplifyLeft (id, argss) rhs = (id, mapUpdate (gen $ Var id) argss rhs)
    mapUpdate e [args] rhs = gen $ MapUpdate e args rhs
    mapUpdate e (args1 : argss) rhs = gen $ MapUpdate e args1 (mapUpdate (gen $ MapSelection e args1) argss rhs)
    
execCall name lhss args pos = do
  sig <- procSig name <$> use envTypeContext
  execCallBySig sig lhss args pos
    
execCallBySig sig lhss args pos = do
  defs <- gets $ lookupProcedure (psigName sig)
  tc <- use envTypeContext
  (sig', def) <- selectDef tc defs
  let lhssExpr = map (attachPos (ctxPos tc) . Var) lhss
  retsV <- execProcedure sig' def args lhssExpr `catchError` addFrame
  zipWithM_ resetAnyVar lhss retsV
  where
    selectDef tc [] = return (assumePostconditions sig, dummyDef tc)
    selectDef tc defs = do
      i <- generate (`genIndex` length defs)
      return (sig, defs !! i)
    params = psigParams sig
    paramConstraints tc = M.filterWithKey (\k _ -> k `elem` map itwId params) $ foldr asUnion M.empty $ map (extractConstraints tc . itwWhere) params
    -- For procedures with no implementation: dummy definition that just havocs all modifiable globals
    dummyDef tc = PDef {
        pdefIns = map itwId (psigArgs sig),
        pdefOuts = map itwId (psigRets sig),
        pdefParamsRenamed = False,
        pdefBody = ([], (M.fromList . toBasicBlocks . singletonBlock . gen . Havoc . psigModifies) sig),
        pdefConstraints = paramConstraints tc,
        pdefPos = noPos
      }
    addFrame err = addStackFrame (StackFrame pos (psigName sig)) err
        
-- | Execute program consisting of blocks starting from the block labeled label.
-- Return the location of the exit point.
execBlock :: (Monad m, Functor m) => Map Id [Statement] -> Id -> Execution m SourcePos
execBlock blocks label = let
  block = blocks ! label
  statements = init block
  in do
    mapM exec statements
    case last block of
      Pos pos Return -> return pos
      Pos _ (Goto lbs) -> tryOneOf blocks lbs
  
-- | tryOneOf blocks labels: try executing blocks starting with each of labels,
-- until we find one that does not result in an assumption violation      
tryOneOf :: (Monad m, Functor m) => Map Id [Statement] -> [Id] -> Execution m SourcePos        
tryOneOf blocks (l : lbs) = execBlock blocks l `catchError` retry
  where
    retry err 
      | failureKind err == Unreachable && not (null lbs) = tryOneOf blocks lbs
      | otherwise = throwError err
  
-- | 'execProcedure' @sig def args lhss@ :
-- Execute definition @def@ of procedure @sig@ with actual arguments @args@ and call left-hand sides @lhss@
execProcedure :: (Monad m, Functor m) => PSig -> PDef -> [Expression] -> [Expression] -> Execution m [Value]
execProcedure sig def args lhss = let 
  ins = pdefIns def
  outs = pdefOuts def
  blocks = snd (pdefBody def)
  localConstraints = pdefConstraints def
  exitPoint pos = if pos == noPos 
    then pdefPos def  -- Fall off the procedure body: take the procedure definition location
    else pos          -- A return statement inside the body
  execBody = do
    checkPreconditions sig def    
    pos <- exitPoint <$> execBlock blocks startLabel
    checkPostonditions sig def pos    
    mapM (eval . attachPos (pdefPos def) . Var) outs
  in do
    argsV <- mapM eval args
    mem <- saveOld
    executeLocally (enterProcedure sig def args lhss) (pdefLocals def) ins argsV localConstraints execBody `finally` restoreOld mem
    
{- Specs -}

-- | Assert preconditions of definition def of procedure sig
checkPreconditions sig def = mapM_ (exec . attachPos (pdefPos def) . Predicate . subst sig) (psigRequires sig)
  where 
    subst sig (SpecClause t f e) = SpecClause t f (paramSubst sig def e)

-- | Assert postconditions of definition def of procedure sig at exitPoint    
checkPostonditions sig def exitPoint = mapM_ (exec . attachPos exitPoint . Predicate . subst sig) (psigEnsures sig)
  where 
    subst sig (SpecClause t f e) = SpecClause t f (paramSubst sig def e)
        
-- | 'wellDefined' @val@ : throw an exception if @val@ is under construction
wellDefined (CustomValue t n) | t == ucTypeName = throwInternalException $ UnderConstruction n
wellDefined val = return val
  
-- | 'checkDefinitions' @typeGuard evalLocally myCode defs pos@ : return the result of the first applicable definition from @defs@;
-- if none are applicable return 'Nothing', 
-- unless an under construction value different from @myCode@ has been evaluated, in which case rethrow the UnderConstruction exception;
-- use @typeGuard tv formalTypes@ to decide if a definition with type variables @tv@ and types of formals @formalTypes@ is applicable to the current invocation; 
-- use @evalLocally formals@ to evaluate expressions inside a definition with arguments @formals@;
-- @pos@ is the position of the definition invocation
checkDefinitions :: (Monad m, Functor m) => ([Id] -> [Type] -> Bool) -> ([Id] -> Expression -> Execution m Value) -> Int -> [FDef] -> SourcePos -> Execution m (Maybe Value)
checkDefinitions typeGuard evalLocally myCode defs pos = checkDefinitions' typeGuard evalLocally myCode Nothing defs pos 

checkDefinitions' _ _ _ Nothing [] _ = return Nothing
checkDefinitions' _ _ _ (Just code) [] _ = throwInternalException (UnderConstruction code)
checkDefinitions' typeGuard evalLocally myCode mCode (FDef name tv formals guard body : defs) pos = tryDefinitions `catchError` ucHandler
  where
    tryDefinitions = do      
      mVal <- applyDefinition (evalLocally (map fst formals)) guard body
      case mVal of
        Just val -> return mVal
        Nothing -> checkDefinitions' typeGuard evalLocally myCode mCode defs pos 
    ucHandler err = case rtfSource err of
      InternalException (UnderConstruction code) -> if code == myCode
        then checkDefinitions' typeGuard evalLocally myCode mCode defs pos
        else checkDefinitions' typeGuard evalLocally myCode (Just code) defs pos
      _ -> throwError err
    applyDefinition evaluation guard body = if typeGuard tv (map snd formals)
      then do
        applicable <- case guard of
          Pos _ TT -> return $ BoolValue True -- optimization for trivial guards
          _ -> evaluation guard `catchError` addFrame
        case applicable of
          BoolValue False -> return Nothing
          BoolValue True -> (Just <$> evaluation body) `catchError` addFrame
      else return Nothing
    addFrame = addStackFrame (StackFrame pos name)
    
-- | 'checkNameDefinitions' @name t pos@ : return a value for @name@ of type @t@ mentioned at @pos@, if there is an applicable definition
checkNameDefinitions :: (Monad m, Functor m) => Id -> Type -> SourcePos -> Execution m (Maybe Value)    
checkNameDefinitions name t pos = do
  n <- gets $ lookupCustomCount ucTypeName
  resetAnyVar name $ CustomValue ucTypeName n  
  modify $ setCustomCount ucTypeName (n + 1)
  defs <- fst <$> gets (lookupNameConstraints name)
  let simpleDefs = [simpleDef | simpleDef <- defs, null $ fdefArgs simpleDef] -- Ignore forall-definition, they will be attached to the map value by checkNameConstraints
  checkDefinitions (\_ _ -> True) (\_ -> eval) n simpleDefs pos `finally` cleanup n
  where  
    cleanup n = do
      forgetAnyVar name
      modify $ setCustomCount ucTypeName n
        
-- | 'checkMapDefinitions' @r t args actuals pos@ : return a value at index @actuals@ 
-- in the map of type @t@ referenced by @r@ mentioned at @pos@, if there is an applicable definition 
checkMapDefinitions :: (Monad m, Functor m) => Ref -> Type -> [Expression] -> [Value] -> SourcePos -> Execution m (Maybe Value)    
checkMapDefinitions r t args actuals pos = do
  n <- gets $ lookupCustomCount ucTypeName
  setMapValue r actuals $ CustomValue ucTypeName n  
  modify $ setCustomCount ucTypeName (n + 1)  
  defs <- fst <$> gets (lookupMapConstraints r)
  tc <- use envTypeContext
  let argTypes = map (exprType tc) args
  checkDefinitions (typeGuard argTypes) evalLocally n defs pos `finally` cleanup n
  where  
    sig = fsigFromType t
    typeGuard argTypes tv formalTypes = isJust $ unifier tv formalTypes argTypes
    evalLocally formals expr = if null formals
        then eval expr
        else executeLocally (enterFunction sig formals args) formals formals actuals M.empty (eval expr)
    cleanup n = do
      forgetMapValue r actuals
      modify $ setCustomCount ucTypeName n      

-- | 'applyConstraint' @name evaluation guard body pos@ : 
-- check for an entity @name@ that @guard@ ==> @body@, using @evaluation@ to evaluate both @guard@ and @body@;
-- (@pos@ is the position of the constraint invocation)      
applyConstraint name evaluation guard body pos = do
  applicable <- case guard of
    Pos _ TT -> return $ BoolValue True -- optimization for trivial guards
    _ -> evaluation guard `catchError` addFrame
  case applicable of
    BoolValue True -> do
      satisfied <- evaluation body `catchError` addFrame
      case satisfied of 
        BoolValue True -> return ()
        BoolValue False -> throwRuntimeFailure (SpecViolation $ SpecClause Axiom True body) pos
    BoolValue False -> return ()
  where
    addFrame = addStackFrame (StackFrame pos name)
    
-- | 'checkNameConstraints' @name pos@: assume all constraints of entity @name@ mentioned at @pos@;
-- is @name@ is of map type, attach all its forall-definitions and forall-contraints to the corresponding reference 
checkNameConstraints name pos = do
  (defs, constraints) <- gets $ lookupNameConstraints name
  mapM_ checkConstraint constraints
  mapM_ attachDefinition defs
  where
    checkConstraint (FDef _ [] [] guard body) = applyConstraint name eval guard body pos -- Simple constraint: assume it
    checkConstraint constr = do             -- Forall-constraint: attach to the map value
      Reference r <- evalVar name pos
      modify $ addMapConstraint r constr
    attachDefinition (FDef _ [] [] _ _) = return ()  -- Simple definition: ignore
    attachDefinition def = do                     -- Forall definition: attach to the map value
      Reference r <- evalVar name pos
      modify $ addMapDefinition r def
      
-- | 'checkMapConstraints' @r t args actuals pos@ : assume all constraints for the value at index @actuals@ 
-- in the map of type @t@ referenced by @r@ mentioned at @pos@
checkMapConstraints r t args actuals pos = do
  constraints <- snd <$> gets (lookupMapConstraints r)
  tc <- use envTypeContext
  let argTypes = map (exprType tc) args
  let typeGuard tv formalTypes = isJust $ unifier tv formalTypes argTypes
  mapM_ (checkConstraint typeGuard) constraints        
  where
    checkConstraint typeGuard (FDef name tv formals guard body) = if typeGuard tv (map snd formals)
      then applyConstraint name (evalLocally (map fst formals)) guard body pos
      else return ()
    evalLocally formalNames expr = do
      let sig = fsigFromType t
      executeLocally (enterFunction sig formalNames args) formalNames formalNames actuals M.empty (eval expr)

{- Preprocessing -}

-- | Collect procedure implementations, and constant/function/global variable constraints
preprocess :: (Monad m, Functor m) => Program -> SafeExecution m ()
preprocess (Program decls) = mapM_ processDecl decls
  where
    processDecl decl = case node decl of
      FunctionDecl name _ args _ mBody -> processFunction name args mBody
      ProcedureDecl name _ args rets _ (Just body) -> processProcedureBody name (position decl) (map noWhere args) (map noWhere rets) body
      ImplementationDecl name _ args rets bodies -> mapM_ (processProcedureBody name (position decl) args rets) bodies
      AxiomDecl expr -> processAxiom expr
      VarDecl vars -> mapM_ processAxiom (map itwWhere vars)
      _ -> return ()
  
processFunction name args mBody = do
  sig <- funSig name <$> use envTypeContext
  envTypeContext %= \tc -> tc { ctxConstants = M.insert (functionConst name) (fsigType sig) (ctxConstants tc) }  
  case mBody of
    Nothing -> return ()
    Just body -> modify $ addGlobalDefinition (functionConst name) (FDef name (fsigTypeVars sig) formals (conjunction []) body)
  where    
    formals = over (mapped._1) formalName args
    formalName Nothing = dummyFArg 
    formalName (Just n) = n    
    
processProcedureBody name pos args rets body = do
  tc <- use envTypeContext
  let params = psigParams $ procSig name tc
  let paramsRenamed = map itwId params /= (argNames ++ retNames)    
  let flatBody = (map (mapItwType (resolve tc)) (concat $ fst body), M.fromList (toBasicBlocks $ snd body))
  let allLocals = params ++ fst flatBody
  let localConstraints = M.filterWithKey (\k _ -> k `elem` map itwId allLocals) $ foldr asUnion M.empty $ map (extractConstraints tc . itwWhere) allLocals
  modify $ addProcedureImpl name (PDef argNames retNames paramsRenamed flatBody localConstraints pos) 
  where
    argNames = map fst args
    retNames = map fst rets

processAxiom expr = do
  tc <- use envTypeContext
  envConstraints.amGlobals %= (`asUnion` extractConstraints tc expr)
  
{- Constant and function constraints -}

-- | 'extractConstraints' @bExpr@ : extract definitions and constraints from @bExpr@
extractConstraints :: Context -> Expression -> AbstractStore
extractConstraints tc bExpr = extractConstraints' tc [] (negationNF bExpr)

extractConstraints' :: Context -> [Expression] -> Expression -> AbstractStore
extractConstraints' tc guards bExpr = case (node bExpr) of
  Quantified Forall tv vars bExpr' -> extractConstraints' (enterQuantified tv vars tc) guards bExpr'
  Quantified Exists _ _ _ -> M.empty
  BinaryExpression And bExpr1 bExpr2 -> let
    constraints1 = extractConstraints' tc guards bExpr1
    constraints2 = extractConstraints' tc guards bExpr2
    in constraints1 `asUnion` constraints2
  BinaryExpression Or bExpr1 bExpr2 -> let
    constraints1 = extractConstraints' tc ((negationNF $ enot bExpr1) : guards) bExpr2
    constraints2 = extractConstraints' tc ((negationNF $ enot bExpr2) : guards) bExpr1
    in constraints1 `asUnion` constraints2
  BinaryExpression Eq expr1 expr2 -> let
    defs1 = extractDefsAtomic expr1 expr2
    defs2 = extractDefsAtomic expr2 expr1
    constraints = extractConstraintsAtomic
    in foldr1 asUnion [defs1, defs2, constraints]
  _ -> extractConstraintsAtomic
  where
    fvExpr = freeVars bExpr
    fvGuards = concatMap freeVars guards
    allFV = fvExpr ++ fvGuards
    tv = ctxTypeVars tc
    vars = M.toList $ ctxIns tc
    usedVars = [(v, t) | (v, t) <- vars, v `elem` allFV]
  
    extractDefsAtomic lhs rhs = case node lhs of
      Var name -> addDefFor name [] rhs
      MapSelection (Pos _ (Var name)) args -> addDefFor name args rhs
      Application name args -> addDefFor (functionConst name) args rhs
      _ -> M.empty
    addDefFor name args rhs = let
        argTypes = map (exprType tc) args
        (formals, argGuards) = unzip $ extractArgs (map fst usedVars) args
        allGuards = concat argGuards ++ guards
        extraVars = [(v, t) | (v, t) <- usedVars, v `notElem` formals]
      in if length formals == length args && null extraVars -- Only possible if all arguments are simple and there are no extra variables
        then M.singleton name ([FDef name tv (zip formals argTypes) (conjunction allGuards) rhs], [])
        else M.empty
    
    extractConstraintsAtomic = case usedVars of -- This is a compromise: quantified expressions constrain names they mention of any arity but zero (ToDo: think about it)
      [] -> foldr asUnion M.empty $ map addSimpleConstraintFor fvExpr
      _ -> foldr asUnion M.empty $ map addForallConstraintFor (freeSelections bExpr ++ over (mapped._1) functionConst (applications bExpr))
    addSimpleConstraintFor name = M.singleton name ([], [FDef name [] [] (conjunction guards) bExpr])
    addForallConstraintFor (name, args) = let
        argTypes = map (exprType tc) args
        (formals, argGuards) = unzip $ extractArgs (map fst usedVars) args
        allArgGuards = concat argGuards
        extraVars = [(v, t) | (v, t) <- usedVars, v `notElem` formals]
        constraint = if null extraVars
          then conjunction guards |=>| bExpr
          else attachPos (position bExpr) $ Quantified Forall tv extraVars (conjunction guards |=>| bExpr) -- outer guards are inserted into the body, because they might contain extraVars
      in if length formals == length args -- Only possible if all arguments are simple
        then M.singleton name ([], [FDef name tv (zip formals argTypes) (conjunction allArgGuards) constraint])
        else M.empty
            
-- | 'extractArgs' @vars args@: extract simple arguments from @args@;
-- an argument is simple if it is either one of variables in @vars@ or does not contain any of @vars@;
-- in the latter case the argument is represented as a fresh name and a constraint
extractArgs :: [Id] -> [Expression] -> [(Id, [Expression])]
extractArgs vars args = foldl extractArg [] (zip args [0..])
  where
    extractArg res ((Pos p e), i) = let 
      x = freshArgName i 
      xExpr = attachPos p $ Var x
      in res ++
        case e of
          Var arg -> if arg `elem` vars
            then if arg `elem` map fst res
              then [(x, [xExpr |=| Pos p e])]      -- Bound variable that already occurred: use fresh variable as formal, add equality guard
              else [(arg, [])]                     -- New bound variable: use variable name as formal, no additional guards
            else [(x, [xExpr |=| Pos p e])]        -- Constant: use fresh variable as formal, add equality guard
          _ -> if null $ freeVars (Pos p e) `intersect` nonfixedBV
                  then [(x, [xExpr |=| Pos p e])]  -- Expression where all bound variables are already fixed: use fresh variable as formal, add equality guard
                  else []                          -- Expression involving non-fixed bound variables: not a simple argument, omit
    freshArgName i = nonIdChar : show i
    varArgs = [v | (Pos p (Var v)) <- args]
    nonfixedBV = vars \\ varArgs    
       
{- Quantification -}

-- | Sets of interval constraints on integer variables
type IntervalConstraints = Map Id Interval
            
-- | The set of domains for each variable in vars, outside which boolean expression boolExpr is always false.
-- Fails if any of the domains are infinite or cannot be found.
domains :: (Monad m, Functor m) => Expression -> [Id] -> Execution m [Domain]
domains boolExpr vars = do
  initC <- foldM initConstraints M.empty vars
  finalC <- inferConstraints boolExpr initC 
  forM vars (domain finalC)
  where
    initConstraints c var = do
      tc <- use envTypeContext
      qbound <- use envQBound
      case M.lookup var (allVars tc) of
        Just BoolType         -> return c
        Just (MapType _ _ _)  -> throwRuntimeFailure (UnsupportedConstruct "quantification over a map") (position boolExpr)
        Just t                -> return $ M.insert var (defaultDomain qbound t) c        
    defaultDomain qbound t = case qbound of
      Nothing -> top
      Just n -> let 
        (lower, upper) = case t of
          IntType -> intInterval n
          IdType _ _ -> natInterval n
        in Interval (Finite lower) (Finite upper)
    domain c var = do
      tc <- use envTypeContext
      case M.lookup var (allVars tc) of
        Just BoolType -> return $ map BoolValue [True, False]
        Just t -> do
          case c ! var of
            int | isBottom int -> return []
            Interval (Finite l) (Finite u) -> return $ map (valueFromInteger t) [l..u]
            int -> throwRuntimeFailure (InfiniteDomain var int) (position boolExpr)

-- | Starting from initial constraints, refine them with the information from boolExpr,
-- until fixpoint is reached or the domain for one of the variables is empty.
-- This function terminates because the interval for each variable can only become smaller with each iteration.
inferConstraints :: (Monad m, Functor m) => Expression -> IntervalConstraints -> Execution m IntervalConstraints
inferConstraints boolExpr constraints = do
  constraints' <- foldM refineVar constraints (M.keys constraints)
  if bot `elem` M.elems constraints'
    then return $ M.map (const bot) constraints'  -- if boolExpr does not have a satisfying assignment to one variable, then it has none to all variables
    else if constraints == constraints'
      then return constraints'                    -- if a fixpoint is reached, return it
      else inferConstraints boolExpr constraints' -- otherwise do another iteration
  where
    refineVar :: (Monad m, Functor m) => IntervalConstraints -> Id -> Execution m IntervalConstraints
    refineVar c id = do
      int <- inferInterval boolExpr c id
      return $ M.insert id (meet (c ! id) int) c 

-- | Infer an interval for variable x, outside which boolean expression booExpr is always false, 
-- assuming all other quantified variables satisfy constraints;
-- boolExpr has to be in negation-prenex normal form.
inferInterval :: (Monad m, Functor m) => Expression -> IntervalConstraints -> Id -> Execution m Interval
inferInterval boolExpr constraints x = (case node boolExpr of
  FF -> return bot
  BinaryExpression And be1 be2 -> liftM2 meet (inferInterval be1 constraints x) (inferInterval be2 constraints x)
  BinaryExpression Or be1 be2 -> liftM2 join (inferInterval be1 constraints x) (inferInterval be2 constraints x)
  BinaryExpression Eq ae1 ae2 -> do
    (a, b) <- toLinearForm (ae1 |-| ae2) constraints x
    if 0 <: a && 0 <: b
      then return top
      else return $ -b // a
  BinaryExpression Leq ae1 ae2 -> do
    (a, b) <- toLinearForm (ae1 |-| ae2) constraints x
    if isBottom a || isBottom b
      then return bot
      else if 0 <: a && not (isBottom (meet b nonPositives))
        then return top
        else return $ join (lessEqual (-b // meet a positives)) (greaterEqual (-b // meet a negatives))
  BinaryExpression Ls ae1 ae2 -> inferInterval (ae1 |<=| (ae2 |-| num 1)) constraints x
  BinaryExpression Geq ae1 ae2 -> inferInterval (ae2 |<=| ae1) constraints x
  BinaryExpression Gt ae1 ae2 -> inferInterval (ae2 |<=| (ae1 |-| num 1)) constraints x
  -- Quantifier can only occur here if it is alternating with the enclosing one, hence no domain can be inferred 
  _ -> return top
  ) `catchError` handleNotLinear
  where      
    lessEqual int | isBottom int = bot
                  | otherwise = Interval NegInf (upper int)
    greaterEqual int  | isBottom int = bot
                      | otherwise = Interval (lower int) Inf
    handleNotLinear err = case rtfSource err of
      InternalException NotLinear -> return top
      _ -> throwError err                      

-- | Linear form (A, B) represents a set of expressions a*x + b, where a in A and b in B
type LinearForm = (Interval, Interval)

-- | If possible, convert arithmetic expression aExpr into a linear form over variable x,
-- assuming all other quantified variables satisfy constraints.
toLinearForm :: (Monad m, Functor m) => Expression -> IntervalConstraints -> Id -> Execution m LinearForm
toLinearForm aExpr constraints x = case node aExpr of
  Numeral n -> return (0, fromInteger n)
  Var y -> if x == y
    then return (1, 0)
    else case M.lookup y constraints of
      Just int -> return (0, int)
      Nothing -> const aExpr
  Application name args -> if null $ M.keys constraints `intersect` freeVars aExpr
    then const aExpr
    else throwInternalException NotLinear
  MapSelection m args -> if null $ M.keys constraints `intersect` freeVars aExpr
    then const aExpr
    else throwInternalException NotLinear
  Old e -> old $ toLinearForm e constraints x
  UnaryExpression Neg e -> do
    (a, b) <- toLinearForm e constraints x
    return (-a, -b)
  BinaryExpression op e1 e2 -> do
    left <- toLinearForm e1 constraints x
    right <- toLinearForm e2 constraints x 
    combineBinOp op left right
  where
    const e = do
      v <- eval e
      case v of
        IntValue n -> return (0, fromInteger n)
    combineBinOp Plus   (a1, b1) (a2, b2) = return (a1 + a2, b1 + b2)
    combineBinOp Minus  (a1, b1) (a2, b2) = return (a1 - a2, b1 - b2)
    combineBinOp Times  (a, b)   (0, k)   = return (k * a, k * b)
    combineBinOp Times  (0, k)   (a, b)   = return (k * a, k * b)
    combineBinOp _ _ _ = throwInternalException NotLinear
    
{- Map equality -}

-- | 'evalEquality' @v1 v2@ : Evaluate @v1 == v2@
evalEquality :: (Monad m, Functor m) => Value -> Value -> Execution m Value
evalEquality v1 v2 = do
  h <- use $ envMemory.memHeap
  case objectEq h v1 v2 of
    Just b -> return $ BoolValue b
    Nothing -> decideEquality v1 v2  -- No evidence yet if two maps are equal or not, make a non-deterministic choice
  where
    decideEquality (Reference r1) (Reference r2) = do
      h <- use $ envMemory.memHeap
      let (s1, vals1) = flattenMap h r1
      let (s2, vals2) = flattenMap h r2
      mustEqual <- generate genBool                     -- Decide if maps should be considered equal right away
      if mustEqual
        then do makeEq v1 v2; return $ BoolValue True               -- Make the maps equal and return True
        else if s1 == s2                                            -- Otherwise: if the maps come from the same source
          then decideOverrideEquality r1 vals1 r2 vals2               -- Then the difference must be in overrides
          else if mustAgree h vals1 vals2                             -- Otherwise: if the difference cannot be in overrides
            then do makeSourceNeq s1 s2; return $ BoolValue False       -- Then make the sources incompatible and return False
            else do                                                     -- Otherwise we can freely choose if the difference is in the source or in the overrides
              compareOverrides <- generate genBool                      -- Make a choice
              if compareOverrides
                then decideOverrideEquality r1 vals1 r2 vals2           -- decide equality based on overrides
                else do makeSourceNeq s1 s2; return $ BoolValue False   -- otherwise make the sources incompatible and return False
    decideOverrideEquality r1 vals1 r2 vals2 = do
      let diff = if hasMapValues $ vals1 `M.intersection` vals2                     -- If there are maps stored at common indexes
          then vals1 `M.union` vals2                                                -- then even values at a common index might be different
          else (vals2 `M.difference` vals1) `M.union` (vals1 `M.difference` vals2)  -- otherwise only values at non-shared indexes might be different
      (i, val) <- (`M.elemAt` diff) <$> generate (`genIndex` M.size diff) -- Choose an index at which the values might be different
      val1 <- lookupStored r1 i val
      val2 <- lookupStored r2 i val
      BoolValue answer <- evalEquality val1 val2
      when answer $ makeEq v1 v2
      return $ BoolValue answer 
    hasMapValues m
      | M.null m  = False
      | otherwise = case M.findMin m of
        (_, Reference _) -> True
        _ -> False      
    lookupStored r i template = do
      h <- use $ envMemory.memHeap
      let (s, vals) = flattenMap h r    
      case M.lookup i vals of
        Just v -> return v
        Nothing -> do
          v <- generateValueLike template
          setMapValue s i v
          return v
    makeSourceNeq s1 s2 = do
      setMapValue s1 [special s1, special s2] (special s1)
      setMapValue s2 [special s1, special s2] (special s2)
    special r = CustomValue refIdTypeName $ fromIntegral r
          
-- | Ensure that two compatible values are equal
makeEq :: (Monad m, Functor m) => Value -> Value -> Execution m ()
makeEq (Reference r1) (Reference r2) = do
  h <- use $ envMemory.memHeap
  let (s1, vals1) = flattenMap h r1
  let (s2, vals2) = flattenMap h r2
  zipWithM_ makeEq (M.elems $ vals1 `M.intersection` vals2) (M.elems $ vals2 `M.intersection` vals1) -- Enforce that the values at shared indexes are equal
  if s1 == s2
    then do -- Same source; compatible, but nonequal overrides
      mapM_ (uncurry $ setMapValue s1) (M.toList $ vals2 `M.difference` vals1) -- Store values only defined in r2 in the source
      mapM_ (uncurry $ setMapValue s1) (M.toList $ vals1 `M.difference` vals2) -- Store values only defined in r1 in the source
    else do -- Different sources
      Reference newSource <- allocate . MapValue . Source $ vals1 `M.union` vals2
      mapM_ decRefCountValue (M.elems (vals2 `M.intersection` vals1)) -- Take care of references from vals2 that are no longer used
      derive r1 newSource
      derive r2 newSource
      mergeConstraints s1 s2 newSource
  where
    derive r newSource = do
      deriveBaseOf r newSource M.empty
      envMemory.memHeap %= update r (MapValue (Derived newSource M.empty))      
      envMemory.memHeap %= incRefCount newSource      
    deriveBaseOf r newSource diffR = do
      MapValue repr <- readHeap r
      case repr of
        Source _ -> return ()
        Derived base override -> do
          let diffBase = override `M.union` diffR -- The difference between base and newSource
          h <- use $ envMemory.memHeap
          let vals = mapValues h base
          deriveBaseOf base newSource diffBase
          newVals <- foldM addMissing (vals `M.intersection` diffBase) (M.toList $ diffBase `M.difference` vals) -- Choose arbitrary values for all keys in diffBase that are not defined for base
          envMemory.memHeap %= update base (MapValue (Derived newSource newVals))
          envMemory.memHeap %= incRefCount newSource
          envMemory.memHeap %= decRefCount base
    addMissing vals (key, oldVal) = do
      newVal <- generateValueLike oldVal
      incRefCountValue newVal
      return $ M.insert key newVal vals
    mergeConstraints s1 s2 newSource = do
      (defs1, constraints1) <- gets $ lookupMapConstraints s1
      (defs2, constraints2) <- gets $ lookupMapConstraints s2
      envConstraints.amHeap %= M.insert newSource (defs1 ++ defs2, constraints1 ++ constraints2)
makeEq (MapValue _) (MapValue _) = internalError "Attempt to call makeEq on maps directly" 
makeEq _ _ = return ()  