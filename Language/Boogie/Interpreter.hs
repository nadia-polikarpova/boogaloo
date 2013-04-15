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
  testCaseDoc,
  sessionSummaryDoc,
  -- * Executing parts of programs
  eval,
  exec,
  preprocess
  ) where

import Language.Boogie.Environment  
import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Heap
import Language.Boogie.Generator
import Language.Boogie.Position
import Language.Boogie.Tokens (nonIdChar)
import Language.Boogie.Pretty
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
    result (Left err, env) = TestCase sig (env^.envMemory) (env^.envConstraints) (Just err)
    result (_, env)      = TestCase sig (env^.envMemory) (env^.envConstraints) Nothing    
            
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
  inOld <- use envInOld
  if inOld
    then execution
    else do
      outerEnv <- get
      envMemory.memGlobals .= outerEnv^.envMemory.memOld
      envInOld .= True            
      res <- execution
      innerMem <- use envMemory
      envMemory.memOld .= innerMem^.memGlobals
      -- Restore globals to their outer values and add feshly initialized globals
      envMemory.memGlobals .= (outerEnv^.envMemory.memGlobals) `M.union` (removeDomain (innerMem^.memModified) (innerMem^.memGlobals))
      envInOld .= False
      return res

-- | Save current values of global variables in memOld, return the caller memory
saveOld :: (Monad m, Functor m) => Execution m Memory 
saveOld = do
  callerMem <- use envMemory
  let globals = callerMem^.memGlobals
  envMemory.memOld .= globals
  mapM_ incRefCountValue (M.elems globals) -- Each value stored in globals is now pointed by an additional (old) variable
  envMemory.memModified .= S.empty
  return $ callerMem

-- | 'restoreOld' @callerMem@ : restore 'memOld' to its value from @callerMem@
restoreOld :: (Monad m, Functor m) => Memory -> Execution m ()  
restoreOld callerMem = do
  -- Among the callee's old values, those that had not been modified by the caller are "clean" (should be propagated back to the caller)
  (dirtyOlds, cleanOlds) <- uses (envMemory.memOld) $ partitionDomain (callerMem^.memModified)
  envMemory.memOld .= (callerMem^.memOld) `M.union` cleanOlds
  mapM_ decRefCountValue (M.elems dirtyOlds) -- Dirty old values go out of scope
  envMemory.memModified %= ((callerMem^.memModified) `S.union`)
  
-- | Execute computation in a local context
executeLocally :: (MonadState (Environment m) s, Finalizer s) => (Context -> Context) -> [Id] -> [Value] -> [Expression] -> s a -> s a
executeLocally localTC formals actuals localWhere computation = do
  oldEnv <- get
  envTypeContext %= localTC
  envMemory.memLocals .= M.empty
  zipWithM_ (setVar memLocals) formals actuals
  mapM_ (extendNameConstraint symLocals) localWhere
  computation `finally` unwind oldEnv
  where
    -- | Restore type context and the values of local variables 
    unwind oldEnv = do
      locals <- use $ envMemory.memLocals
      mapM_ decRefCountValue (M.elems locals)
      envTypeContext .= oldEnv^.envTypeContext
      envMemory.memLocals .= oldEnv^.envMemory.memLocals
      envConstraints.symLocals .= oldEnv^.envConstraints.symLocals
      
-- | Exucute computation in a nested context      
executeNested :: (MonadState (Environment m) s, Finalizer s) => TypeBinding -> [IdType] -> s a -> s a
executeNested inst locals computation = do
  oldEnv <- get
  envTypeContext %= nestedContext inst locals
  envMemory.memLocals %= deleteAll localNames
  computation `finally` unwind oldEnv
  where
    -- | Restore type context and the values of local variables 
    localNames = map fst locals
    unwind oldEnv = do      
      envTypeContext .= oldEnv^.envTypeContext
      mapM_ (unsetVar memLocals) localNames
      envMemory.memLocals %= (`M.union` (oldEnv^.envMemory.memLocals)) . deleteAll localNames
     
-- | Execute computation in a global context     
executeGlobally :: (MonadState (Environment m) s, Finalizer s) => s a -> s a
executeGlobally computation = do
  oldEnv <- get
  envTypeContext %= globalContext
  envMemory.memLocals .= M.empty
  envConstraints.symLocals .= M.empty
  computation `finally` unwind oldEnv
  where
    -- | Restore type context and the values of local variables 
    unwind oldEnv = do
      envTypeContext .= oldEnv^.envTypeContext
      envMemory.memLocals .= oldEnv^.envMemory.memLocals
      envConstraints.symLocals .= oldEnv^.envConstraints.symLocals  
                              
{- Runtime failures -}

data FailureSource = 
  SpecViolation SpecClause (Maybe Expression) | -- ^ Violation of user-defined specification
  UnsupportedConstruct Doc |                    -- ^ Language construct is not yet supported (should disappear in later versions)
  InternalException InternalCode                -- ^ Must be cought inside the interpreter and never reach the user
  
instance Eq FailureSource where
  SpecViolation clause1 lt1 == SpecViolation clause2 lt2  = clause1 == clause2 && maybe2 True samePos lt1 lt2
  UnsupportedConstruct doc1 == UnsupportedConstruct doc2  = doc1 == doc2
  InternalException code1 == InternalException code2      = code1 == code2
  _ == _                                                  = False
  
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

-- | Throw a spec violation
throwViolation specClause pos = do
  lt <- use envLastTerm
  throwRuntimeFailure (SpecViolation specClause lt) pos

-- | Kinds of run-time failures
data FailureKind = Error | -- ^ Error state reached (assertion violation)
  Unreachable | -- ^ Unreachable state reached (assumption violation)
  Nonexecutable -- ^ The state is OK in Boogie semantics, but the execution cannot continue due to the limitations of the interpreter
  deriving Eq

-- | Kind of a run-time failure
failureKind :: RuntimeFailure -> FailureKind
failureKind err = case rtfSource err of
  SpecViolation (SpecClause _ True _) _ -> Unreachable
  SpecViolation (SpecClause _ False _) _ -> Error
  _ -> Nonexecutable
  
instance Error RuntimeFailure where
  noMsg    = RuntimeFailure (UnsupportedConstruct $ text "unknown") noPos emptyMemory []
  strMsg s = RuntimeFailure (UnsupportedConstruct $ text s) noPos emptyMemory []
  
-- | Pretty-printed run-time failure
runtimeFailureDoc debug err = 
  let store = (if debug then id else userStore ((rtfMemory err)^.memHeap)) (M.filterWithKey (\k _ -> isRelevant k) (visibleVariables (rtfMemory err)))
      sDoc = storeDoc store 
  in failureSourceDoc (rtfSource err) <+> posDoc (rtfPos err) <+> 
    (nest 2 $ option (not (isEmpty sDoc)) (text "with") $+$ sDoc) $+$
    vsep (map stackFrameDoc (reverse (rtfTrace err)))
  where
    failureSourceDoc (SpecViolation (SpecClause specType isFree e) lt) = text (clauseName specType isFree) <+> dquotes (pretty e) <+> defPosition specType e <+>
      lastTermDoc lt <+>
      text "violated"
    failureSourceDoc (UnsupportedConstruct s) = text "Unsupported construct" <+> s
    
    clauseName Inline isFree = if isFree then "Assumption" else "Assertion"  
    clauseName Precondition isFree = if isFree then "Free precondition" else "Precondition"  
    clauseName Postcondition isFree = if isFree then "Free postcondition" else "Postcondition"  
    clauseName LoopInvariant isFree = if isFree then "Free loop invariant" else "Loop invariant"  
    clauseName Where True = "Where clause"  -- where clauses cannot be non-free  
    clauseName Axiom True = "Axiom"  -- axioms cannot be non-free  
    
    defPosition Inline _ = empty
    defPosition LoopInvariant _ = empty
    defPosition _ e = text "defined" <+> posDoc (position e)
    
    lastTermDoc lt = case lt of
      Nothing -> empty
      Just t -> parens (text "last evaluated term:" <+> dquotes (pretty t) <+> posDoc (position t))
    
    isRelevant k = case rtfSource err of
      SpecViolation (SpecClause _ _ expr) _ -> k `elem` freeVars expr
      _ -> False
    
    stackFrameDoc f = text "in call to" <+> text (callName f) <+> posDoc (callPos f)
    posDoc pos
      | pos == noPos = text "from the environment"
      | otherwise = text "on line" <+> int (sourceLine pos)

instance Pretty RuntimeFailure where pretty err = runtimeFailureDoc True err
  
-- | Do two runtime failures represent the same fault?
-- Yes if the same property failed at the same program location
-- or, for preconditions, for the same caller   
instance Eq RuntimeFailure where
  f == f' = rtfSource f == rtfSource f' && rtfPos f == rtfPos f'
    
-- | Internal error codes 
data InternalCode = NotLinear | UnderConstruction Int
  deriving Eq

throwInternalException code = throwRuntimeFailure (InternalException code) noPos

{- Execution results -}
    
-- | Description of an execution
data TestCase = TestCase {
  tcProcedure :: PSig,                -- ^ Root procedure (entry point) of the execution
  tcMemory :: Memory,                 -- ^ Final memory state (at the exit from the root procedure) 
  tcSymbolicMemory :: SymbolicMemory, -- ^ Final symbolic memory state (at the exit from the root procedure) 
  tcFailure :: Maybe RuntimeFailure   -- ^ Failure the execution eded with, or Nothing if the execution ended in a valid state
}

-- | 'isPass' @tc@: Does @tc@ end in a valid state?
isPass :: TestCase -> Bool
isPass (TestCase _ _ _ Nothing) =  True
isPass _ =          False

-- | 'isInvalid' @tc@: Does @tc@ and in an unreachable state?
isInvalid :: TestCase -> Bool 
isInvalid (TestCase _ _ _ (Just err))
  | failureKind err == Unreachable = True
isInvalid _                        = False

-- | 'isNonexecutable' @tc@: Does @tc@ end in a non-executable state?
isNonexecutable :: TestCase -> Bool 
isNonexecutable (TestCase _ _ _ (Just err))
  | failureKind err == Nonexecutable  = True
isNonexecutable _                     = False

-- | 'isFail' @tc@: Does @tc@ end in an error state?
isFail :: TestCase -> Bool
isFail tc = not (isPass tc || isInvalid tc || isNonexecutable tc)

-- | Remove empty maps from a store
removeEmptyMaps = M.filter $ not . isEmptyMap

-- | 'testCaseDoc' @debug header n tc@ : Pretty printed @tc@',
-- displayed in user or debug format depending on 'debug'
-- with a header "'header' 'n':".
testCaseDoc :: Bool -> String -> Integer -> TestCase -> Doc
testCaseDoc debug header n tc = 
  auxDoc (text header <+> integer n <> text ":") <+> 
  testCaseSummary debug tc $+$
  case tcFailure tc of
    Just err -> errorDoc (runtimeFailureDoc debug err) $+$
      option debug (linebreak <> finalStateDoc True tc)
    Nothing -> finalStateDoc debug tc  

-- | 'testCaseSummary' @debug tc@ : Summary of @tc@'s inputs and outcome
testCaseSummary debug tc@(TestCase sig mem symMem mErr) = (text (psigName sig) <> 
  parens (commaSep (map (inDoc . itwId) (psigArgs sig))) <>
  (option (not $ M.null globalInputs) ((tupled . map globDoc . M.toList) globalInputs))) <+>
  outcomeDoc tc
  where
    mem' = if debug then mem else userMemory symMem mem
    globalInputs = removeEmptyMaps $ (mem'^.memOld) `M.union` (mem'^.memConstants)
    inDoc name = pretty $ (mem'^.memLocals) ! name
    globDoc (name, val) = text name <+> text "=" <+> pretty val
    outcomeDoc tc 
      | isPass tc = text "passed"
      | isInvalid tc = text "invalid"
      | isNonexecutable tc = text "non-executable"
      | otherwise = text "failed"
      
-- | 'finalStateDoc' @debug tc@ : outputs of @tc@, 
-- displayed in user or debug format depending on 'debug' 
finalStateDoc :: Bool -> TestCase -> Doc
finalStateDoc debug tc@(TestCase sig mem symMem mErr) = memoryDoc [] outNames finalMem $+$
  if debug then pretty symMem else empty
  where
    finalMem =  over memLocals (removeEmptyMaps . restrictDomain (S.fromList outNames)) $ 
                over memOld (const M.empty) $
                over memGlobals removeEmptyMaps $
                over memConstants removeEmptyMaps $
                if debug then mem else userMemory symMem mem
    outNames = map itwId (psigRets sig)
    
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
instance Pretty Summary where 
  pretty summary =
    text "Test cases:" <+> int (totalCount summary) $+$
    text "Passed:" <+> int (sPassCount summary) $+$
    text "Invalid:" <+> int (sInvalidCount summary) $+$
    text "Non executable:" <+> int (sNonExecutableCount summary) $+$
    text "Failed:" <+> int (sFailCount summary) <+> parens (int (length (sUniqueFailures summary)) <+> text "unique")

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

-- | Pretty-printed summary of a test session
sessionSummaryDoc :: Bool -> [TestCase] -> Doc
sessionSummaryDoc debug tcs = let sum = testSessionSummary tcs 
  in vsep . punctuate linebreak $
    pretty sum :
    zipWith (testCaseDoc debug "Failure") [0..] (sUniqueFailures sum)

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
  IdType x [] | isTypeVar [] x -> throwRuntimeFailure (UnsupportedConstruct (text "choice of a value from unknown type" <+> pretty t)) pos
  -- Maps are initializaed lazily, allocate an empty map on the heap:
  t@(MapType _ _ _) -> allocate t emptyMap
  BoolType -> BoolValue <$> generate genBool
  IntType -> IntValue <$> generate genInteger
  t@(IdType _ _) -> do
    n <- gets $ lookupCustomCount t
    i <- generate (`genIndex` (n + 1))
    when (i == n) $ modify (setCustomCount t (n + 1))
    return $ CustomValue t i
          
-- | 'incRefCountValue' @val@ : if @val@ is a reference, increase its count
incRefCountValue val = case val of
  Reference _ r -> envMemory.memHeap %= incRefCount r
  _ -> return ()    

-- | 'decRefCountValue' @val@ : if @val@ is a reference, decrease its count  
decRefCountValue val = case val of
  Reference _ r -> envMemory.memHeap %= decRefCount r
  _ -> return ()     
    
-- | 'unsetVar' @getter name@ : if @name@ was associated with a reference in @getter@, decrease its reference count
unsetVar getter name = do
  store <- use $ envMemory.getter
  case M.lookup name store of    
    Just (Reference _ r) -> do          
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
      
-- | 'forgetAnyVar' @name@ : forget value of a constant, global or local variable @name@
forgetAnyVar name = do
  tc <- use envTypeContext
  if M.member name (localScope tc)
    then forgetVar memLocals name
    else if M.member name (ctxGlobals tc)
      then forgetVar memGlobals name
      else forgetVar memConstants name
      
-- | 'setMapValue' @r index val@ : map @index@ to @val@ in the map referenced by @r@
setMapValue r index val = do
  vals <- readHeap r
  envMemory.memHeap %= update r (M.insert index val vals)
  incRefCountValue val
  
-- | 'forgetMapValue' @r index@ : forget value at @index@ in the map referenced by @r@  
-- (@r@ has to be a source map)
forgetMapValue r index = do
  vals <- readHeap r
  case M.lookup index vals of
    Nothing -> return ()
    Just val -> do
      decRefCountValue val
      envMemory.memHeap %= update r (M.delete index vals)
      
-- | 'readHeap' @r@: current value of reference @r@ in the heap
readHeap r = flip at r <$> use (envMemory.memHeap)
    
-- | 'allocate': store an empty map of type @t@ at a fresh location in the heap
allocate :: (Monad m, Functor m) => Type -> MapRepr -> Execution m Value
allocate t repr = Reference t <$> (state . withHeap . alloc) repr
  
-- | Remove all unused references from the heap  
collectGarbage :: (Monad m, Functor m) => Execution m ()  
collectGarbage = do
  h <- use $ envMemory.memHeap
  when (hasGarbage h) (do
    r <- state $ withHeap dealloc
    mapM_ decRefCountValue (M.elems $ h `at` r)
    cs <- gets $ lookupMapConstraints r
    let usedRefs = nub . concatMap mapRefs $ concatMap (\c -> [defGuard c, defBody c]) (fst cs) ++ snd cs 
    mapM_ (\r -> envMemory.memHeap %= decRefCount r) usedRefs    
    envConstraints.symHeap %= M.delete r
    collectGarbage)
    
-- | 'extendNameConstraint' @lens con@ : add @con@ as a constraint for all free variables in @con@ to @envConstraints.lens@
extendNameConstraint :: (MonadState (Environment m) s, Finalizer s) => SimpleLens SymbolicMemory NameConstraints -> Expression -> s ()
extendNameConstraint lens con = do
  mapM_ (\name -> modify $ addNameConstraint name (envConstraints.lens) con) (freeVars con)

-- | 'extendMapDefinition' @r def@ : add @def@ to the definiton of the map @r@
extendMapDefinition r def = do
  modify $ addMapDefinition r def
  let usedRefs = nub $ mapRefs (defGuard def) ++ mapRefs (defBody def)
  mapM_ (\r -> envMemory.memHeap %= incRefCount r) usedRefs    

-- | 'extendMapConstraint' @r c@ : add @c@ to the consraints of the map @r@  
extendMapConstraint r c = do
  modify $ addMapConstraint r c
  mapM_ (\r -> envMemory.memHeap %= incRefCount r) (mapRefs c)
  
{- Expressions -}

-- | Semantics of unary operators
unOp :: UnOp -> Value -> Value
unOp Neg (IntValue n)   = IntValue (-n)
unOp Not (BoolValue b)  = BoolValue (not b)

-- | Short-circuit boolean operators
shortCircuitOps = [And, Or, Implies, Explies]

-- | Short-circuit semantics of binary operators:
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
                                                then generateValue IntType pos
                                                else return $ IntValue (fst (n1 `euclidean` n2))
binOp pos Mod     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                then generateValue IntType pos
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
binOp pos Eq      v1 v2                         = evalEquality v1 v2 pos
binOp pos Neq     v1 v2                         = vnot <$> evalEquality v1 v2 pos
binOp pos Lc      v1 v2                         = throwRuntimeFailure (UnsupportedConstruct $ text "orders") pos

-- | Euclidean division used by Boogie for integer division and modulo
euclidean :: Integer -> Integer -> (Integer, Integer)
a `euclidean` b =
  case a `quotRem` b of
    (q, r) | r >= 0    -> (q, r)
           | b >  0    -> (q - 1, r + b)
           | otherwise -> (q + 1, r - b)
           
-- | 'evalEquality' @v1 v2 pos@ : Evaluate @v1 == v2@ at position @pos@
evalEquality :: (Monad m, Functor m) => Value -> Value -> SourcePos -> Execution m Value
evalEquality v1@(Reference t1 r1) v2@(Reference t2 r2) pos = if r1 == r2
  then return (BoolValue True) -- Equal references point to equal maps
  else if t1 /= t2 -- Different types can occur in a generic context
    then return (BoolValue False)
    else let
        MapType tv domains range = t1
        freshVarNames = map (\i -> nonIdChar : show i) [0..]
        vars = zip freshVarNames domains
        lit = attachPos pos . Literal
        var = attachPos pos . Var
        app m = attachPos pos $ MapSelection (lit m) (map (var . fst) vars)
      in evalForall tv vars (app v1 |=| app v2) pos
evalEquality (MapValue _ _) (MapValue _ _) _ = internalError $ text "Attempt to compare two maps"
evalEquality v1 v2 _ = return $ BoolValue (v1 == v2)           
         
-- | Evaluate an expression;
-- can have a side-effect of initializing variables that were not previously defined
eval :: (Monad m, Functor m) => Expression -> Execution m Value
eval expr = do
  envLastTerm .= Nothing
  evalSub expr

-- | Evaluate a sub-epression (this should be called instead of eval from inside expression evaluation)  
evalSub expr = case node expr of
  Literal v -> return v
  Var name -> evalVar name (position expr)
  Application name args -> evalApplication name args (position expr)
  MapSelection m args -> evalMapSelection m args (position expr)
  MapUpdate m args new -> evalMapUpdate m args new (position expr)
  Old e -> old $ evalSub e
  IfExpr cond e1 e2 -> evalIf cond e1 e2
  Coercion e t -> evalSub e
  UnaryExpression op e -> evalUnary op e
  BinaryExpression op e1 e2 -> evalBinary op e1 e2
  Quantified Lambda tv vars e -> evalLambda tv vars e (position expr)
  Quantified Forall tv vars e -> evalForall tv vars e (position expr)
  Quantified Exists tv vars e -> vnot <$> evalForall tv vars (enot e) (position expr)
  
evalVar :: (Monad m, Functor m) => Id -> SourcePos -> Execution m Value  
evalVar name pos = do
  tc <- use envTypeContext
  case M.lookup name (localScope tc) of
    Just t -> evalVarWith t memLocals False
    Nothing -> case M.lookup name (ctxGlobals tc) of
      Just t -> do
        inOld <- use envInOld
        modified <- use $ envMemory.memModified
        -- Also initialize the old value of the global, unless we are evaluating and old expression (because of garbage collection) or the variable has been already modified:
        executeGlobally $ evalVarWith t memGlobals (not inOld && S.notMember name modified)
      Nothing -> case M.lookup name (ctxConstants tc) of
        Just t -> executeGlobally $ evalVarWith t memConstants False
        Nothing -> internalError $ text "Encountered unknown identifier during execution:" <+> text name
  where  
    evalVarWith :: (Monad m, Functor m) => Type -> StoreLens -> Bool -> Execution m Value
    evalVarWith t lens initOld = do
      s <- use $ envMemory.lens
      case M.lookup name s of         -- Lookup a cached value
        Just val -> return val
        Nothing -> do                 -- If not found, choose a value non-deterministically
          chosenValue <- generateValue t pos
          setVar lens name chosenValue
          when initOld $ setVar memOld name chosenValue
          checkNameConstraints name pos
          return chosenValue
              
evalApplication :: (Monad m, Functor m) => Id -> [Expression] -> SourcePos -> Execution m Value  
evalApplication name args pos = evalMapSelection (functionExpr name pos) args pos  
        
rejectMapIndex pos idx = case idx of
  Reference _ r -> throwRuntimeFailure (UnsupportedConstruct $ text "map as an index") pos
  _ -> return ()
      
evalMapSelection m args pos = do  
  mV <- evalSub m
  case mV of
    Reference _ r -> do
      argsV <- mapM evalSub args
      h <- use $ envMemory.memHeap
      case M.lookup argsV (h `at` r) of    -- Lookup a cached value
        Just val -> wellDefined val
        Nothing -> do                           -- If not found, look for an applicable definition          
          tc <- use envTypeContext          
          definedValue <- checkMapDefinitions r argsV pos
          case definedValue of
            Just val -> do
              inDef <- use envInDef
              cache r argsV val (not inDef)
            Nothing -> do                       -- If not found, choose a value non-deterministically
              mapM_ (rejectMapIndex pos) argsV
              let rangeType = exprType tc (gen $ MapSelection m args)
              chosenValue <- generateValue rangeType pos
              cache r argsV chosenValue True
    _ -> return mV -- function without arguments (ToDo: is this how it should be handled?)
  where
    cache r argsV val check = do              
      setMapValue r argsV val
      when check $ checkMapConstraints r argsV pos
      return val
        
evalMapUpdate m args new pos = do
  mVal@(Reference t r) <- evalSub m
  argsVals <- mapM evalSub args
  mapM_ (rejectMapIndex pos) argsVals
  newVal <- evalSub new
  repr <- readHeap r
  newMVal@(Reference _ r') <- allocate t (M.insert argsVals newVal repr)
  let lit = attachPos pos . Literal    
      var = attachPos pos . Var
      freshVarNames = map (\i -> nonIdChar : show i) [0..]
      bv = zip freshVarNames domains
      bvExprs = map (var . fst) bv
      MapType tv domains _ = t
      appOld = attachPos pos $ MapSelection (lit mVal) bvExprs
      appNew = attachPos pos $ MapSelection (lit newMVal) bvExprs
      guard = disjunction (zipWith (|!=|) bvExprs (map lit argsVals))
      constraint = inheritPos (Quantified Lambda tv bv) (guard |=>| (appOld |=| appNew))
  extendMapConstraint r constraint
  extendMapConstraint r' constraint  
  extendMapDefinition r (Def tv bv guard appNew)
  extendMapDefinition r' (Def tv bv guard appOld)
  return newMVal
  
evalIf cond e1 e2 = do
  v <- evalSub cond
  case v of
    BoolValue True -> evalSub e1    
    BoolValue False -> evalSub e2    
    
evalUnary op e = unOp op <$> evalSub e    
      
evalBinary op e1 e2 = if op `elem` shortCircuitOps
  then do -- Keep track of which terms got evaluated
    envLastTerm .= Just e1
    left <- evalSub e1
    case binOpLazy op left of
      Just result -> return result
      Nothing -> do
        envLastTerm .= Just e2
        right <- evalSub e2
        binOp (position e1) op left right
  else do
    left <- evalSub e1
    right <- evalSub e2
    binOp (position e1) op left right
    
evalLambda tv vars e pos = do
  tc <- use envTypeContext
  let t = exprType tc (lambda e)
  val@(Reference _ r) <- generateValue t pos
  (Quantified Lambda _ _ symBody) <- node <$> symbolicEval (lambda e)
  extendMapDefinition r (def symBody)
  let app = attachPos pos $ MapSelection (attachPos pos $ Literal val) (map (attachPos pos . Var . fst) vars)
  extendMapConstraint r (lambda $ app |=| symBody)
  return val
  where
    lambda = attachPos pos . Quantified Lambda tv vars
    def = Def tv vars (conjunction [])
    
evalForall :: (Monad m, Functor m) => [Id] -> [IdType] -> Expression -> SourcePos -> Execution m Value
evalForall tv vars e pos = do  
  symExpr <- symbolicEval (attachPos pos $ Quantified Forall tv vars e)
  let mc = extractMapConstraints symExpr
  BoolValue <$> allM evalForMap (M.toList mc)
  where
    evalForMap (r, (defs, constraints)) = do      
      satCache <- allM (checkCached r) constraints
      if not satCache  -- If any cached values do not satisfy the constraint
        then return False   -- found evidence that the constraint does not hold
        else do             -- no evidence yet if the constraint holds for all arguments, make a non-deterministic choice for every constraint           
          satDecide <- allM (decideConstraint r) constraints 
          when satDecide $ mapM_ (extendMapDefinition r) defs
          when satDecide $ mapM_ (extendMapConstraint r) constraints
          return satDecide          
    checkCached r c = do
      cache <- readHeap r
      allM (\actuals -> applyConstraint c actuals pos) (M.keys cache)
    decideConstraint r c@(Pos _ (Quantified Lambda tv vars _)) = do
      let typeBinding = M.fromList $ zip tv (repeat anyType)
      let argTypes = map (typeSubst typeBinding . snd) vars
      -- ToDo: we could plug in linear analysis here and replace with genIndex sometimes
      index <- mapM (flip generateValue pos) argTypes -- choose an index non-deterministically
      applyConstraint c index pos
          
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
  b <- unValueBool <$> eval (specExpr specClause)
  when (not b) $ throwViolation specClause pos
    
execHavoc names pos = do
  mapM_ forgetAnyVar names
  mapM_ (modify . markModified) names
    
execAssign lhss rhss = do
  rVals <- mapM eval rhss'
  zipWithM_ resetAnyVar lhss' rVals
  mapM_ (modify . markModified) lhss' 
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
  let lhssExpr = map (gen . Var) lhss
  retsV <- execProcedure sig' def args lhssExpr pos `catchError` addFrame
  zipWithM_ resetAnyVar lhss retsV
  where
    selectDef tc [] = return (assumePostconditions sig, dummyDef tc)
    selectDef tc defs = do
      i <- generate (`genIndex` length defs)
      return (sig, defs !! i)
    -- For procedures with no implementation: dummy definition that just havocs all modifiable globals
    dummyDef tc = PDef {
        pdefIns = map itwId (psigArgs sig),
        pdefOuts = map itwId (psigRets sig),
        pdefParamsRenamed = False,
        pdefBody = ([], (M.fromList . toBasicBlocks . singletonBlock . gen . Havoc . psigModifies) sig),
        pdefPos = noPos
      }
    addFrame err = addStackFrame (StackFrame pos (psigName sig)) err
        
-- | 'execBlock' @blocks label@: Execute program consisting of @blocks@ starting from the block labeled @label@.
-- Return the location of the exit point.
execBlock :: (Monad m, Functor m) => Map Id [Statement] -> Id -> Execution m SourcePos
execBlock blocks label = let
  block = blocks ! label
  statements = init block
  in do
    mapM exec statements
    case last block of
      Pos pos Return -> return pos
      Pos _ (Goto lbs) -> do
        i <- generate (`genIndex` length lbs)
        execBlock blocks (lbs !! i)
    
-- | 'execProcedure' @sig def args lhss@ :
-- Execute definition @def@ of procedure @sig@ with actual arguments @args@ and call left-hand sides @lhss@
execProcedure :: (Monad m, Functor m) => PSig -> PDef -> [Expression] -> [Expression] -> SourcePos -> Execution m [Value]
execProcedure sig def args lhss callPos = let 
  ins = pdefIns def
  outs = pdefOuts def
  blocks = snd (pdefBody def)
  exitPoint pos = if pos == noPos 
    then pdefPos def  -- Fall off the procedure body: take the procedure definition location
    else pos          -- A return statement inside the body
  execBody = do
    checkPreconditions sig def callPos   
    pos <- exitPoint <$> execBlock blocks startLabel
    checkPostonditions sig def pos    
    mapM (eval . attachPos (pdefPos def) . Var) outs
  in do
    argsV <- mapM eval args
    mem <- saveOld
    executeLocally (enterProcedure sig def args lhss) ins argsV (map itwWhere (psigRets sig ++ fst (pdefBody def))) execBody `finally` restoreOld mem
    
{- Specs -}

-- | Assert preconditions of definition def of procedure sig
checkPreconditions sig def callPos = mapM_ (exec . attachPos callPos . Predicate . subst sig) (psigRequires sig)
  where 
    subst sig (SpecClause t f e) = SpecClause t f (paramSubst sig def e)

-- | Assert postconditions of definition def of procedure sig at exitPoint    
checkPostonditions sig def exitPoint = mapM_ (exec . attachPos exitPoint . Predicate . subst sig) (psigEnsures sig)
  where 
    subst sig (SpecClause t f e) = SpecClause t f (paramSubst sig def e)

{- Constraints and symbolic execution -}

-- | 'symbolicEval' @expr@ : evaluate @expr@ modulo quantification
symbolicEval expr = symbolicEval' [] expr
  where
    symbolicEval' vars (Pos p e) = attachPos p <$> case e of
      l@(Literal _) -> return l
      var@(Var name) -> if name `elem` vars
        then return var
        else Literal <$> evalVar name p
      Application name args -> node <$> symbolicEval' vars (attachPos p $ MapSelection (functionExpr name p) args)
      MapSelection m args -> do
        m' <- symbolicEval' vars m
        args' <- mapM (symbolicEval' vars) args
        if all isLiteral (m' : args')
          then Literal <$> evalMapSelection m' args' p
          else return $ MapSelection m' args'
      MapUpdate m args new -> do
        m' <- symbolicEval' vars m
        args' <- mapM (symbolicEval' vars) args
        new' <- symbolicEval' vars new
        if all isLiteral (m' : new' : args')
          then Literal <$> evalMapUpdate m' args' new' p
          else return $ MapUpdate m' args' new'   
      Old e -> node <$> old (symbolicEval' vars e)
      IfExpr cond e1 e2 -> do
        cond' <- symbolicEval' vars cond
        e1' <- symbolicEval' vars e1
        e2' <- symbolicEval' vars e2
        if all isLiteral [cond', e1', e2']
          then Literal <$> evalIf cond' e1' e2'
          else return $ IfExpr cond' e1' e2'
      Coercion e t -> node <$> symbolicEval' vars e
      UnaryExpression op e -> do
        e' <- symbolicEval' vars e
        if isLiteral e'
          then Literal <$> evalUnary op e'
          else return $ UnaryExpression op e'
      BinaryExpression op e1 e2 -> do
        e1' <- symbolicEval' vars e1
        e2' <- symbolicEval' vars e2
        if isLiteral e1' && isLiteral e2'
          then Literal <$> evalBinary op e1' e2'
          else return $ BinaryExpression op e1' e2'
      Quantified qop tv bv e -> Quantified qop tv bv <$> symbolicEval' (vars ++ map fst bv) e
      
-- | Evaluate all free variables in a definiton
symbolicEvalDef :: (Monad m, Functor m) => Def -> Execution m Def
symbolicEvalDef def@(Def tv formals guard body) = do
  (Quantified Lambda _ _ guard') <- node <$> symbolicEval (defGuardLambda def)
  (Quantified Lambda _ _ body') <- node <$> symbolicEval (defBodyLambda def)
  return $ Def tv formals guard' body'      
        
-- | 'wellDefined' @val@ : throw an exception if @val@ is under construction
wellDefined (CustomValue t n) | t == ucType = throwInternalException $ UnderConstruction n
wellDefined val = return val

-- | 'checkNameConstraints' @name pos@ : execute where clause of variable @name@ at position @pos@
checkNameConstraints name pos = do
  cs <- gets $ lookupNameConstraints name
  mapM_ (\c -> execPredicate (SpecClause Axiom True c) pos) cs
  
-- | 'checkDefinitions' @myCode defs actuals pos@ : return the result of the first definition from @defs@ applicable to @actuals@;
-- if none are applicable return 'Nothing', 
-- unless an under construction value different from @myCode@ has been evaluated, in which case rethrow the UnderConstruction exception;
-- @pos@ is the position of the definition invocation
checkDefinitions :: (Monad m, Functor m) => Int -> [Def] -> [Value] -> SourcePos -> Execution m (Maybe Value)
checkDefinitions myCode defs actuals pos = checkDefinitions' myCode Nothing defs actuals pos

checkDefinitions' _ Nothing     [] _ _ = return Nothing
checkDefinitions' _ (Just code) [] _ _ = throwInternalException (UnderConstruction code)
checkDefinitions' myCode mCode (def : defs) actuals pos = tryDefinitions `catchError` ucHandler
  where
    tryDefinitions = do      
      mVal <- applyDefinition def actuals pos
      case mVal of
        Just val -> return mVal
        Nothing -> checkDefinitions' myCode mCode defs actuals pos 
    ucHandler err = case rtfSource err of
      InternalException (UnderConstruction code) -> if code == myCode
        then checkDefinitions' myCode mCode defs actuals pos
        else checkDefinitions' myCode (Just code) defs actuals pos
      _ -> throwError err      
      
-- | 'applyDefinition' @def actuals pos@ : 
-- if @guard (actuals)@ return the result of @body (actuals)@,
-- otherwise return 'Nothing'
-- (@pos@ is the position of the definition invocation)      
applyDefinition def@(Def tv formals guard body) actuals pos = do
  if isNothing $ unifier tv formalTypes actualTypes -- Is the definition applicable to these types?
    then return Nothing
    else do
      applicable <- unValueBool <$> evalInDef guard -- Is the definition applicable to these values?
      res <- if not applicable
        then return Nothing
        else Just <$> evalInDef body
      return res
  where
    formalNames = map fst formals
    formalTypes = map snd formals
    actualTypes = map valueType actuals
    locally = if null formals
        then id
        else executeLocally (\ctx -> ctx { ctxLocals = M.fromList (zip formalNames actualTypes) }) formalNames actuals []
    evalInDef expr = do
      oldInDef <- use envInDef
      envInDef .= True
      res <- locally (evalSub expr) `finally` (envInDef .= oldInDef)
      return res
        
-- | 'checkMapDefinitions' @r actuals pos@ : return a value at index @actuals@ 
-- in the map referenced by @r@ mentioned at @pos@, if there is an applicable definition 
checkMapDefinitions :: (Monad m, Functor m) => Ref -> [Value] -> SourcePos -> Execution m (Maybe Value)    
checkMapDefinitions r actuals pos = do  
  n <- gets $ lookupCustomCount ucType
  setMapValue r actuals $ CustomValue ucType n  
  modify $ setCustomCount ucType (n + 1)  
  defs <- fst <$> gets (lookupMapConstraints r)
  checkDefinitions n defs actuals pos `finally` cleanup n
  where  
    cleanup n = do
      forgetMapValue r actuals
      modify $ setCustomCount ucType n

-- | 'applyConstraint' @c actuals pos@ : 
-- return if @c (actuals)@ holds
-- (@pos@ is the position of the constraint invocation)      
applyConstraint c actuals pos = case node c of
  Quantified Lambda tv formals body ->
    let 
      formalNames = map fst formals
      formalTypes = map snd formals
      actualTypes = map valueType actuals
      locally = executeLocally (\ctx -> ctx { ctxLocals = M.fromList (zip formalNames actualTypes) }) formalNames actuals []    
    in if isNothing $ unifier tv formalTypes actualTypes -- Is the constraint applicable to these types?
      then return True
      else unValueBool <$> locally (evalSub body)
  _ -> unValueBool <$> evalSub c  
        
-- | 'checkMapConstraints' @r actuals pos@ : assume all constraints for the value at index @actuals@ 
-- in the map referenced by @r@ mentioned at @pos@
checkMapConstraints r actuals pos = do
  constraints <- snd <$> gets (lookupMapConstraints r)
  mc <- findM (\c -> not <$> applyConstraint c actuals pos) constraints
  when (isJust mc) (throwViolation (SpecClause Axiom True $ fromJust mc) pos)
  
{- Preprocessing -}

-- | Collect procedure implementations, and constant/function/global variable constraints
preprocess :: (Monad m, Functor m) => Program -> SafeExecution m ()
preprocess (Program decls) = mapM_ processDecl decls
  where
    processDecl decl = case node decl of
      FunctionDecl name _ args _ mBody -> processFunction name (map fst args) mBody
      ProcedureDecl name _ args rets _ (Just body) -> processProcedureBody name (position decl) (map noWhere args) (map noWhere rets) body
      ImplementationDecl name _ args rets bodies -> mapM_ (processProcedureBody name (position decl) args rets) bodies
      AxiomDecl expr -> extendNameConstraint symGlobals expr
      VarDecl vars -> mapM_ (extendNameConstraint symGlobals) (map itwWhere vars)      
      _ -> return ()
      
processFunction name argNames mBody = do
  sig@(MapType tv argTypes retType) <- funSig name <$> use envTypeContext
  let constName = functionConst name  
  envTypeContext %= \tc -> tc { ctxConstants = M.insert constName sig (ctxConstants tc) }    
  case mBody of
    Nothing -> return ()
    Just body -> do
      let pos = position body
      let formals = zip (map formalName argNames) argTypes
      let app = attachPos pos $ Application name (map (attachPos pos . Var . fst) formals)
      let axiom = inheritPos (Quantified Forall tv formals) (app |=| body)      
      extendNameConstraint symGlobals axiom
  where        
    formalName Nothing = dummyFArg 
    formalName (Just n) = n
    
processProcedureBody name pos args rets body = do
  tc <- use envTypeContext
  let params = psigParams $ procSig name tc
  let paramsRenamed = map itwId params /= (argNames ++ retNames)    
  let flatBody = (map (mapItwType (resolve tc)) (concat $ fst body), M.fromList (toBasicBlocks $ snd body))
  let allLocals = params ++ fst flatBody
  modify $ addProcedureImpl name (PDef argNames retNames paramsRenamed flatBody pos) 
  where
    argNames = map fst args
    retNames = map fst rets

{- Constant and function constraints -}

-- | 'extractMapConstraints' @bExpr@ : extract definitions and constraints from @bExpr@
-- @bExpr@ must not contain any free variables
extractMapConstraints :: Expression -> MapConstraints
extractMapConstraints bExpr = extractConstraints' [] [] [] (negationNF bExpr)

-- | 'extractConstraints'' @tv vars guards body@ : extract definitions and constraints from expression @guards@ ==> @body@
-- bound type variables @tv@ and bound variables @vars@
extractConstraints' :: [Id] -> [IdType] -> [Expression] -> Expression -> MapConstraints
extractConstraints' tv vars guards body = case (node body) of
  Quantified Forall tv' vars' bExpr -> extractConstraints' (tv ++ tv') (vars ++ vars') guards bExpr
  Quantified Exists _ _ _ -> M.empty -- ToDo: skolemize?
  BinaryExpression And bExpr1 bExpr2 -> let
    constraints1 = extractConstraints' tv vars guards bExpr1
    constraints2 = extractConstraints' tv vars guards bExpr2
    in constraints1 `constraintUnion` constraints2
  BinaryExpression Or bExpr1 bExpr2 -> let
    constraints1 = extractConstraints' tv vars ((negationNF $ enot bExpr1) : guards) bExpr2
    constraints2 = extractConstraints' tv vars ((negationNF $ enot bExpr2) : guards) bExpr1
    in constraints1 `constraintUnion` constraints2
  BinaryExpression Eq expr1 expr2 -> let
    defs1 = extractDefsAtomic expr1 expr2
    defs2 = extractDefsAtomic expr2 expr1
    constraints = extractConstraintsAtomic
    in foldr1 constraintUnion [defs1, defs2, constraints]
  _ -> extractConstraintsAtomic
  where
    -- | Bound variables used in body or guards:
    allFreeVars = freeVars body ++ concatMap freeVars guards
    usedVars = [(v, t) | (v, t) <- vars, v `elem` allFreeVars]
    boundTC = emptyContext { ctxTypeVars = tv, ctxLocals = M.fromList vars }
  
    extractDefsAtomic lhs rhs = case defLhs lhs of
      Just (x, args) -> addDefFor x args rhs
      Nothing -> M.empty
    addDefFor x args rhs = let
        argTypes = map (exprType boundTC) args
        (formals, argGuards) = unzip $ extractArgs (map fst usedVars) args
        allGuards = concat argGuards ++ guards
        extraVars = [(v, t) | (v, t) <- usedVars, v `notElem` formals]
      in if length formals == length args && null extraVars -- Only possible if all arguments are simple and there are no extra variables
        then M.singleton x ([Def tv (zip formals argTypes) (conjunction allGuards) rhs], [])
        else M.empty
    
    -- We extract a parametrized constraint from an application if its arguments contain at least one bound variable
    extractConstraintsAtomic = foldr constraintUnion M.empty $ map addConstraintFor (refSelections body)
    addConstraintFor (x, args) = let
        argTypes = map (exprType boundTC) args
        (formals, argGuards) = unzip $ extractArgs (map fst usedVars) args
        allArgGuards = concat argGuards
        (argVars, extraVars) = partition (\(v, t) -> v `elem` formals) usedVars
        constraint = if null extraVars
          then guardWith guards body
          else inheritPos (Quantified Forall tv extraVars) (guardWith guards body) -- outer guards are inserted into the body, because they might contain extraVars
      in if not (null argVars) &&       -- argumnets contain bound variables
          length formals == length args -- all arguments are simple
        then M.singleton x ([], [inheritPos (Quantified Lambda tv (zip formals argTypes)) (guardWith allArgGuards constraint)])
        else M.empty
        
    defLhs e = case node e of
      MapSelection (Pos _ (Literal (Reference _ r))) args -> Just (r, args)
      _ -> Nothing        
            
-- | 'extractArgs' @vars args@: extract simple arguments from @args@;
-- an argument is simple if it is either one of variables in @vars@ or does not contain any of @vars@;
-- in the latter case the argument is represented as a fresh name and a guard
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
       