{-# LANGUAGE FlexibleContexts, Rank2Types #-}

-- | Interpreter for Boogie 2
module Language.Boogie.Interpreter (
  -- * Executing programs
  Execution,
  executeProgram,
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

import Language.Boogie.Solver  
import Language.Boogie.Environment
import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Heap hiding (Heap)
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
      
-- | 'executeProgram' @p tc solver entryPoint@ :
-- Execute program @p@ in type context @tc@ with solver @solver@, starting from procedure @entryPoint@,
-- and return the outcome(s) embedded into the solver's monad.
executeProgram :: (Monad m, Functor m) => Program -> Context -> Solver m -> Id -> m (TestCase)
executeProgram p tc solver entryPoint = result <$> runStateT (runErrorT programExecution) (initEnv tc solver)
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
  envMemory.memModified .= S.empty
  return $ callerMem

-- | 'restoreOld' @callerMem@ : restore 'memOld' to its value from @callerMem@
restoreOld :: (Monad m, Functor m) => Memory -> Execution m ()  
restoreOld callerMem = do
  -- Among the callee's old values, those that had not been modified by the caller are "clean" (should be propagated back to the caller)
  (dirtyOlds, cleanOlds) <- uses (envMemory.memOld) $ partitionDomain (callerMem^.memModified)
  envMemory.memOld .= (callerMem^.memOld) `M.union` cleanOlds
  envMemory.memModified %= ((callerMem^.memModified) `S.union`)
  
-- | Execute computation in a local context
executeLocally :: (MonadState (Environment m) s, Finalizer s) => (Context -> Context) -> [Id] -> [Thunk] -> [Expression] -> s a -> s a
executeLocally localTC formals actuals localWhere computation = do
  oldEnv <- get
  envTypeContext %= localTC
  envMemory.memLocals .= M.empty
  zipWithM_ (setVar memLocals) formals actuals
  mapM_ (extendNameConstaints conLocals) localWhere
  computation `finally` unwind oldEnv
  where
    -- | Restore type context and the values of local variables 
    unwind oldEnv = do
      locals <- use $ envMemory.memLocals
      envTypeContext .= oldEnv^.envTypeContext
      envMemory.memLocals .= oldEnv^.envMemory.memLocals
      envConstraints.conLocals .= oldEnv^.envConstraints.conLocals
      
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
      envMemory.memLocals %= (`M.union` (oldEnv^.envMemory.memLocals)) . deleteAll localNames
     
-- | Execute computation in a global context     
executeGlobally :: (MonadState (Environment m) s, Finalizer s) => s a -> s a
executeGlobally computation = do
  oldEnv <- get
  envTypeContext %= globalContext
  envMemory.memLocals .= M.empty
  envConstraints.conLocals .= M.empty
  computation `finally` unwind oldEnv
  where
    -- | Restore type context and the values of local variables 
    unwind oldEnv = do
      envTypeContext .= oldEnv^.envTypeContext
      envMemory.memLocals .= oldEnv^.envMemory.memLocals
      envConstraints.conLocals .= oldEnv^.envConstraints.conLocals  
                              
{- Runtime failures -}

data FailureSource = 
  SpecViolation SpecClause |      -- ^ Violation of user-defined specification
  UnsupportedConstruct Doc        -- ^ Language construct is not yet supported (should disappear in later versions)
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
  _ -> Nonexecutable
  
instance Error RuntimeFailure where
  noMsg    = RuntimeFailure (UnsupportedConstruct $ text "unknown") noPos emptyMemory []
  strMsg s = RuntimeFailure (UnsupportedConstruct $ text s) noPos emptyMemory []
  
-- | Pretty-printed run-time failure
runtimeFailureDoc debug err = 
  let store = (if debug then id else userStore ((rtfMemory err)^.memMaps)) (M.filterWithKey (\k _ -> isRelevant k) (visibleVariables (rtfMemory err)))
      sDoc = storeDoc store 
  in failureSourceDoc (rtfSource err) <+> posDoc (rtfPos err) <+> 
    (nest 2 $ option (not (isEmpty sDoc)) (text "with") $+$ sDoc) $+$
    vsep (map stackFrameDoc (reverse (rtfTrace err)))
  where
    failureSourceDoc (SpecViolation (SpecClause specType isFree e)) = text (clauseName specType isFree) <+> dquotes (pretty e) <+> defPosition specType e <+>
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
        
    isRelevant k = case rtfSource err of
      SpecViolation (SpecClause _ _ expr) -> k `elem` freeVars expr
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

{- Execution results -}
    
-- | Description of an execution
data TestCase = TestCase {
  tcProcedure :: PSig,                -- ^ Root procedure (entry point) of the execution
  tcMemory :: Memory,                 -- ^ Final memory state (at the exit from the root procedure) 
  tcSymbolicMemory :: ConstraintMemory, -- ^ Final symbolic memory state (at the exit from the root procedure) 
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
removeEmptyMaps = id -- M.filter $ not . isEmptyMap

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
testCaseSummary debug tc@(TestCase sig mem conMem mErr) = (text (psigName sig) <> 
  parens (commaSep (map (inDoc . itwId) (psigArgs sig))) <>
  (option (not $ M.null globalInputs) ((tupled . map globDoc . M.toList) globalInputs))) <+>
  outcomeDoc tc
  where
    mem' = if debug then mem else userMemory conMem mem
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
finalStateDoc debug tc@(TestCase sig mem conMem mErr) = memoryDoc [] outNames finalMem $+$
  if debug then pretty conMem else empty
  where
    finalMem =  over memLocals (removeEmptyMaps . restrictDomain (S.fromList outNames)) $ 
                over memOld (const M.empty) $
                over memGlobals removeEmptyMaps $
                over memConstants removeEmptyMaps $
                if debug then mem else userMemory conMem mem
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
  
-- | 'freshLogical': generate a fresh logical variable reference
freshLogical :: (Monad m, Functor m) => Execution m Ref
freshLogical = do
  l <- use envLogicalCount
  envLogicalCount %= (+ 1)
  return l
  
-- | 'freshMapRef' @cache@: store @cache@ at a fresh map reference and return it
freshMapRef :: (Monad m, Functor m) => MapCache -> Execution m Ref
freshMapRef cache = (state . withHeap . alloc) cache  
      
-- | 'generateValue' @t pos@ : choose a value of type @t@ at source position @pos@;
-- fail if @t@ is a type variable
generateValue :: (Monad m, Functor m) => Type -> SourcePos -> Execution m Thunk
generateValue t pos = case t of
  IdType x [] | isTypeVar [] x -> throwRuntimeFailure (UnsupportedConstruct (text "choice of a value from unknown type" <+> pretty t)) pos
  t@(MapType _ _ _) -> (attachPos pos . Literal . Reference t) <$> freshMapRef emptyMap
  t -> (attachPos pos . Logical t) <$> freshLogical
              
-- | 'setVar' @setter name val@ : set value of variable @name@ to @val@ using @setter@
setVar setter name val = do
  envMemory.setter %= M.insert name val
  
-- | 'resetAnyVar' @name val@ : set value of a constant, global or local variable @name@ to @val@
setAnyVar name val = do
  tc <- use envTypeContext
  if M.member name (localScope tc)
    then setVar memLocals name val
    else if M.member name (ctxGlobals tc)
      then setVar memGlobals name val
      else setVar memConstants name val  
      
-- | 'forgetVar' @lens name@ : forget value of variable @name@ in @lens@;
-- if @name@ was associated with a reference, decrease its reference count      
forgetVar :: (Monad m, Functor m) => StoreLens -> Id -> Execution m ()
forgetVar lens name = do
  envMemory.lens %= M.delete name
      
-- | 'forgetAnyVar' @name@ : forget value of a constant, global or local variable @name@
forgetAnyVar name = do
  tc <- use envTypeContext
  if M.member name (localScope tc)
    then forgetVar memLocals name
    else if M.member name (ctxGlobals tc)
      then forgetVar memGlobals name
      else forgetVar memConstants name
      
-- | 'getMapCache' @r@: current cache of map @r@
getMapCache r = flip at r <$> use (envMemory.memMaps)      
      
-- | 'setMapValue' @r index val@ : map @index@ to @val@ in the map referenced by @r@
setMapValue r index val = do
  vals <- getMapCache r
  envMemory.memMaps %= update r (M.insert index val vals)
  
-- | 'forgetMapValue' @r index@ : forget value at @index@ in the map referenced by @r@  
-- (@r@ has to be a source map)
forgetMapValue r index = do
  vals <- getMapCache r
  case M.lookup index vals of
    Nothing -> return ()
    Just val -> envMemory.memMaps %= update r (M.delete index vals)

{- Expressions -}
         
-- | Evaluate an expression;
-- can have a side-effect of initializing variables and map points that were not previously defined
eval :: (Monad m, Functor m) => Expression -> Execution m Thunk
eval expr@(Pos pos e) = case e of
  Literal v -> return expr
  Var name -> evalVar name pos
  Logical t r -> evalLogical t r pos
  Application name args -> evalApplication name args pos
  MapSelection m args -> evalMapSelection m args pos
  MapUpdate m args new -> evalMapUpdate m args new pos
  Old e -> old $ eval e
  IfExpr cond e1 e2 -> evalIf cond e1 e2
  Coercion e t -> eval e
  UnaryExpression op e -> evalUnary op e
  BinaryExpression op e1 e2 -> evalBinary op e1 e2
  Quantified Lambda tv vars e -> evalLambda tv vars e pos
  Quantified Forall tv vars e -> evalForall tv vars e pos
  Quantified Exists tv vars e -> evalForall tv vars (enot e) pos >>= evalUnary Not
  
evalLogical t r pos = do
  vals <- use $ envMemory.memLogical
  return $ case M.lookup r vals of
            Nothing -> attachPos pos $ Logical t r
            Just val -> val  
  
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
    evalVarWith :: (Monad m, Functor m) => Type -> StoreLens -> Bool -> Execution m Thunk
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
              
evalApplication name args pos = evalMapSelection (functionExpr name pos) args pos  
        
rejectMapIndex pos idx = case thunkType idx of
  MapType _ _ _ -> throwRuntimeFailure (UnsupportedConstruct $ text "map as an index") pos
  _ -> return ()
      
evalMapSelection m args pos = do  
  m' <- eval m
  case fromLiteral m' of
    Reference _ r -> do
      args' <- mapM eval args
      mapM_ (rejectMapIndex pos) args'
      mCache <- getMapCache r
      case M.lookup args' mCache of    -- Lookup a cached value
        Just val -> return val
        Nothing -> do                       -- If not found, choose a value non-deterministically
          let rangeType = thunkType (gen $ MapSelection m' args')
          chosenValue <- generateValue rangeType pos
          setMapValue r args' chosenValue
          checkMapConstraints r args' pos
          return chosenValue
    _ -> return m' -- function without arguments (ToDo: is this how it should be handled?)
        
evalMapUpdate m args new pos = do
  m' <- eval m
  let Reference t r = fromLiteral m'
  args' <- mapM eval args
  mapM_ (rejectMapIndex pos) args'
  new' <- eval new    
  mRepr <- getMapCache r
  newM' <- generateValue t pos
  let Reference _ r' = fromLiteral newM'
  let var = attachPos pos . Var
      freshVarNames = map (\i -> nonIdChar : show i) [0..]
      bv = zip freshVarNames domains
      bvExprs = map (var . fst) bv
      MapType tv domains _ = t
      appOld = attachPos pos $ MapSelection m' bvExprs
      appNew = attachPos pos $ MapSelection newM' bvExprs
      guardNeq = disjunction (zipWith (|!=|) bvExprs args')
      guardEq = conjunction (zipWith (|=|) bvExprs args')
      lambda = inheritPos (Quantified Lambda tv bv)
  extendMapConstaints r $ lambda (guardNeq |=>| (appOld |=| appNew))
  extendMapConstaints r' $ lambda (guardNeq |=>| (appOld |=| appNew))  
  extendMapConstaints r' $ lambda (guardEq |=>| (appNew |=| new'))
  return newM'
  
evalIf cond e1 e2 = do
  cond' <- eval cond
  if isLiteral cond'
    then case fromLiteral cond' of
      BoolValue True -> eval e1    
      BoolValue False -> eval e2    
    else do
      e1' <- eval e1
      e2' <- eval e2
      return $ attachPos (position cond) $ IfExpr cond' e1' e2'
      
-- | Semantics of unary operators
unOp :: UnOp -> Value -> Value
unOp Neg (IntValue n)   = IntValue (-n)
unOp Not (BoolValue b)  = BoolValue (not b)      
    
evalUnary op e  = do
  e' <- eval e
  return . attachPos (position e) $ if isLiteral e'
                              then Literal $ unOp op $ fromLiteral e'
                              else UnaryExpression op e'
                                                            
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
binOp :: (Monad m, Functor m) => SourcePos -> BinOp -> Value -> Value -> Execution m Thunk 
binOp pos Plus    (IntValue n1) (IntValue n2)   = return $ attachPos pos $ Literal $ IntValue (n1 + n2)
binOp pos Minus   (IntValue n1) (IntValue n2)   = return $ attachPos pos $ Literal $ IntValue (n1 - n2)
binOp pos Times   (IntValue n1) (IntValue n2)   = return $ attachPos pos $ Literal $ IntValue (n1 * n2)
binOp pos Div     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                then generateValue IntType pos
                                                else return $ attachPos pos $ Literal $ IntValue (fst (n1 `euclidean` n2))
binOp pos Mod     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                then generateValue IntType pos
                                                else return $ attachPos pos $ Literal $ IntValue (snd (n1 `euclidean` n2))
binOp pos Leq     (IntValue n1) (IntValue n2)   = return $ attachPos pos $ Literal $ BoolValue (n1 <= n2)
binOp pos Ls      (IntValue n1) (IntValue n2)   = return $ attachPos pos $ Literal $ BoolValue (n1 < n2)
binOp pos Geq     (IntValue n1) (IntValue n2)   = return $ attachPos pos $ Literal $ BoolValue (n1 >= n2)
binOp pos Gt      (IntValue n1) (IntValue n2)   = return $ attachPos pos $ Literal $ BoolValue (n1 > n2)
binOp pos And     (BoolValue b1) (BoolValue b2) = return $ attachPos pos $ Literal $ BoolValue (b1 && b2)
binOp pos Or      (BoolValue b1) (BoolValue b2) = return $ attachPos pos $ Literal $ BoolValue (b1 || b2)
binOp pos Implies (BoolValue b1) (BoolValue b2) = return $ attachPos pos $ Literal $ BoolValue (b1 <= b2)
binOp pos Explies (BoolValue b1) (BoolValue b2) = return $ attachPos pos $ Literal $ BoolValue (b1 >= b2)
binOp pos Equiv   (BoolValue b1) (BoolValue b2) = return $ attachPos pos $ Literal $ BoolValue (b1 == b2)
binOp pos Eq      v1 v2                         = evalEquality pos v1 v2
binOp pos Neq     v1 v2                         = evalEquality pos v1 v2 >>= evalUnary Not
binOp pos Lc      v1 v2                         = throwRuntimeFailure (UnsupportedConstruct $ text "orders") pos

-- | Euclidean division used by Boogie for integer division and modulo
euclidean :: Integer -> Integer -> (Integer, Integer)
a `euclidean` b =
  case a `quotRem` b of
    (q, r) | r >= 0    -> (q, r)
           | b >  0    -> (q - 1, r + b)
           | otherwise -> (q + 1, r - b)
           
-- | 'evalEquality' @v1 v2 pos@ : Evaluate @v1 == v2@ at position @pos@
evalEquality :: (Monad m, Functor m) => SourcePos -> Value -> Value -> Execution m Thunk
evalEquality pos v1@(Reference t1 r1) v2@(Reference t2 r2) = if r1 == r2
  then return $ lit (BoolValue True) -- Equal references point to equal maps
  else if t1 /= t2 -- Different types can occur in a generic context
    then return $ lit (BoolValue False)
    else let
        MapType tv domains range = t1
        freshVarNames = map (\i -> nonIdChar : show i) [0..]
        vars = zip freshVarNames domains                
        app m = attachPos pos $ MapSelection (lit m) (map (var . fst) vars)
      in evalForall tv vars (app v1 |=| app v2) pos
  where
    lit = attachPos pos . Literal
    var = attachPos pos . Var
-- evalEquality (MapValue _ _) (MapValue _ _) _ = internalError $ text "Attempt to compare two maps"
evalEquality pos v1 v2 = return $ attachPos pos $ Literal $ BoolValue (v1 == v2)                              
      
evalBinary op e1 e2 = do
  let pos = position e1
  e1' <- eval e1
  if isLiteral e1' && op `elem` shortCircuitOps && isJust (binOpLazy op (fromLiteral e1'))
    then return $ attachPos pos $ Literal $ fromJust $ binOpLazy op (fromLiteral e1')
    else do
      e2' <- eval e2
      if isLiteral e1' && isLiteral e2'
        then binOp pos op (fromLiteral e1') (fromLiteral e2')
        else return $ attachPos pos $ BinaryExpression op e1' e2'
    
evalLambda tv vars e pos = do
  tc <- use envTypeContext
  let t = exprType tc (lambda e)
  m' <- generateValue t pos
  (Quantified Lambda _ _ symBody) <- node <$> evalQuantified (lambda e)
  let var = attachPos pos . Var      
      app = attachPos pos $ MapSelection m' (map (var . fst) vars)
      Reference _ r = fromLiteral m'
  extendMapConstaints r (lambda $ app |=| symBody)
  return m'
  where
    lambda = attachPos pos . Quantified Lambda tv vars
    
evalForall tv vars e pos = do  
  symExpr <- evalQuantified (attachPos pos $ Quantified Forall tv vars e)
  res <- generateValue BoolType pos
  samples <- mapM (evalForMap res) (M.toList $ extractMapConstraints symExpr)
  extendLogicalConstaints $ res |=| conjunction samples
  return res
  where
    evalForMap res (r, constraints) = do
      samples <- mapM (evalConstraint res r) constraints
      return $ conjunction samples
    evalConstraint res r c = do       
      cache <- getMapCache r
      cacheRs <- mapM (\actuals -> applyMapConstraint c actuals pos) (M.keys cache)
      newR <- decideConstraint r c
      addGuardedConstraint res r c
      return $ conjunction (cacheRs ++ [newR])
    decideConstraint r c@(Pos _ (Quantified Lambda tv vars _)) = do
      let typeBinding = M.fromList $ zip tv (repeat anyType)
      let argTypes = map (typeSubst typeBinding . snd) vars
      index <- mapM (flip generateValue pos) argTypes -- choose an index non-deterministically
      applyMapConstraint c index pos
    addGuardedConstraint res r (Pos p (Quantified Lambda tv vars e)) = extendMapConstaints r (Pos p (Quantified Lambda tv vars (res |=>| e)))
    lit = attachPos pos . Literal
          
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
  
execPredicate (SpecClause source True expr) pos = do
  c <- eval expr
  extendLogicalConstaints c

execPredicate clause@(SpecClause source False expr) pos = do
  c <- eval expr
  solveConstraints
  c' <- eval c
  case fromLiteral c' of
    BoolValue True -> return ()
    BoolValue False -> throwRuntimeFailure (SpecViolation clause) pos
    
execHavoc names pos = do
  mapM_ forgetAnyVar names
  mapM_ (modify . markModified) names
    
execAssign lhss rhss = do
  rVals <- mapM eval rhss'
  zipWithM_ setAnyVar lhss' rVals
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
  zipWithM_ setAnyVar lhss retsV
  where
    selectDef tc [] = return (assumePostconditions sig, dummyDef tc)
    selectDef tc defs = do
      i <- genIndex $ length defs
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
        i <- genIndex $ length lbs
        execBlock blocks (lbs !! i)
    
-- | 'execProcedure' @sig def args lhss@ :
-- Execute definition @def@ of procedure @sig@ with actual arguments @args@ and call left-hand sides @lhss@
execProcedure :: (Monad m, Functor m) => PSig -> PDef -> [Expression] -> [Expression] -> SourcePos -> Execution m [Thunk]
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

{- Evaluating constraints -}

-- | 'extendNameConstaints' @lens c@ : add @c@ as a constraint for all free variables in @c@ to @envConstraints.lens@
extendNameConstaints :: (MonadState (Environment m) s, Finalizer s) => SimpleLens ConstraintMemory NameConstraints -> Expression -> s ()
extendNameConstaints lens c = mapM_ (\name -> modify $ addNameConstraint name (envConstraints.lens) c) (freeVars c)

-- | 'extendMapConstaints' @r c@ : add @c@ to the constraints of the map @r@  
extendMapConstaints r c = modify $ addMapConstraint r c

-- | 'extendLogicalConstaints' @c@ : add @c@ to the logical constraints
extendLogicalConstaints c = modify $ addLogicalConstraint c

-- | 'evalQuantified' @expr@ : evaluate @expr@ modulo quantification
evalQuantified expr = evalQuantified' [] expr
  where
    evalQuantified' vars (Pos p e) = attachPos p <$> case e of
      l@(Literal _) -> return l
      l@(Logical _ _) -> return l
      var@(Var name) -> if name `elem` vars
        then return var
        else node <$> evalVar name p
      Application name args -> node <$> evalQuantified' vars (attachPos p $ MapSelection (functionExpr name p) args)
      MapSelection m args -> do
        m' <- evalQuantified' vars m
        args' <- mapM (evalQuantified' vars) args
        if all isLiteral (m' : args')
          then node <$> evalMapSelection m' args' p
          else return $ MapSelection m' args'
      MapUpdate m args new -> do
        m' <- evalQuantified' vars m
        args' <- mapM (evalQuantified' vars) args
        new' <- evalQuantified' vars new
        if all isLiteral (m' : new' : args')
          then node <$> evalMapUpdate m' args' new' p
          else return $ MapUpdate m' args' new'   
      Old e -> node <$> old (evalQuantified' vars e)
      IfExpr cond e1 e2 -> do
        cond' <- evalQuantified' vars cond
        e1' <- evalQuantified' vars e1
        e2' <- evalQuantified' vars e2
        if all isLiteral [cond', e1', e2']
          then node <$> evalIf cond' e1' e2'
          else return $ IfExpr cond' e1' e2'
      Coercion e t -> node <$> evalQuantified' vars e
      UnaryExpression op e -> do
        e' <- evalQuantified' vars e
        if isLiteral e'
          then node <$> evalUnary op e'
          else return $ UnaryExpression op e'
      BinaryExpression op e1 e2 -> do
        e1' <- evalQuantified' vars e1
        e2' <- evalQuantified' vars e2
        if isLiteral e1' && isLiteral e2'
          then node <$> evalBinary op e1' e2'
          else return $ BinaryExpression op e1' e2'
      Quantified qop tv bv e -> Quantified qop tv bv <$> evalQuantified' (vars ++ map fst bv) e
              
-- | 'checkNameConstraints' @name pos@ : execute where clause of variable @name@ at position @pos@
checkNameConstraints name pos = do
  cs <- gets $ lookupNameConstraints name
  cs' <- mapM eval cs
  mapM_ extendLogicalConstaints cs'
  
-- | 'checkMapConstraints' @r actuals pos@ : assume all constraints for the value at index @actuals@ 
-- in the map referenced by @r@ mentioned at @pos@
checkMapConstraints r actuals pos = do
  cs <- gets $ lookupMapConstraints r
  cs' <- mapM (\c -> applyMapConstraint c actuals pos) cs  
  mapM_ extendLogicalConstaints cs'
  
-- | 'applyMapConstraint' @c actuals pos@ : 
-- return if @c (actuals)@ holds
-- (@pos@ is the position of the constraint invocation)      
applyMapConstraint c actuals pos = 
  let
    Quantified Lambda tv formals body = node c
    formalNames = map fst formals
    formalTypes = map snd formals
    actualTypes = map thunkType actuals
    locally = executeLocally (\ctx -> ctx { ctxLocals = M.fromList (zip formalNames actualTypes) }) formalNames actuals []    
  in if isNothing $ unifier tv formalTypes actualTypes -- Is the constraint applicable to these types?
    then return $ attachPos pos $ tt
    else locally (eval body)
    
-- | 'solve' @cs@ : apply solver to constraints @cs@
solve :: (Monad m, Functor m) => ConstraintSet -> Execution m Solution
solve cs = do    
  s <- use envSolver
  lift $ lift $ s cs
    
-- | 'solveAll' @cs@ : completely solve constraints @cs@
-- (apply solver until no constraints are left;
-- if any constraint evaluates to false with the current solution, throw an assumption violation)
solveAll :: (Monad m, Functor m) => ConstraintSet -> Execution m ()
solveAll [] = return ()
solveAll constraints = do
  solution <- solve constraints
  envMemory.memLogical %= M.union solution
  newConstraints <- catMaybes <$> mapM checkConstraint constraints
  solveAll newConstraints
  where
    checkConstraint c = do
      res <- eval c
      case node res of
        Literal (BoolValue True) -> return Nothing
        Literal (BoolValue False) -> throwRuntimeFailure (SpecViolation (SpecClause Axiom True c)) (position res)
        _ -> return $ Just res

-- | Solve current logical variable constraints
solveConstraints :: (Monad m, Functor m) => Execution m ()
solveConstraints = do
  constraints <- use $ envConstraints.conLogical
  solveAll constraints
  envConstraints.conLogical .= []
  
-- | 'genIndex' @n@ : return an intereg in [0, n)  
genIndex :: (Monad m, Functor m) => Int -> Execution m Int
genIndex n = if n == 1
  then return 0
  else do
    l <- generateValue IntType noPos
    solveAll [num 0 |<=| l, l |<| num (fromIntegral n)]
    (fromInteger . unValueInt . fromLiteral) <$> eval l
          
{- Preprocessing -}

-- | Collect procedure implementations, and constant/function/global variable constraints
preprocess :: (Monad m, Functor m) => Program -> SafeExecution m ()
preprocess (Program decls) = mapM_ processDecl decls
  where
    processDecl decl = case node decl of
      FunctionDecl name _ args _ mBody -> processFunction name (map fst args) mBody
      ProcedureDecl name _ args rets _ (Just body) -> processProcedureBody name (position decl) (map noWhere args) (map noWhere rets) body
      ImplementationDecl name _ args rets bodies -> mapM_ (processProcedureBody name (position decl) args rets) bodies
      AxiomDecl expr -> extendNameConstaints conGlobals expr
      VarDecl vars -> mapM_ (extendNameConstaints conGlobals) (map itwWhere vars)      
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
      extendNameConstaints conGlobals axiom
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

{- Extracting constraints -}

-- | 'extractMapConstraints' @bExpr@ : extract parametrized constraints from @bExpr@
-- @bExpr@ must not contain any free variables
extractMapConstraints :: Expression -> MapConstraints
extractMapConstraints bExpr = extractConstraints' [] [] [] (negationNF bExpr)

-- | 'extractConstraints'' @tv vars guards body@ : extract parametrized constraints from expression @guards@ ==> @body@
-- with bound type variables @tv@ and bound variables @vars@
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
  _ -> extractConstraintsAtomic
  where
    -- | Bound variables used in body or guards:
    allFreeVars = freeVars body ++ concatMap freeVars guards
    usedVars = [(v, t) | (v, t) <- vars, v `elem` allFreeVars]
    boundTC = emptyContext { ctxTypeVars = tv, ctxLocals = M.fromList vars }
  
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
        then M.singleton x [inheritPos (Quantified Lambda tv (zip formals argTypes)) (guardWith allArgGuards constraint)]
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
       
