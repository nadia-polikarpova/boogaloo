{-# LANGUAGE FlexibleContexts #-}

-- | Interpreter for Boogie 2
module Language.Boogie.Interpreter (
  -- * Executing programs
  executeProgramDet,
  executeProgram,
  executeProgramGeneric,
  -- * State
  Value (..),
  Store,
  emptyStore,
  Environment (..),
  initEnv,
  lookupFunction,
  lookupProcedure,
  modifyTypeContext,
  setAnyVar,
  Memory,
  memory,
  debugMemoryDoc,
  userMemoryDoc,
  -- * Executions
  Execution,
  SafeExecution,
  execSafely,
  execUnsafely,
  -- * Run-time failures
  FailureSource (..),
  InternalCode,
  StackFrame (..),
  StackTrace,
  RuntimeFailure (..),  
  FailureKind (..),
  failureKind,
  -- * Execution outcomes
  isPass,
  isInvalid,
  isNonexecutable,
  isFail,
  -- * Executing parts of programs
  eval,
  exec,
  execProcedure,
  collectDefinitions,
  -- * Pretty-printing
  valueDoc,
  storeDoc,
  functionsDoc,
  runtimeFailureDoc
  ) where

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
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Error hiding (join)
import Control.Applicative hiding (empty)
import Control.Monad.State hiding (join)
import Control.Monad.Identity hiding (join)
import Control.Monad.Stream
import Text.PrettyPrint

{- Interface -}

-- | 'executeProgram' @p tc entryPoint@ :
-- Execute program @p@ /non-deterministically/ in type context @tc@ starting from procedure @entryPoint@ 
-- and return an infinite list of possible outcomes (each either runtime failure or the final variable store).
-- Whenever a value is unspecified, all values of the required type are tried exhaustively.
executeProgram :: Program -> Context -> Id -> [Either RuntimeFailure Memory]
executeProgram p tc entryPoint = toList $ executeProgramGeneric p tc exhaustiveGenerator entryPoint

-- | 'executeProgramDet' @p tc entryPoint@ :
-- Execute program @p@ /deterministically/ in type context @tc@ starting from procedure @entryPoint@ 
-- and return a single outcome.
-- Whenever a value is unspecified, a default value of the required type is used.
executeProgramDet :: Program -> Context -> Id -> Either RuntimeFailure Memory
executeProgramDet p tc entryPoint = runIdentity $ executeProgramGeneric p tc defaultGenerator entryPoint
      
-- | 'executeProgramGeneric' @p tc genValue genIndex entryPoint@ :
-- Execute program @p@ in type context @tc@ with input generator @generator@, starting from procedure @entryPoint@,
-- and return the outcome(s) embedded into the generator's monad.
executeProgramGeneric :: (Monad m, Functor m) => Program -> Context -> Generator m -> Id -> m (Either RuntimeFailure Memory)
executeProgramGeneric p tc generator entryPoint = result <$> runStateT (runErrorT programExecution) (initEnv tc generator)
  where
    programExecution = do
      execUnsafely $ collectDefinitions p
      execRootCall entryPoint
    execRootCall name = do
      sig <- procSig name <$> gets envTypeContext
      let params = psigParams sig
      let defaultBinding = M.fromList $ zip (psigTypeVars sig) (repeat defaultType)
      let paramTypes = map (typeSubst defaultBinding) (map itwType params)
      modify $ modifyTypeContext (setLocals (M.fromList $ zip (map itwId params) paramTypes))
      execCallBySig (assumePreconditions sig) (map itwId (psigRets sig)) (map (gen . Var . itwId) (psigArgs sig)) noPos
    defaultType = BoolType      
    result (Left err, _) = Left err
    result (_, env)      = Right $ memory env
    
{- Values -}

-- | Run-time value
data Value = IntValue Integer |               -- ^ Integer value
  BoolValue Bool |                            -- ^ Boolean value
  CustomValue Integer |                       -- ^ Value of a user-defined type (values with the same code are considered equal)
  MapValue (Maybe Ref) (Map [Value] Value) |  -- ^ Value of a map type: consists of an optional reference to the base map (if derived from base by updating) and key-value pairs that override base
  Reference Ref                               -- ^ Reference to a map stored in the heap
  deriving (Eq, Ord)
  
vnot (BoolValue b) = BoolValue (not b)  

-- | Pretty-printed value
valueDoc :: Value -> Doc
valueDoc (IntValue n) = integer n
valueDoc (BoolValue False) = text "false"
valueDoc (BoolValue True) = text "true"
valueDoc (MapValue mR m) = optionMaybe mR refDoc <> 
  brackets (commaSep (map itemDoc (M.toList m)))
  where itemDoc (keys, v) = commaSep (map valueDoc keys) <+> text "->" <+>  valueDoc v
valueDoc (CustomValue n) = text "custom_" <> integer n
valueDoc (Reference r) = refDoc r

instance Show Value where
  show v = show (valueDoc v)

{- Execution state -}  

-- | Store: stores variable values at runtime 
type Store = Map Id Value

-- | A store with no variables
emptyStore :: Store
emptyStore = M.empty

-- | Pretty-printed store
storeDoc :: Store -> Doc
storeDoc vars = vsep $ map varDoc (M.toList vars)
  where varDoc (id, val) = text id <+> text "=" <+> valueDoc val
  
-- | 'deepDeref' @h v@: Completely dereference value @v@ given heap @h@ (so that no references are left in @v@)
deepDeref :: Heap Value -> Value -> Value
deepDeref h v = deepDeref' v
  where
    deepDeref' (Reference r) = deepDeref' (h `at` r)
    deepDeref' (MapValue mR m) = let
      unValue (MapValue Nothing m) = m
      base = case mR of
        Nothing -> M.empty
        Just r -> unValue $ deepDeref' (Reference r)
      override = (M.map deepDeref' . M.mapKeys (map deepDeref')) m -- Here we do not assume that keys contain no references, as this is used for error reporting
      in MapValue Nothing $ M.union override base
    deepDeref' v = v  

-- | 'objectEq' @h v1 v2@: is @v1@ equal to @v2@ in the Boogie semantics? Nothing if cannot be determined.
objectEq :: Heap Value -> Value -> Value -> Maybe Bool
objectEq h (Reference r1) (Reference r2) = if r1 == r2
  then Just True -- Equal references point to equal maps
  else let 
    (br1, over1) = baseOverride r1
    (br2, over2) = baseOverride r2
    in if mustDisagree h over1 over2
      then Just False -- Must disagree on some indexes, cannot be equal  
      else if br1 == br2 && mustAgree h over1 over2
        then Just True -- Derived from the same base map and must agree on all overridden indexes, must be equal
        else Nothing -- Derived from different base maps or may disagree on some overridden indexes, no conclusion        
  where
    baseOverride r = let (MapValue mBase m) = h `at` r in
      case mBase of
        Nothing -> (r, M.empty)
        Just base -> (base, m)
    mustDisagree h m1 m2 = M.foldl (||) False $ (M.intersectionWith (mustNeq h) m1 m2)
    mustAgree h m1 m2 = let common = M.intersectionWith (mustEq h) m1 m2 in
      M.size m1 == M.size common && M.size m2 == M.size common && M.foldl (&&) True common
objectEq _ (MapValue base1 m1) (MapValue base2 m2) = internalError "Attempt to compare two maps"
objectEq _ v1 v2 = Just $ v1 == v2

mustEq h v1 v2 = case objectEq h v1 v2 of
  Just True -> True
  _ -> False  
mustNeq h v1 v2 = case objectEq h v1 v2 of
  Just False -> True
  _ -> False  
mayEq h v1 v2 = not $ mustNeq h v1 v2
mayNeq h v1 v2 = not $ mustEq h v1 v2

-- | 'functionCacheName' @name@ : name of a constant that stores cached applications of function @name@
functionCacheName name = name ++ (nonIdChar : "cache")

-- | 'isAuxName' @name@ : is @name@ and auxiliary variable/constant introduced by the inetrpreter?
isAuxName name = nonIdChar `elem` name
  
-- | Execution state
data Environment m = Environment
  {
    -- | Store
    envLocals :: Store,                          -- ^ Local variable store
    envGlobals :: Store,                         -- ^ Global variable store
    envOld :: Store,                             -- ^ Old global variable store (in two-state contexts)
    -- | Heap (used for lazy initialization of maps)
    envHeap :: Heap Value,                       -- ^ Heap
    -- | Static information
    envConstDefs :: Map Id Expression,           -- ^ Constant names to definitions
    envConstConstraints :: Map Id [Expression],  -- ^ Constant names to constraints
    envFunctions :: Map Id [FDef],               -- ^ Function names to definitions
    envProcedures :: Map Id [PDef],              -- ^ Procedure names to definitions
    envTypeContext :: Context,                   -- ^ Type context
    envGenerator :: Generator m,                 -- ^ Input generator (used for non-deterministic choices)
    -- | Scope information
    envInOld :: Bool                             -- ^ Is an old expression currently being evaluated?
  }
   
-- | 'initEnv' @tc gen@: Initial environment in a type context @tc@ with a value generator @gen@  
initEnv tc gen = Environment
  {
    envLocals = emptyStore,
    envGlobals = emptyStore,
    envOld = emptyStore,
    envHeap = emptyHeap,
    envConstDefs = M.empty,
    envConstConstraints = M.empty,
    envFunctions = M.empty,
    envProcedures = M.empty,
    envTypeContext = tc,
    envGenerator = gen,
    envInOld = False
  }

-- | 'lookupConstConstraints' @id env@ : All constraints of constant @id@ in @env@
lookupConstConstraints id env = case M.lookup id (envConstConstraints env) of
  Nothing -> []
  Just cs -> cs
  
-- | 'lookupFunction' @id env@ : All definitions of function @id@ in @env@
lookupFunction id env = case M.lookup id (envFunctions env) of
  Nothing -> []
  Just defs -> defs    
  
-- | 'lookupProcedure' @id env@ : All definitions of procedure @id@ in @env@  
lookupProcedure id env = case M.lookup id (envProcedures env) of
  Nothing -> []
  Just defs -> defs 

-- Environment modifications  
setGlobal id val env = env { envGlobals = M.insert id val (envGlobals env) }
setLocal id val env = env { envLocals = M.insert id val (envLocals env) }
setOld id val env = env { envOld = M.insert id val (envOld env) }    
addConstantDef id def env = env { envConstDefs = M.insert id def (envConstDefs env) }
addConstantConstraint id expr env = env { envConstConstraints = M.insert id (lookupConstConstraints id env ++ [expr]) (envConstConstraints env) }
addFunctionDefs id defs env = env { envFunctions = M.insert id (lookupFunction id env ++ defs) (envFunctions env) }
addProcedureDef id def env = env { envProcedures = M.insert id (lookupProcedure id env ++ [def]) (envProcedures env) } 
modifyTypeContext f env = env { envTypeContext = f (envTypeContext env) }
withHeap f env = let (res, h') = f (envHeap env) in (res, env { envHeap = h' })  
withHeap_ f env = env { envHeap = f (envHeap env) }  

-- | Pretty-printed set of function definitions
functionsDoc :: Map Id [FDef] -> Doc  
functionsDoc funcs = vsep $ map funcDoc (M.toList funcs)
  where 
    funcDoc (id, defs) = vsep $ map (funcsDefDoc id) defs
    funcsDefDoc id (FDef formals guard body) = exprDoc guard <+> text "->" <+> 
      text id <> parens (commaSep (map text formals)) <+> text "=" <+> exprDoc body
      
-- | View of the environment that contains information relevant to the user
data Memory = Memory Store (Heap Value)

-- | Memory state of an environment
memory :: Environment m -> Memory
memory env = Memory (envLocals env `M.union` envGlobals env `M.union` M.mapKeys oldName (envOld env)) (envHeap env)
  where
    oldName var = var ++ (nonIdChar : "old")

-- | Empty memory
emptyMemory = Memory emptyStore emptyHeap

-- | 'debugMemoryDoc' @mem@ : implementation-specific representation of @mem@
debugMemoryDoc :: Memory -> Doc
debugMemoryDoc (Memory store heap) = storeDoc store $+$ heapDoc heap

-- | 'userMemoryDoc' @mem isRelevant@ : representation of @mem@ on the abstraction level of the Boogie semantics,
-- restricted to variables that satisfy @isRelevant@
userMemoryDoc :: Memory -> (Id -> Bool) -> Doc
userMemoryDoc (Memory store heap) isRelevant = storeDoc $ flatten filtered
  where
    filtered = M.filterWithKey (\k _ -> not (isAuxName k) && isRelevant k) store
    flatten s = M.map (deepDeref heap) s
    
instance Show Memory where
  show mem = show $ debugMemoryDoc mem
            
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
  env <- get
  put env { envGlobals = envOld env, envInOld = True }
  res <- execution
  modify $ \env' -> env' { envOld = envGlobals env', envGlobals = envGlobals env `M.union` envGlobals env', envInOld = envInOld env } -- Include freshly initialized globals into both old and new states
  return res

-- | Save current values of global variables in the "old" environment, return the previous "old" environment
saveOld :: (Monad m, Functor m) => Execution m (Environment m)  
saveOld = do
  env <- get
  let globals = envGlobals env  
  put env { envOld = globals }
  mapM_ incRefCountValue (M.elems globals) -- Each value stored in globals is now pointed by an additional (old) variable
  return $ env

-- | Set the "old" environment to olds  
restoreOld :: (Monad m, Functor m) => Environment m -> Execution m ()  
restoreOld env = do
  env' <- get
  let (oldOlds, newOlds) = M.partitionWithKey (\var _ -> M.member var (envGlobals env)) (envOld env')  
  put env' { envOld = envOld env `M.union` newOlds } -- Add old values for freshly initialized globals (they are valid up until the program entry point, so could be accessed until the end of the program)
  mapM_ decRefCountValue (M.elems oldOlds) -- Old values for previously initialized varibles go out of scope
  
-- | Enter local scope (apply localTC to the type context and assign actuals to formals),
-- execute computation,
-- then restore type context and local variables to their initial values
executeLocally :: (MonadState (Environment m) s, Finalizer s) => (Context -> Context) -> [Id] -> [Id] -> [Value] -> s a -> s a
executeLocally localTC locals formals actuals computation = do
  oldEnv <- get
  modify $ modifyTypeContext localTC
  modify $ \env -> env { envLocals = deleteAll locals (envLocals env) }
  zipWithM_ (setVar (const emptyStore) setLocal) formals actuals -- All formals are fresh, can use emptyStore for current values
  computation `finally` unwind oldEnv
  where
    -- | Restore type context and the values of local variables 
    unwind oldEnv = do
      mapM_ (unsetVar envLocals) locals
      modify $ \env -> env { envTypeContext = envTypeContext oldEnv, envLocals = deleteAll locals (envLocals env) `M.union` envLocals oldEnv }
                              
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
  callPos :: SourcePos, -- ^ Source code position of the call
  callName :: Id        -- ^ Name of procedure or function
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
  mem <- gets memory
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
runtimeFailureDoc err = failureSourceDoc (rtfSource err) <+> posDoc (rtfPos err) $+$
  userMemoryDoc (rtfMemory err) isRelevant $+$
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
  show err = show (runtimeFailureDoc err)
  
-- | Internal error codes 
data InternalCode = NotLinear
  deriving Eq

throwInternalException code = throwRuntimeFailure (InternalException code) noPos

{- Execution outcomes -}

-- | 'isPass' @outcome@: Does @outcome@ belong to a passing execution? (Denotes a valid final state)
isPass :: Either RuntimeFailure Memory -> Bool
isPass (Right _) =  True
isPass _ =          False

-- | 'isInvalid' @outcome@: Does @outcome@ belong to an invalid execution? (Denotes an unreachable state)
isInvalid :: Either RuntimeFailure Memory -> Bool 
isInvalid (Left err)
  | failureKind err == Unreachable = True
isInvalid _                        = False

-- | 'isNonexecutable' @outcome@: Does @outcome@ belong to an execution that cannot be carried out completely by the interpreter? (Denotes a non-executable state)
isNonexecutable :: Either RuntimeFailure Memory -> Bool 
isNonexecutable (Left err)
  | failureKind err == Nonexecutable  = True
isNonexecutable _                     = False

-- | 'isFail' @outcome@: Does @outcome@ belong to a failing execution? (Denotes an error state)
isFail :: Either RuntimeFailure Memory -> Bool
isFail outcome = not (isPass outcome || isInvalid outcome || isNonexecutable outcome)

{- Basic executions -}      

-- | 'generate' @f@ : computation that extracts @f@ from the generator
generate :: (Monad m, Functor m) => (Generator m -> m a) -> Execution m a
generate f = do    
  gen <- gets envGenerator
  lift (lift (f gen))
      
-- | 'generateValue' @t pos@ : choose a value of type @t@ at source position @pos@;
-- fail if @t@ is a type variable
generateValue :: (Monad m, Functor m) => Type -> SourcePos -> Execution m Value
generateValue t pos = case t of
    IdType x [] | isTypeVar [] x -> throwRuntimeFailure (UnsupportedConstruct ("choice of a value from unknown type " ++ show t)) pos
    -- | Maps are initializaed lazily, allocate an empty map on the heap:
    MapType _ _ _ -> allocate $ MapValue Nothing M.empty
    BoolType -> BoolValue <$> generate genBool
    IntType -> IntValue <$> generate genInteger
    IdType _ _ -> CustomValue <$> generate genInteger
        
-- | 'incRefCountValue' @val@ : if @val@ is a reference, increase its count
incRefCountValue val = case val of
  Reference r -> modify . withHeap_ $ incRefCount r
  _ -> return ()    

-- | 'decRefCountValue' @val@ : if @val@ is a reference, decrease its count  
decRefCountValue val = case val of
  Reference r -> modify . withHeap_ $ decRefCount r
  _ -> return ()     
    
-- | 'unsetVar' @getStore id@ : if @id@ was associated with a reference in @getStore@, decrease its reference count
unsetVar getStore id = do
  store <- gets $ getStore
  case M.lookup id store of    
    Just (Reference r) -> do          
      modify . withHeap_ $ decRefCount r
    _ -> return ()

-- | 'setVar' @getStore setter id val@ : set value of variable @id@ to @val@ using @setter@;
-- adjust reference count if needed using @getStore@ to access the current value of @id@  
setVar getStore setter id val = do
  case val of
    Reference r -> do
      unsetVar getStore id
      modify . withHeap_ $ incRefCount r
    _ -> return ()
  modify $ setter id val    
          
-- | 'setAnyVar' @id val@ : set value of global or local variable @id@ to @val@
setAnyVar id val = do
  tc <- gets envTypeContext
  if M.member id (localScope tc)
    then setVar envLocals setLocal id val
    else setVar envGlobals setGlobal id val

-- | 'readHeap' @r@: current value of reference @r@ in the heap
readHeap r = flip at r <$> gets envHeap
    
-- | 'allocate' @v@: store @v@ at a fresh location in the heap and return that location
allocate :: (Monad m, Functor m) => Value -> Execution m Value
allocate v = Reference <$> (state . withHeap . alloc) v
  
-- | Remove all unused references from the heap  
collectGarbage :: (Monad m, Functor m) => Execution m ()  
collectGarbage = do
  h <- gets envHeap
  when (hasGarbage h) (do
    MapValue mBase over <- state $ withHeap dealloc
    case mBase of
      Nothing -> return ()
      Just base -> modify . withHeap_ $ decRefCount base
    mapM_ decElem (M.elems over)
    collectGarbage)
  where
    decElem v = case v of
      Reference r -> modify . withHeap_ $ decRefCount r
      _ -> return ()    

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
binOp pos Eq      v1 v2                         = do
                                                    h <- gets envHeap
                                                    case objectEq h v1 v2 of
                                                      Just b -> return $ BoolValue b
                                                      Nothing -> throwRuntimeFailure (MapEquality (deepDeref h v1) (deepDeref h v2)) pos 
binOp pos Neq     v1 v2                         = vnot <$> binOp pos Eq v1 v2
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
  Var id -> evalVar id (position expr)
  Application id args -> evalApplication id args (position expr)
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
  
evalVar id pos = do
  tc <- gets envTypeContext
  case M.lookup id (localScope tc) of
    Just t -> lookupStore envLocals (init (generateValue t pos) [setLocal] checkWhere)
    Nothing -> case M.lookup id (ctxGlobals tc) of
      Just t -> do
        inOld <- gets envInOld
        let setters = if inOld then [setGlobal] else [setGlobal, setOld]
        lookupStore envGlobals (init (generateValue t pos) setters checkWhere)
      Nothing -> case M.lookup id (ctxConstants tc) of
        Just t -> lookupStore envGlobals (initConst t)
        Nothing -> (internalError . show) (text "Encountered unknown identifier during execution:" <+> text id) 
  where
    -- | Initialize @id@ with a value geberated by @gen@, and then perform @check@
    init gen sets check = do
      val <- gen
      mapM_ (\set -> setVar (const emptyStore) set id val) sets
      check id pos
      return val
    -- | Lookup @id@ in @store@; if occurs return its stored value, otherwise @calculate@
    lookupStore store calculate = do
      s <- gets store
      case M.lookup id s of
        Just val -> return val
        Nothing -> calculate
    -- | Initialize constant @id@ of type @t@ using its defininition, if present, and otherwise non-deterministically
    initConst t = do
      constants <- gets envConstDefs
      case M.lookup id constants of
        Just e -> init (eval e) [setGlobal] checkConstConstraints
        Nothing -> init (generateValue t pos) [setGlobal] checkConstConstraints
  
evalApplication name args pos = do
  defs <- gets (lookupFunction name)  
  evalDefs defs
  where
    -- | If the guard of one of function definitions evaluates to true, apply that definition; otherwise treat an an undefined constant map
    evalDefs :: (Monad m, Functor m) => [FDef] -> Execution m Value
    evalDefs [] = do
      sig <- funSig name <$> gets envTypeContext
      let mapName = functionCacheName name
      modify $ modifyTypeContext (\tc -> tc { ctxConstants = M.insert mapName (fsigType sig) (ctxConstants tc) })
      evalMapSelection ((gen . Var) mapName) args pos
    evalDefs (FDef formals guard body : defs) = do
      argsV <- mapM eval args
      applicable <- evalLocally formals argsV guard `catchError` addStackFrame frame
      case applicable of
        BoolValue True -> evalLocally formals argsV body `catchError` addStackFrame frame 
        BoolValue False -> evalDefs defs
    evalLocally formals actuals expr = do
      sig <- funSig name <$> gets envTypeContext
      executeLocally (enterFunction sig formals args) formals formals actuals (eval expr)
    returnType tc = exprType tc (gen $ Application name args)
    frame = StackFrame pos name
    
rejectMapIndex pos idx = case idx of
  Reference r -> throwRuntimeFailure (UnsupportedConstruct "map as an index") pos
  _ -> return ()    
    
evalMapSelection m args pos = do   
  Reference r <- eval m  
  argsV <- mapM eval args
  mapM_ (rejectMapIndex pos) argsV
  h <- gets envHeap  
  case lookupHeap h argsV r of
    Left v -> return v
    Right baseRef -> do
      tc <- gets envTypeContext
      let rangeType = exprType tc (gen $ MapSelection m args)
      val <- generateValue rangeType pos
      -- ToDo: where and axiom checks
      -- case mapVariable tc (node m) of
        -- Nothing -> return val -- The underlying map comes from a constant or function, nothing to check
        -- Just v -> checkWhere v pos >> return val -- The underlying map comes from a variable: check the where clause
      incRefCountValue val
      MapValue Nothing baseMap <- readHeap baseRef
      modify . withHeap_ $ update baseRef (MapValue Nothing (M.insert argsV val baseMap))
      return val    
  where
    lookupHeap :: Heap Value -> [Value] -> Ref -> Either Value Ref
    lookupHeap h argsV r = let MapValue mBase map = h `at` r in
      case M.lookup argsV map of
        Just v -> Left v
        Nothing -> case mBase of
          Nothing -> Right r
          Just baseRef -> lookupHeap h argsV baseRef
    mapVariable tc (Var v) = if M.member v (allVars tc)
      then Just v
      else Nothing
    mapVariable tc (MapUpdate m _ _) = mapVariable tc (node m)
    mapVariable tc _ = Nothing
        
evalMapUpdate m args new pos = do
  Reference r <- eval m
  MapValue mBase o <- readHeap r
  argsV <- mapM eval args
  mapM_ (rejectMapIndex pos) argsV
  newV <- eval new
  incRefCountValue newV
  let (base, over) = case mBase of Nothing -> (r, M.singleton argsV newV); Just b -> (b, M.insert argsV newV o)
  modify . withHeap_ $ incRefCount base
  allocate $ MapValue (Just base) over
  
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
evalExists tv vars e pos = do
  tc <- gets envTypeContext
  case node $ normalize tc (attachPos pos $ Quantified Exists tv vars e) of
    Quantified Exists tv' vars' e' -> evalExists' tv' vars' e'

evalExists' :: (Monad m, Functor m) => [Id] -> [IdType] -> Expression -> Execution m Value    
evalExists' tv vars e = do
  results <- executeLocally (enterQuantified tv vars) (map fst vars) [] [] evalWithDomains
  return $ BoolValue (any isTrue results)
  where
    evalWithDomains = do
      doms <- domains e varNames
      evalForEach varNames doms
    -- | evalForEach vars domains: evaluate e for each combination of possible values of vars, drown from respective domains
    evalForEach :: (Monad m, Functor m) => [Id] -> [Domain] -> Execution m [Value]
    evalForEach [] [] = replicate 1 <$> eval e
    evalForEach (var : vars) (dom : doms) = concat <$> forM dom (fixOne vars doms var)
    -- | Fix the value of var to val, then evaluate e for each combination of values for the rest of vars
    fixOne :: (Monad m, Functor m) => [Id] -> [Domain] -> Id -> Value -> Execution m [Value]
    fixOne vars doms var val = do
      setVar envLocals setLocal var val
      evalForEach vars doms
    isTrue (BoolValue b) = b
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
    
execHavoc ids pos = do
  tc <- gets envTypeContext
  mapM_ (havoc tc) ids 
  where
    havoc tc id = do
      val <- generateValue (exprType tc . gen . Var $ id) pos
      setAnyVar id val
      checkWhere id pos      
    
execAssign lhss rhss = do
  rVals <- mapM eval rhss'
  zipWithM_ setAnyVar lhss' rVals
  where
    lhss' = map fst (zipWith simplifyLeft lhss rhss)
    rhss' = map snd (zipWith simplifyLeft lhss rhss)
    simplifyLeft (id, []) rhs = (id, rhs)
    simplifyLeft (id, argss) rhs = (id, mapUpdate (gen $ Var id) argss rhs)
    mapUpdate e [args] rhs = gen $ MapUpdate e args rhs
    mapUpdate e (args1 : argss) rhs = gen $ MapUpdate e args1 (mapUpdate (gen $ MapSelection e args1) argss rhs)
    
execCall name lhss args pos = do
  sig <- procSig name <$> gets envTypeContext
  execCallBySig sig lhss args pos
    
execCallBySig sig lhss args pos = do
  defs <- gets $ lookupProcedure (psigName sig)
  (sig', def) <- selectDef sig defs
  lhssExpr <- (\tc -> map (attachPos (ctxPos tc) . Var) lhss) <$> gets envTypeContext
  retsV <- execProcedure sig' def args lhssExpr `catchError` addStackFrame frame
  zipWithM_ setAnyVar lhss retsV
  where
    selectDef sig [] = return (assumePostconditions sig, dummyDef sig)
    selectDef sig defs = do
      i <- generate (`genIndex` length defs)
      return (sig, defs !! i)
    -- For procedures with no implementation: dummy definition that just havocs all modifiable globals
    dummyDef sig = PDef {
        pdefIns = map itwId (psigArgs sig),
        pdefOuts = map itwId (psigRets sig),
        pdefParamsRenamed = False,
        pdefBody = ([], (M.fromList . toBasicBlocks . singletonBlock . gen . Havoc . psigModifies) sig),
        pdefPos = noPos
      }  
    frame = StackFrame pos (psigName sig)
        
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
  exitPoint pos = if pos == noPos 
    then pdefPos def  -- Fall off the procedure body: take the procedure definition location
    else pos          -- A return statement inside the body
  execBody = do
    checkPreconditions sig def
    env <- saveOld
    pos <- exitPoint <$> execBlock blocks startLabel
    checkPostonditions sig def pos
    restoreOld env
    mapM (eval . attachPos (pdefPos def) . Var) outs
  in do
    argsV <- mapM eval args
    executeLocally (enterProcedure sig def args lhss) (pdefLocals def) ins argsV execBody
    
{- Specs -}

-- | Assert preconditions of definition def of procedure sig
checkPreconditions sig def = mapM_ (exec . attachPos (pdefPos def) . Predicate . subst sig) (psigRequires sig)
  where 
    subst sig (SpecClause t f e) = SpecClause t f (paramSubst sig def e)

-- | Assert postconditions of definition def of procedure sig at exitPoint    
checkPostonditions sig def exitPoint = mapM_ (exec . attachPos exitPoint . Predicate . subst sig) (psigEnsures sig)
  where 
    subst sig (SpecClause t f e) = SpecClause t f (paramSubst sig def e)

-- | 'checkConstConstraints' @id pos@: Assume constraining axioms of constant @id@ at a program location @pos@
-- (pos will be reported as the location of the failure instead of the location of the variable definition).    
checkConstConstraints id pos = do
  constraints <- gets $ lookupConstConstraints id
  mapM_ (exec . attachPos pos . Predicate . SpecClause Axiom True) constraints

-- | 'checkWhere' @id pos@: Assume where clause of variable @id@ at a program location pos
-- (pos will be reported as the location of the failure instead of the location of the variable definition).
checkWhere id pos = do
  whereClauses <- ctxWhere <$> gets envTypeContext
  case M.lookup id whereClauses of
    Nothing -> return ()
    Just w -> (exec . attachPos pos . Predicate . SpecClause Where True) w

{- Preprocessing -}

-- | Collect constant, function and procedure definitions from the program
collectDefinitions :: (Monad m, Functor m) => Program -> SafeExecution m ()
collectDefinitions (Program decls) = mapM_ processDecl decls
  where
    processDecl (Pos _ (FunctionDecl name _ args _ (Just body))) = processFunctionBody name args body
    processDecl (Pos pos (ProcedureDecl name _ args rets _ (Just body))) = processProcedureBody name pos (map noWhere args) (map noWhere rets) body
    processDecl (Pos pos (ImplementationDecl name _ args rets bodies)) = mapM_ (processProcedureBody name pos args rets) bodies
    processDecl (Pos _ (AxiomDecl expr)) = processAxiom expr
    processDecl _ = return ()
  
processFunctionBody name args body = let
  formals = map (formalName . fst) args
  guard = gen TT
  in
    modify $ addFunctionDefs name [FDef formals guard body]
  where
    formalName Nothing = dummyFArg 
    formalName (Just n) = n    
    
processProcedureBody name pos args rets body = do
  sig <- procSig name <$> gets envTypeContext
  modify $ addProcedureDef name (PDef argNames retNames (paramsRenamed sig) (flatten body) pos) 
  where
    argNames = map fst args
    retNames = map fst rets
    flatten (locals, statements) = (concat locals, M.fromList (toBasicBlocks statements))
    paramsRenamed sig = map itwId (psigParams sig) /= (argNames ++ retNames)     

processAxiom expr = do
  extractConstantConstraints expr
  extractFunctionDefs expr []
  
{- Constant and function definitions -}

-- | Extract constant definitions and constraints from a boolean expression bExpr
extractConstantConstraints :: (Monad m, Functor m) => Expression -> SafeExecution m ()
extractConstantConstraints bExpr = case node bExpr of  
  BinaryExpression Eq (Pos _ (Var c)) rhs -> modify $ addConstantDef c rhs    -- c == rhs: remember rhs as a definition for c
  _ -> mapM_ (\c -> modify $ addConstantConstraint c bExpr) (freeVars bExpr)  -- otherwise: remember bExpr as a constraint for all its free variables

-- | Extract function definitions from a boolean expression bExpr, using guards extracted from the exclosing expression.
-- bExpr of the form "(forall x :: P(x, c) ==> f(x, c) == rhs(x, c) && B) && A",
-- with zero or more bound variables x and zero or more constants c,
-- produces a definition "f(x, x') = rhs(x, x')" with a guard "P(x) && x' == c"
extractFunctionDefs :: (Monad m, Functor m) => Expression -> [Expression] -> SafeExecution m ()
extractFunctionDefs bExpr guards = extractFunctionDefs' (node bExpr) guards

extractFunctionDefs' (BinaryExpression Eq (Pos _ (Application f args)) rhs) outerGuards = do
  c <- gets envTypeContext
  -- Only possible if each argument is either a variables or does not involve variables and there are no extra variables in rhs:
  if all (simple c) args && closedRhs c
    then do    
      let (formals, guards) = unzip (extractArgs c)
      let allGuards = concat guards ++ outerGuards
      let guard = if null allGuards then gen TT else foldl1 (|&|) allGuards
      modify $ addFunctionDefs f [FDef formals guard rhs]
    else return ()
  where
    simple _ (Pos p (Var _)) = True
    simple c e = null $ freeVars e `intersect` M.keys (ctxIns c)
    closedRhs c = null $ (freeVars rhs \\ concatMap freeVars args) `intersect` M.keys (ctxIns c)
    extractArgs c = zipWith (extractArg c) args [0..]
    -- | Formal argument name and guards extracted from an actual argument at position i
    extractArg :: Context -> Expression -> Integer -> (String, [Expression])
    extractArg c (Pos p e) i = let 
      x = freshArgName i 
      xExpr = attachPos p $ Var x
      in 
        case e of
          Var arg -> if arg `M.member` ctxIns c 
            then (arg, []) -- Bound variable of the enclosing quantifier: use variable name as formal, no additional guards
            else (x, [xExpr |=| Pos p e]) -- Constant: use fresh variable as formal (will only appear in the guard), add equality guard
          _ -> (x, [xExpr |=| Pos p e])
    freshArgName i = f ++ (nonIdChar : show i)
extractFunctionDefs' (BinaryExpression Implies cond bExpr) outerGuards = extractFunctionDefs bExpr (cond : outerGuards)
extractFunctionDefs' (BinaryExpression And bExpr1 bExpr2) outerGuards = do
  extractFunctionDefs bExpr1 outerGuards
  extractFunctionDefs bExpr2 outerGuards
extractFunctionDefs' (Quantified Forall tv vars bExpr) outerGuards = executeLocally (enterQuantified tv vars) (map fst vars) [] [] (extractFunctionDefs bExpr outerGuards)
extractFunctionDefs' _ _ = return ()
   
{- Quantification -}

-- | Sets of interval constraints on integer variables
type Constraints = Map Id Interval
            
-- | The set of domains for each variable in vars, outside which boolean expression boolExpr is always false.
-- Fails if any of the domains are infinite or cannot be found.
domains :: (Monad m, Functor m) => Expression -> [Id] -> Execution m [Domain]
domains boolExpr vars = do
  initC <- foldM initConstraints M.empty vars
  finalC <- inferConstraints boolExpr initC 
  forM vars (domain finalC)
  where
    initConstraints c var = do
      tc <- gets envTypeContext
      case M.lookup var (allVars tc) of
        Just BoolType -> return c
        Just IntType -> return $ M.insert var top c
        _ -> throwRuntimeFailure (UnsupportedConstruct "quantification over a map or user-defined type") (position boolExpr)
    domain c var = do
      tc <- gets envTypeContext
      case M.lookup var (allVars tc) of
        Just BoolType -> return $ map BoolValue [True, False]
        Just IntType -> do
          case c ! var of
            int | isBottom int -> return []
            Interval (Finite l) (Finite u) -> return $ map IntValue [l..u]
            int -> throwRuntimeFailure (InfiniteDomain var int) (position boolExpr)

-- | Starting from initial constraints, refine them with the information from boolExpr,
-- until fixpoint is reached or the domain for one of the variables is empty.
-- This function terminates because the interval for each variable can only become smaller with each iteration.
inferConstraints :: (Monad m, Functor m) => Expression -> Constraints -> Execution m Constraints
inferConstraints boolExpr constraints = do
  constraints' <- foldM refineVar constraints (M.keys constraints)
  if bot `elem` M.elems constraints'
    then return $ M.map (const bot) constraints'  -- if boolExpr does not have a satisfying assignment to one variable, then it has none to all variables
    else if constraints == constraints'
      then return constraints'                    -- if a fixpoint is reached, return it
      else inferConstraints boolExpr constraints' -- otherwise do another iteration
  where
    refineVar :: (Monad m, Functor m) => Constraints -> Id -> Execution m Constraints
    refineVar c id = do
      int <- inferInterval boolExpr c id
      return $ M.insert id (meet (c ! id) int) c 

-- | Infer an interval for variable x, outside which boolean expression booExpr is always false, 
-- assuming all other quantified variables satisfy constraints;
-- boolExpr has to be in negation-prenex normal form.
inferInterval :: (Monad m, Functor m) => Expression -> Constraints -> Id -> Execution m Interval
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
toLinearForm :: (Monad m, Functor m) => Expression -> Constraints -> Id -> Execution m LinearForm
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
  