{- Interpreter for Boogie 2 -}
module Interpreter where

import AST
import Position
import Message
import qualified TypeChecker as TC
import BasicBlocks
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Error
import Control.Applicative
import Control.Monad.State

{- Interface -}

-- | Execute program p with type context tc (produced by the type checker) and entry point main, 
-- | and return the values of global variables;
-- | main must have no arguments
executeProgram :: Program -> TypeContext -> Id -> Either ExecutionError (Map Id Value)
executeProgram p tc main = envGlobals <$> finalEnvironment
  where
    initEnvironment = emptyEnv { envTypeContext = tc }
    finalEnvironment = case runState (runErrorT programState) initEnvironment of
      (Left err, _) -> Left err
      (_, env)      -> Right env            
    programState = do
      collectDefinitions p
      procedures <- gets envProcedures
      case M.lookup main procedures of
        Nothing -> throwError (NoEntryPoint main)
        Just (def : defs) -> do
          execProcedure main def [] >> return ()
      
{- State -}

data Value = IntValue Integer |   -- Integer value
  BoolValue Bool |                -- Boolean value
  MapValue (Map [Value] Value) |  -- Value of a map type
  CustomValue Integer             -- Value of a user-defined type (values with the same code are considered equal)
  deriving (Eq, Ord, Show)
  
-- | Default value of a type (used to initialize variables)  
defaultValue :: Type -> Value
defaultValue BoolType         = BoolValue False  
defaultValue IntType          = IntValue 0
defaultValue (MapType _ _ _)  = MapValue M.empty
defaultValue (Instance _ _)   = CustomValue 0
  
type TypeContext = TC.Context

data Environment = Environment
  {
    envLocals :: Map Id Value,            -- Local variable names to values
    envGlobals :: Map Id Value,           -- Global variable names to values
    envOld :: Map Id Value,               -- Global variable names to old values (in two-state contexts)
    envConstants :: Map Id (Expression),  -- Constant names to expressions
    envFunctions :: Map Id FDef,          -- Function names to definitions
    envProcedures :: Map Id [PDef],       -- Procedure names to definitions
    envTypeContext :: TypeContext
  } deriving Show
   
emptyEnv = Environment
  {
    envLocals = M.empty,
    envGlobals = M.empty,
    envOld = M.empty,
    envConstants = M.empty,
    envFunctions = M.empty,
    envProcedures = M.empty,
    envTypeContext = TC.emptyContext
  }

setGlobal id val env = env { envGlobals = M.insert id val (envGlobals env) }    
setLocal id val env = env { envLocals = M.insert id val (envLocals env) }
addConstant id def env = env { envConstants = M.insert id def (envConstants env) }
addFunction id def env = env { envFunctions = M.insert id def (envFunctions env) }
addProcedure id def env = env { envProcedures = M.insert id (def : oldDefs) (envProcedures env) } 
  where
    oldDefs = case M.lookup id (envProcedures env) of
      Nothing -> []
      Just defs -> defs

-- | Computations with Environment as state, which can result in either a or ExecutionError  
type Execution a = ErrorT ExecutionError (State Environment) a  

-- | Get value of variable or constant id.
-- | id has to be declared in the current type context. 
-- | In case id does not yet have a value in the current environment, a default value is returned and cached in the environment.
getV :: Id -> Execution Value
getV id = do
  tc <- gets envTypeContext
  case M.lookup id (TC.localScope tc) of
    Just t -> lookup envLocals setLocal t
    Nothing -> case M.lookup id (TC.ctxGlobals tc) of
      Just t -> lookup envGlobals setGlobal t
      Nothing -> case M.lookup id (TC.ctxConstants tc) of
        Just t -> do
          constants <- gets envConstants
          case M.lookup id constants of
            Just e -> eval e
            Nothing -> return $ defaultValue t -- ToDo: cache constant value?
  where
    lookup getter setter t = do
      vars <- gets getter
      case M.lookup id vars of
        Just val -> return val
        Nothing -> do
          modify $ setter id (defaultValue t)
          return $ defaultValue t
        
-- | Set value of variable id to val.
-- | id has to be declared in the current type context.
setV :: Id -> Value -> Execution ()    
setV id val = do
  tc <- gets envTypeContext
  if M.member id (TC.localScope tc)
    then modify $ setLocal id val
    else modify $ setGlobal id val      
    
-- | Set values of variables ids to vals.  
setAll :: [Id] -> [Value] -> Execution ()
setAll ids vals = zipWithM_ setV ids vals  

-- | Enter local scope (apply localTC to the type context, assign actuals to formals, save globals in the old state),
-- | execute computation,
-- | then restore type context, local variables and the old state to their initial values
executeLocally :: (TypeContext -> TypeContext) -> [Id] -> [Value] -> Execution a -> Execution a
executeLocally localTC formals actuals computation = do
  env <- get
  put env { envTypeContext = localTC (envTypeContext env), envOld = envGlobals env }
  setAll formals actuals
  res <- computation
  env' <- get
  put env' { envTypeContext = envTypeContext env, envLocals = envLocals env, envOld = envOld env }
  return res
  
{- Errors -}

data ExecutionError = AssertViolation String | 
  AssumeViolation String |
  DivisionByZero |
  UnsupportedConstruct String |
  NoEntryPoint String |
  OtherError String

instance Error ExecutionError where
  noMsg    = OtherError "Unknown error"
  strMsg s = OtherError s

instance Show ExecutionError where
  show (AssertViolation s) = "Assertion violation: " ++ s
  show (AssumeViolation s) = "Assumption violation: " ++ s
  show (DivisionByZero) = "Division by zero"
  show (UnsupportedConstruct s) = "Execution of " ++ s ++ " is not supported yet"
  show (NoEntryPoint name) = "Cannot find program entry point: " ++ name
  show (OtherError s) = "Unknown error type: " ++ s

{- Expressions -}

-- | Semantics of unary operators
unOp :: UnOp -> Value -> Value
unOp Neg (IntValue n)   = IntValue (-n)
unOp Not (BoolValue b)  = BoolValue (not b)

-- | Semi-strict semantics of binary operators:
-- | binOpLazy op lhs: returns the value of "lhs `op`" if already defined, otherwise Nothing 
binOpLazy :: BinOp -> Value -> Maybe Value
binOpLazy And     (BoolValue False) = Just $ BoolValue False
binOpLazy Or      (BoolValue True)  = Just $ BoolValue True
binOpLazy Implies (BoolValue False) = Just $ BoolValue True
binOpLazy _ _                       = Nothing

-- | Strict semantics of binary operators
binOp :: BinOp -> Value -> Value -> Execution Value 
binOp Plus    (IntValue n1) (IntValue n2)   = return $ IntValue (n1 + n2)
binOp Minus   (IntValue n1) (IntValue n2)   = return $ IntValue (n1 - n2)
binOp Times   (IntValue n1) (IntValue n2)   = return $ IntValue (n1 * n2)
binOp Div     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                then throwError DivisionByZero
                                                else return $ IntValue (n1 `div` n2)
binOp Mod     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                then throwError DivisionByZero
                                                else return (IntValue (n1 `mod` n2))
binOp Leq     (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 <= n2)
binOp Ls      (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 < n2)
binOp Geq     (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 >= n2)
binOp Gt      (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 > n2)
binOp And     (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 && b2)
binOp Or      (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 || b2)
binOp Implies (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 <= b2)
binOp Equiv   (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 == b2)
binOp Eq      v1 v2                         = return $ BoolValue (v1 == v2)
binOp Neq     v1 v2                         = return $ BoolValue (v1 /= v2)
binOp Lc      v1 v2                         = throwError (UnsupportedConstruct "orders")

-- | Evaluate an expression;
-- | can have a side-effect of initializing variables that were not previously defined
eval :: Expression -> Execution Value
eval e = case contents e of
  TT -> return $ BoolValue True
  FF -> return $ BoolValue False
  Numeral n -> return $ IntValue n
  Var id -> getV id
  Application id args -> evalApplication id args
  MapSelection m args -> evalMapSelection m args
  MapUpdate m args new -> evalMapUpdate m args new
  Old e -> evalOld e
  UnaryExpression op e -> unOp op <$> eval e
  BinaryExpression op e1 e2 -> evalBinary op e1 e2
  Quantified op args vars e -> throwError (UnsupportedConstruct "quantified expressions")
  
evalApplication id args = do
  functions <- gets envFunctions
  tc <- gets envTypeContext
  case M.lookup id functions of
    Nothing -> return $ defaultValue (returnType tc)
    Just (FDef formals body) -> do
      argsV <- mapM eval args
      executeLocally (TC.enterFunction id formals args) formals argsV (eval body)
  where
    returnType tc = fromRight $ TC.checkExpression tc (gen $ Application id args)
    
evalMapSelection m args = do 
  tc <- gets envTypeContext
  mV <- eval m
  argsV <- mapM eval args
  case mV of 
    MapValue map -> case M.lookup argsV map of
      Nothing -> return $ defaultValue (rangeType tc)
      Just v -> return v
  where
    rangeType tc = fromRight $ TC.checkExpression tc (gen $ MapSelection m args)
    
evalMapUpdate m args new = do
  mV <- eval m
  argsV <- mapM eval args
  newV <- eval new
  case mV of 
    MapValue map -> return $ MapValue (M.insert argsV newV map)
    
evalOld e = do
  env <- get
  put env { envGlobals = envOld env }
  res <- eval e
  put env
  return res
  
evalBinary op e1 e2 = do
  left <- eval e1
  case binOpLazy op left of
    Just result -> return result
    Nothing -> do
      right <- eval e2
      binOp op left right
  
{- Statements -}

-- | Execute a simple statement
exec :: Statement -> Execution ()
exec stmt = case contents stmt of
  Assert e -> execAssert e
  Assume e -> execAssume e
  Havoc ids -> execHavoc ids
  Assign lhss rhss -> execAssign lhss rhss
  Call lhss name args -> execCall lhss name args
  CallForall name args -> return () -- ToDo: assume pre ==> post?

execAssert e = do
  b <- eval e
  case b of 
    BoolValue True -> return ()
    BoolValue False -> throwError (AssertViolation (show e))
    
execAssume e = do
  b <- eval e
  case b of 
    BoolValue True -> return ()
    BoolValue False -> throwError (AssumeViolation (show e))
    
execHavoc ids = do
  tc <- gets envTypeContext
  setAll ids (map defaultValue (types tc))
  where
    types tc = map (fromRight . TC.checkExpression tc . gen . Var) ids
    
execAssign lhss rhss = do
  rVals <- mapM eval rhss'
  setAll lhss' rVals
  where
    lhss' = map fst (zipWith normalize lhss rhss)
    rhss' = map snd (zipWith normalize lhss rhss)
    normalize (id, []) rhs = (id, rhs)
    normalize (id, argss) rhs = (id, mapUpdate (gen $ Var id) argss rhs)
    mapUpdate e [args] rhs = gen $ MapUpdate e args rhs
    mapUpdate e (args1 : argss) rhs = gen $ MapUpdate e args1 (mapUpdate (gen $ MapSelection e args1) argss rhs)
    
execCall lhss name args = do
  tc <- gets envTypeContext
  procedures <- gets envProcedures
  case M.lookup name procedures of
    Nothing -> setAll lhss (map defaultValue (returnTypes tc))
    Just (def : defs) -> do
      retsV <- execProcedure name def args
      setAll lhss retsV
  where
    returnTypes tc = map (fromRight . TC.checkExpression tc . gen . Var) lhss
    
-- | Execute program consisting of blocks starting from the block labeled label
execBlock :: Map Id [Statement] -> Id -> Execution ()
execBlock blocks label = let
  block = blocks ! label
  statements = init block
  jump = contents (last block)
  in do
    mapM exec statements
    case jump of
      Return -> return ()
      Goto lbs -> tryOneOf blocks lbs
  
-- | tryOneOf blocks labels: try executing blocks starting with each of labels,
-- | until we find one that does not result in an assumption violation      
tryOneOf :: Map Id [Statement] -> [Id] -> Execution ()        
tryOneOf blocks (l : lbs) = catchError (execBlock blocks l) retry
  where
    retry (AssumeViolation _) | not (null lbs) = tryOneOf blocks lbs
    retry e = throwError e
  
-- | Execute definition def of procedure name with actual arguments actuals 
execProcedure :: Id -> PDef -> [Expression] -> Execution [Value]
execProcedure name def args = let 
  ins = pdefIns def
  outs = pdefOuts def
  locals = map noWhere (fst (pdefBody def))
  execBody = do
    execBlock (snd (pdefBody def)) startLabel
    mapM getV outs
  in do
    tc <- gets envTypeContext
    argsV <- mapM eval args
    executeLocally (TC.enterProcedure name ins args outs locals) ins argsV execBody  

{- Preprocessing -}

-- | Collect constant, function and procedure definitions from p
collectDefinitions :: Program -> Execution ()
collectDefinitions p = mapM_ (processDecl . contents) p
  where
    processDecl (FunctionDecl name _ args _ (Just body)) = processFunctionBody name args body
    processDecl (ProcedureDecl name _ args rets _ (Just body)) = processProcedureBody name (map noWhere args) (map noWhere rets) body
    processDecl (ImplementationDecl name _ args rets bodies) = mapM_ (processProcedureBody name args rets) bodies
    processDecl (AxiomDecl expr) = processAxiom expr
    processDecl _ = return ()
      
processFunctionBody name args body = modify $ addFunction name (FDef (map (formalName . fst) args) body) 
  where
    formalName Nothing = dummyFArg 
    formalName (Just n) = n

processProcedureBody name args rets body = modify $ addProcedure name (PDef argNames retNames (flatten body)) 
  where
    argNames = map fst args
    retNames = map fst rets
    flatten (locals, statements) = (concat locals, M.fromList (toBasicBlocks statements))
      
processAxiom expr = case contents expr of
  -- c == expr: remember expr as a definition for c
  BinaryExpression Eq (Pos _ (Var c)) rhs -> modify $ addConstant c rhs
  -- ToDo: add axioms that (partially) define functions
  _ -> return ()
    
    