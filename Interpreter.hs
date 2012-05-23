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

{- Interface -}

-- | Execute program p with type context tc (produced by the type checker) and entry point main, 
-- | and return the values of global variables;
-- | main must have no arguments
executeProgram :: Program -> TypeContext -> Id -> Result (Map Id Value)
executeProgram p tc main = let initEnv = collectDefinitions emptyEnv { envTypeContext = tc } p
  in case M.lookup main (envProcedures initEnv) of
    Nothing -> throwError (NoEntryPoint main)
    Just (def : defs) -> do
      (env', _) <- execProcedure initEnv main def []
      return $ envGlobals env'

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
  
-- | Value of id in environment env;
-- | id has to be a name of a variable or constant in the type context of env, but does not have to be in the domain of env
value :: Environment -> Id -> Result Value
value env id = case M.lookup id (TC.localScope (envTypeContext env)) of
  Just t -> return $ lookupIn (envLocals env) t
  Nothing -> case M.lookup id (TC.ctxGlobals (envTypeContext env)) of
    Just t -> return $ lookupIn (envGlobals env) t
    Nothing -> case M.lookup id (TC.ctxConstants (envTypeContext env)) of
      Just t -> case M.lookup id (envConstants env) of
        Just e -> eval env e
        Nothing -> return $ defaultValue t
  where
    lookupIn vars t = case M.lookup id vars of
      Just val -> val
      Nothing -> defaultValue t
    
-- | Assign value val to variable id in environment env;
-- | id has to be defined in the type context of env, but does not have to be in the domain of env
assign :: Environment -> Id -> Value -> Environment    
assign env id val = if M.member id (TC.localScope (envTypeContext env))
  then env { envLocals = M.insert id val (envLocals env) }
  else env { envGlobals = M.insert id val (envGlobals env) }

-- | Assign vals to ids  
assignAll :: Environment -> [Id] -> [Value] -> Environment
assignAll env ids vals = foldl (\e (i, v) -> assign e i v) env (zip ids vals)
  
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

-- | Execution result: either 'a' or an error
type Result a = Either ExecutionError a

{- Expressions -}

-- | Semantics of unary operators
-- | They are strict and cannot fail, hence the non-monadic types
unOp :: UnOp -> Value -> Value
unOp Neg (IntValue n)   = IntValue (-n)
unOp Not (BoolValue b)  = BoolValue (not b)

-- | Semantics of binary operators
-- | Some of them are semi-strict and some can fail, hence the monadic types
binOp :: BinOp -> Result Value -> Result Value -> Result Value
binOp And     (Right (BoolValue False)) _ = return $ BoolValue False
binOp Or      (Right (BoolValue True)) _  = return $ BoolValue True
binOp Implies (Right (BoolValue False)) _ = return $ BoolValue True
binOp op (Right v1) (Right v2) = binOpStrict op v1 v2
  where
    binOpStrict Plus    (IntValue n1) (IntValue n2)   = return $ IntValue (n1 + n2)
    binOpStrict Minus   (IntValue n1) (IntValue n2)   = return $ IntValue (n1 - n2)
    binOpStrict Times   (IntValue n1) (IntValue n2)   = return $ IntValue (n1 * n2)
    binOpStrict Div     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                    then throwError DivisionByZero
                                                    else return $ IntValue (n1 `div` n2)
    binOpStrict Mod     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                    then throwError DivisionByZero
                                                    else return (IntValue (n1 `mod` n2))
    binOpStrict Leq     (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 <= n2)
    binOpStrict Ls      (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 < n2)
    binOpStrict Geq     (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 >= n2)
    binOpStrict Gt      (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 > n2)
    binOpStrict And     (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 && b2)
    binOpStrict Or      (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 || b2)
    binOpStrict Implies (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 <= b2)
    binOpStrict Equiv   (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 == b2)
    binOpStrict Eq      v1 v2                         = return $ BoolValue (v1 == v2)
    binOpStrict Neq     v1 v2                         = return $ BoolValue (v1 /= v2)
    binOpStrict Lc      v1 v2                         = throwError (UnsupportedConstruct "orders")
binOp _ (Left e) _ = Left e
binOp _ _ (Left e) = Left e
  
-- | Evaluate an expression in an environment
eval :: Environment -> Expression -> Result Value
eval env e = eval' env (contents e) 

eval' _   TT                          = return $ BoolValue True
eval' _   FF                          = return $ BoolValue False
eval' _   (Numeral n)                 = return $ IntValue n
eval' env (Var id)                    = value env id
eval' env (Application id args)       = case M.lookup id (envFunctions env) of
                                          Nothing -> return $ defaultValue returnType
                                          Just (FDef formals body) -> do
                                            argsV <- mapM (eval env) args
                                            eval (localEnv formals argsV) body
  where
    returnType = fromRight $ TC.checkExpression (envTypeContext env) (gen $ Application id args)
    localEnv formals actuals = assignAll env { envTypeContext = TC.enterFunction (envTypeContext env) id formals args } formals actuals
eval' env (MapSelection m args)       = do 
                                          mV <- eval env m
                                          argsV <- mapM (eval env) args
                                          case mV of 
                                            MapValue map -> case M.lookup argsV map of
                                              Nothing -> return $ defaultValue rangeType
                                              Just v -> return v
  where
    rangeType = fromRight $ TC.checkExpression (envTypeContext env) (gen $ MapSelection m args)
eval' env  (MapUpdate m args new)     = do
                                          mV <- eval env m
                                          argsV <- mapM (eval env) args
                                          newV <- eval env new
                                          case mV of 
                                            MapValue map -> return $ MapValue (M.insert argsV newV map)
eval' env (Old e)                     = eval env { envGlobals = envOld env } e
eval' env (UnaryExpression op e)      = unOp op <$> eval env e
eval' env (BinaryExpression op e1 e2) = binOp op (eval env e1) (eval env e2)                                                
eval' env (Quantified op args vars e) = throwError (UnsupportedConstruct "quantified expressions")

{- Statements -}

-- | Execute a simple statement in an environment
exec :: Environment -> Statement -> Result Environment
exec env stmt = exec' env (contents stmt)

exec' env (Assert e) = do
  b <- eval env e
  case b of 
    BoolValue True -> return env
    BoolValue False -> throwError (AssertViolation (show e))
exec' env (Assume e) = do
  b <- eval env e
  case b of 
    BoolValue True -> return env
    BoolValue False -> throwError (AssumeViolation (show e))
exec' env (Havoc ids) = return $ assignAll env ids (map defaultValue types)
  where
    types = map (fromRight . TC.checkExpression (envTypeContext env) . gen . Var) ids
exec' env (Assign lhss rhss) = do
  rVals <- mapM (eval env) rhss'
  return $ assignAll env lhss' rVals
  where
    lhss' = map fst (zipWith normalize lhss rhss)
    rhss' = map snd (zipWith normalize lhss rhss)
    normalize (id, []) rhs = (id, rhs)
    normalize (id, argss) rhs = (id, mapUpdate (gen $ Var id) argss rhs)
    mapUpdate e [args] rhs = gen $ MapUpdate e args rhs
    mapUpdate e (args1 : argss) rhs = gen $ MapUpdate e args1 (mapUpdate (gen $ MapSelection e args1) argss rhs)
exec' env (Call lhss name args) = case M.lookup name (envProcedures env) of
  Nothing -> return $ assignAll env lhss (map defaultValue returnTypes)
  Just (def : defs) -> do
    (env', retsV) <- execProcedure env name def args
    return $ assignAll env' lhss retsV
  where
    returnTypes = map (fromRight . TC.checkExpression (envTypeContext env) . gen . Var) lhss
exec' env (CallForall name args) = return env -- ToDo: assume pre ==> post?
  
-- | Execute program consisting of blocks starting from the block labeled label in an environment env
execBlock :: Environment -> Map Id [Statement] -> Id -> Result Environment
execBlock env blocks label = let
  block = blocks ! label
  statements = init block
  jump = contents (last block)
  in do
    env' <- foldM exec env statements
    case jump of
      Return -> return env'
      Goto lbs -> tryOneOf env' blocks lbs

-- | tryOneOf env blocks labels: try executing blocks starting with each of labels,
-- | until we find one that does not result in an assumption violation
tryOneOf :: Environment -> Map Id [Statement] -> [Id] -> Result Environment        
tryOneOf env blocks [l] = execBlock env blocks l
tryOneOf env blocks (l:lbs) = case execBlock env blocks l of
  Right env' -> return env'
  Left (AssumeViolation _) -> tryOneOf env blocks lbs
  Left e -> throwError e

-- | Execute definition def of procedure name in an environment env with actual arguments actuals 
execProcedure :: Environment -> Id -> PDef -> [Expression] -> Result (Environment, [Value])
execProcedure env name def args = let 
  ins = pdefIns def
  outs = pdefOuts def
  locals = map noWhere (fst (pdefBody def))
  localEnv argsV = assignAll env { envTypeContext = TC.enterProcedure (envTypeContext env) name ins args outs locals } ins argsV
  in do
    argsV <- mapM (eval env) args
    env' <- execBlock (localEnv argsV) (snd (pdefBody def)) startLabel
    retsV <- mapM (value env') outs
    return (env' { envTypeContext = envTypeContext env, envLocals = envLocals env }, retsV)    

{- Preprocessing -}

-- | Collect constant, function and procedure definitions, as well as global variable declarations from p
collectDefinitions :: Environment -> Program -> Environment
collectDefinitions env p = foldl processDecl env (map contents p)
  where
    processDecl env (FunctionDecl name _ args _ (Just body)) = processFunctionBody env name args body
    processDecl env (ProcedureDecl name _ args rets _ (Just body)) = processProcedureBodies env name (map noWhere args) (map noWhere rets) [body]
    processDecl env (ImplementationDecl name _ args rets bodies) = processProcedureBodies env name args rets bodies
    processDecl env (AxiomDecl expr) = processAxiom env expr
    processDecl env _ = env
      
processFunctionBody env name args body = env 
  { 
    envFunctions = M.insert name (FDef (map (formalName . fst) args) body) (envFunctions env) 
  }     
  where
    formalName Nothing = dummyFArg 
    formalName (Just n) = n

processProcedureBodies env name args rets bodies = env
  {
    envProcedures = M.insert name (oldDefs ++ map (PDef argNames retNames . flatten) bodies) (envProcedures env)
  }
  where
    argNames = map fst args
    retNames = map fst rets
    flatten (locals, statements) = (concat locals, M.fromList (toBasicBlocks statements))
    oldDefs = case M.lookup name (envProcedures env) of
      Nothing -> []
      Just defs -> defs
      
processAxiom env expr = case contents expr of
  -- c == expr: remember expr as a definition for c
  BinaryExpression Eq (Pos _ (Var c)) rhs -> env { envConstants = M.insert c rhs (envConstants env) }
  -- ToDo: add axioms that (partially) define functions
  _ -> env
    
    