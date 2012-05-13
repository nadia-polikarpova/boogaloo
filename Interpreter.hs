{- Interpreter for Boogie 2 -}
module Interpreter where

import AST
import Position
import TypeChecker
import BasicBlocks
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Error
import Control.Applicative

{- Interface -}

-- | Execute program p with entry point main and return the values of global variables;
-- | main must have no arguments
executeProgram :: Program -> Id -> Result (Map Id Value)
executeProgram p main = let initEnv = collectDefinitions emptyEnv p
  in do
    (env', _) <- execProcedure initEnv main []
    return $ envGlobals env'

{- State -}

data Value = IntValue Integer |   -- Integer value
  BoolValue Bool |                -- Boolean value
  MapValue (Map [Value] Value) |  -- Value of a map type
  CustomValue Integer |           -- Value of a user-defined type (values with the same code are considered equal)
  Top                             -- Undefined value
	deriving (Eq, Ord, Show)

data Environment = Environment
  {
    envLocals :: Map Id Value,            -- Local variable names to values
    envGlobals :: Map Id Value,           -- Global variable names to values
    envOld :: Map Id Value,               -- Global variable names to old values (in two-state contexts)
    envConstants :: Map Id (Expression),  -- Constant names to expressions
    envFunctions :: Map Id FDef,          -- Function names to definitions
    envProcedures :: Map Id [PDef]        -- Procedure names to definitions
  } deriving Show
  
emptyEnv = Environment
  {
    envLocals = M.empty,
    envGlobals = M.empty,
    envOld = M.empty,
    envConstants = M.empty,
    envFunctions = M.empty,
    envProcedures = M.empty
  }

-- | Value of id in environment env;
-- | id has to be a name of a variable or constant.
value :: Environment -> Id -> Result Value
value env id = case M.lookup id (envLocals env) of
  Just val -> elimTop val
  Nothing -> case M.lookup id (envGlobals env) of
    Just val -> elimTop val
    Nothing -> case M.lookup id (envConstants env) of
      Just e -> eval env e
      Nothing -> throwError (UndefinedValue ("constant " ++ id))
  where
    elimTop Top = throwError (UndefinedValue ("variable " ++ id))
    elimTop val = return val
    
-- | Assign value val to variable id in environment env;
-- | id has to be already in the domain of env
assign :: Environment -> (Id, Value) -> Environment    
assign env (id, val) = case M.lookup id (envLocals env) of
  Just _ -> env { envLocals = M.insert id val (envLocals env) }
  Nothing -> env { envGlobals = M.insert id val (envGlobals env) }
  
declareGlobal :: Environment -> Id -> Environment
declareGlobal env id = env { envGlobals = M.insert id Top (envGlobals env) }  

declareLocal :: Environment -> Id -> Environment
declareLocal env id = defineLocal env (id, Top)

defineLocal :: Environment -> (Id, Value) -> Environment
defineLocal env (id, val) = env { envLocals = M.insert id val (envLocals env) }  

  
{- Errors -}

data ExecutionError = AssertViolation String | 
  AssumeViolation String |
  DivisionByZero |
  UndefinedValue String |
  UnsupportedConstruct String |
  OtherError String

instance Error ExecutionError where
  noMsg    = OtherError "Unknown error"
  strMsg s = OtherError s

instance Show ExecutionError where
  show (AssertViolation s) = "Assertion violation: " ++ s
  show (AssumeViolation s) = "Assumption violation: " ++ s
  show (DivisionByZero) = "Division by zero"
  show (UndefinedValue s) = "Value of " ++ s ++ " is not defined uniquely"
  show (UnsupportedConstruct s) = "Execution of " ++ s ++ " is not supported yet"
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
                                          Nothing -> throwError (UndefinedValue ("function " ++ id))
                                          Just (FDef formals body) -> do
                                            argsV <- mapM (eval env) args
                                            eval (foldl defineLocal env (zip formals argsV)) body
eval' env (MapSelection m args)       = do 
                                          mV <- eval env m
                                          argsV <- mapM (eval env) args
                                          case mV of 
                                            MapValue map -> case M.lookup argsV map of
                                              Nothing -> throwError (UndefinedValue ("map selection " ++ show (MapSelection m args)))
                                              Just v -> return v
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
exec' env (Havoc ids) = throwError (UnsupportedConstruct "havocs")
exec' env (Assign lhss rhss) = do
  rVals <- mapM (eval env) rhss'
  return $ foldl assign env (zip lhss' rVals)
  where
    lhss' = map fst (zipWith normalize lhss rhss)
    rhss' = map snd (zipWith normalize lhss rhss)
    normalize (id, []) rhs = (id, rhs)
    normalize (id, argss) rhs = (id, mapUpdate (gen $ Var id) argss rhs)
    mapUpdate e [args] rhs = gen $ MapUpdate e args rhs
    mapUpdate e (args1 : argss) rhs = gen $ MapUpdate e args1 (mapUpdate (gen $ MapSelection e args1) argss rhs)
exec' env (Call lhss name args) = do
  argsV <- mapM (eval env) args
  (env', retsV) <- execProcedure env name argsV
  return $ foldl assign env' (zip lhss retsV)
exec' env (CallForall name args) = return env -- ToDo: assert pre, assume post?
  
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

-- | tryOneOf env blocks labels: try executing program starting with blocks labeled with each of labels,
-- | until we find one that does not result in an assumption violation
tryOneOf :: Environment -> Map Id [Statement] -> [Id] -> Result Environment        
tryOneOf env blocks [l] = execBlock env blocks l
tryOneOf env blocks (l:lbs) = case execBlock env blocks l of
  Right env' -> return env'
  Left (AssumeViolation _) -> tryOneOf env blocks lbs
  Left e -> throwError e

-- | Execute procedure name in an environment env with actual arguments actuals 
execProcedure :: Environment -> Id -> [Value] -> Result (Environment, [Value])
execProcedure env name actuals = let 
  procedure = head ((envProcedures env) ! name)
  inEnv = foldl defineLocal env (zip (pdefIns procedure) actuals)
  localEnv = foldl declareLocal inEnv (pdefOuts procedure ++ map itwId (fst (pdefBody procedure)))
  in do
    env' <- execBlock localEnv (snd (pdefBody procedure)) startLabel
    retsV <- mapM (value env') (pdefOuts procedure)
    return (env' { envLocals = envLocals env }, retsV)

{- Preprocessing -}

dummyArg = ""

-- | Collect constant, function and procedure definitions, as well as global variable declarations from p
collectDefinitions :: Environment -> Program -> Environment
collectDefinitions env p = foldl processDecl env (map contents p)
  where
    processDecl env (VarDecl vars) = foldl declareGlobal env (map itwId vars)
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
    formalName Nothing = dummyArg 
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
    
    