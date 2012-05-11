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

{- State -}

data Value = IntValue Integer |   -- Integer value
  BoolValue Bool |                -- Boolean value
  MapValue (Map [Value] Value) |  -- Value of a map type
  CustomValue Integer             -- Value of a user-defined type (values with the same code are considered equal)
	deriving (Eq, Ord, Show)

data Environment = Environment
  {
    envVars :: Map Id Value,              -- Variable names to values
    envOld :: Map Id Value,               -- Variable names to old values (in two-state contexts)
    envConstants :: Map Id (Expression),  -- Constant names to expressions
    envFunctions :: Map Id FDef,          -- Function names to definitions
    envProcedures :: Map Id [PDef]        -- Procedure names to definitions
  } deriving Show
  
emptyEnv = Environment
  {
    envVars = M.empty,
    envOld = M.empty,
    envConstants = M.empty,
    envFunctions = M.empty,
    envProcedures = M.empty
  }

{- Errors -}

data ExecutionError = AssertViolation String | 
  AssumeViolation String |
  DivisionByZero |
  UndefinedValue String |
  UnsuportedConstruct String |
  OtherError String

instance Error ExecutionError where
  noMsg    = OtherError "Unknown error"
  strMsg s = OtherError s

instance Show ExecutionError where
  show (AssertViolation s) = "Assertion violation: " ++ s
  show (AssumeViolation s) = "Assumption violation: " ++ s
  show (DivisionByZero) = "Division by zero"
  show (UndefinedValue s) = "Value of " ++ s ++ " is not defined uniquely"
  show (UnsuportedConstruct s) = "Execution of " ++ s ++ " is not supported yet"
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
    binOpStrict Lc      v1 v2                         = throwError (UnsuportedConstruct "orders")
binOp _ (Left e) _ = Left e
binOp _ _ (Left e) = Left e
  
-- | Evaluate an expression in an environment
eval :: Environment -> Expression -> Result Value
eval env e = eval' env (contents e) 

eval' _   TT                          = return $ BoolValue True
eval' _   FF                          = return $ BoolValue False
eval' _   (Numeral n)                 = return $ IntValue n
eval' env (Var id)                    = case M.lookup id (envVars env) of
                                          Just val -> return val
                                          Nothing -> case M.lookup id (envConstants env) of
                                            Just expr -> eval env expr
                                            Nothing -> throwError (UndefinedValue ("variable or constant " ++ id))
eval' env (Application id args)       = case M.lookup id (envFunctions env) of
                                          Nothing -> throwError (UndefinedValue ("function " ++ id))
                                          Just (FDef formals body) -> do
                                            argsV <- mapM (eval env) args
                                            eval env { envVars = fScope formals argsV } body
  where
    fScope formals actuals = foldr (\(k, v) m -> M.insert k v m) (envVars env) (zip formals actuals)
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
eval' env (Old e)                     = eval env { envVars = envOld env } e
eval' env (UnaryExpression op e)      = unOp op <$> eval env e
eval' env (BinaryExpression op e1 e2) = binOp op (eval env e1) (eval env e2)                                                
eval' env (Quantified op args vars e) = throwError (UnsuportedConstruct "quantified expressions")

{- Statements -}

{- Declarations -}

dummyArg = ""

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
    
    