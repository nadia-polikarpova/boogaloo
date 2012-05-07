{- Interpreter for Boogie 2 -}
module Interpreter where

import AST
import Position
import TypeChecker
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
    envVars :: Map Id Value,                  -- Variable names to values
    envOld :: Map Id Value,                   -- Variable names to old values (in two-state contexts)
    envFunctions :: Map Id ([Id], Expression) -- Function names to (formal arguments, body)
  }
  
emptyEnv = Environment
  {
    envVars = M.empty,
    envOld = M.empty,
    envFunctions = M.empty
  }

{- Errors -}

-- | Execution result: either 'a' or an error with strings message
type Result a = Either String a

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
                                                    then throwError "Division by zero"
                                                    else return $ IntValue (n1 `div` n2)
    binOpStrict Mod     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                    then throwError "Division by zero"
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
    binOpStrict Lc      v1 v2                         = throwError "Extends order is not supported yet"
binOp _ (Left e) _ = Left e
binOp _ _ (Left e) = Left e
  
-- | Value of an expression in an environment
expression :: Environment -> Expression -> Result Value
expression env e = expression' env (contents e) 

expression' _   TT                          = return $ BoolValue True
expression' _   FF                          = return $ BoolValue False
expression' _   (Numeral n)                 = return $ IntValue n
expression' env (Var id)                    = return $ (envVars env) ! id
expression' env (Application id args)       = case M.lookup id (envFunctions env) of
                                                Nothing -> throwError ("Function " ++ id ++ " does not have a body")
                                                Just (formals, body) -> do
                                                  argsV <- mapM (expression env) args
                                                  expression env { envVars = fScope formals argsV } body
  where
    fScope formals actuals = foldr (\(k, v) m -> M.insert k v m) (envVars env) (zip formals actuals)
expression' env (MapSelection m args)       = do 
                                                mV <- expression env m
                                                argsV <- mapM (expression env) args
                                                case mV of 
                                                  MapValue map -> case M.lookup argsV map of
                                                    Nothing -> throwError ("Value " ++ show (MapSelection m args) ++ " is undefined")
                                                    Just v -> return v
expression' env  (MapUpdate m args new)     = do
                                                mV <- expression env m
                                                argsV <- mapM (expression env) args
                                                newV <- expression env new
                                                case mV of 
                                                  MapValue map -> return $ MapValue (M.insert argsV newV map)
expression' env (Old e)                     = expression env { envVars = envOld env } e
expression' env (UnaryExpression op e)      = unOp op <$> expression env e
expression' env (BinaryExpression op e1 e2) = binOp op (expression env e1) (expression env e2)                                                
expression' env (Quantified op args vars e) = throwError ("Quantified expressions not supported yet")