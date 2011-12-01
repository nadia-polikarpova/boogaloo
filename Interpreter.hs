{- Semantics of Boogie -}
module Interpreter where

import AST

{- State -}
data Value = IntValue Integer | BoolValue Bool 
	deriving Show

type Environment = [(Id, Value)]

{- Errors -}
type Msg = String

data Error a = Success a | Error Msg
	deriving Show
	
instance Monad Error where
	return x          = Success x
	(Success a) >>= k = k a
	(Error msg) >>= k = Error msg
	
throw :: Msg -> Error a
throw msg = Error msg

catch :: Error a -> (Msg -> Error a) -> Error a
catch (Success a) h = (Success a)
catch (Error msg) h = h msg

{- Expressions -}
unOp :: UnOp -> Value -> Error Value
unOp Neg (IntValue n) = return (IntValue (-n))
unOp Not (BoolValue b) = return (BoolValue (not b))
unOp op v = throw ("Invalid argument type " ++ show v ++ " to operation " ++ show op) -- ToDo: output type

binOp :: BinOp -> Value -> Value -> Error Value
binOp Plus (IntValue n1) (IntValue n2) = return (IntValue (n1 + n2))
binOp Minus (IntValue n1) (IntValue n2) = return (IntValue (n1 - n2))
binOp Times (IntValue n1) (IntValue n2) = return (IntValue (n1 * n2))
binOp Div (IntValue n1) (IntValue n2) = return (IntValue (n1 `div` n2))
binOp Mod (IntValue n1) (IntValue n2) = return (IntValue (n1 `mod` n2))
binOp Leq (IntValue n1) (IntValue n2) = return (BoolValue (n1 <= n2))
binOp Ls (IntValue n1) (IntValue n2) = return (BoolValue (n1 < n2))
binOp Geq (IntValue n1) (IntValue n2) = return (BoolValue (n1 >= n2))
binOp Gt (IntValue n1) (IntValue n2) = return (BoolValue (n1 > n2))
binOp And (BoolValue b1) (BoolValue b2) = return (BoolValue (b1 && b2))
binOp Or (BoolValue b1) (BoolValue b2) = return (BoolValue (b1 || b2))
binOp Implies (BoolValue b1) (BoolValue b2) = return (BoolValue (b1 <= b2))
binOp Equiv (BoolValue b1) (BoolValue b2) = return (BoolValue (b1 == b2))
binOp Eq (IntValue n1) (IntValue n2) = return (BoolValue (n1 == n2))
binOp Eq (BoolValue b1) (BoolValue b2) = return (BoolValue (b1 == b2))
binOp Neq (IntValue n1) (IntValue n2) = return (BoolValue (n1 /= n2))
binOp Neq (BoolValue b1) (BoolValue b2) = return (BoolValue (b1 /= b2))
binOp Lc (IntValue n1) (IntValue n2) = return (BoolValue (n1 <= n2))
binOp Lc (BoolValue b1) (BoolValue b2) = return (BoolValue (b1 <= b2))
binOp op v1 v2 = throw ("Invalid argument types " ++ show v1 ++ " and " ++ show v2 ++ " to operation " ++ show op)

expression :: Expression -> Environment -> Error Value
expression (Numeral n) _ = return (IntValue n)
expression TT _ = return (BoolValue True)
expression FF _ = return (BoolValue False)
expression (Var id) env = case lookup id env of
		(Just v) -> return v
		Nothing -> throw ("Undeclared identifier " ++ id)
expression (Application id args) env = throw ("Function calls not supported yet")
expression (Old e) env = throw ("Old expressions not supported yet")
expression (UnaryExpression op e) env = do { v <- expression e env;
	                                       unOp op v }
expression (BinaryExpression op e1 e2) env = do { v1 <- expression e1 env;
                                             v2 <- expression e2 env;
											 binOp op v1 v2 }