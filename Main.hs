module Main where

import Text.ParserCombinators.Parsec
import AST
import Parser
import Interpreter

test :: Parser Expression
test = do { spaces; res <- e0; eof; return res }

myEnv :: Environment
myEnv = [("x", IntValue 1), ("y", IntValue 5), ("b", BoolValue False)]

e :: Expression 
e = BinaryExpression Plus (UnaryExpression Neg (Application "x" [])) (Numeral 6)

eval :: String -> Error Value
eval s = case (parse test "" s) of 
	Left err -> Error (show err)
	Right e -> expression e myEnv