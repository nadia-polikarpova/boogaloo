module Main where

import Text.ParserCombinators.Parsec
import AST
import Parser
import TypeChecker
import PrettyPrinter
import Interpreter
import qualified Data.Map as M
import Control.Monad.Identity
import Control.Monad.Error

interpret = case (parse e0 "" "false ==> x > x / 0") of
    Left err -> print ("Parsing error: " ++ show err)
    Right exp -> 
      case Interpreter.expression env exp of
      Left err -> print ("Evaluation failed: " ++ err)
      Right res -> print res
  where
    env = emptyEnv { envVars = M.fromList [("x", IntValue 5)] }
      
main = do 
  result <- parseFromFile program "test.bpl" 
  case (result) of
    Left err -> print err
    Right ast -> case checkProgram ast of
      Left err -> putStr err
      Right p -> print (programDoc ast)
      
test = do
  result <- parseFromFile program "test.bpl" 
  case (result) of
    Left err -> print err
    Right ast -> do
      case parse program "test1.bpl" (show (programDoc ast)) of
        Left err -> print err
        Right ast' -> if show (programDoc ast) == show (programDoc ast') 
          then putStr ("Passed.\n")
          else putStr ("Failed with different ASTs.\n")

  