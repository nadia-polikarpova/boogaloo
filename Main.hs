module Main where

import Text.ParserCombinators.Parsec
import AST
import Position
import Parser
import TypeChecker
import PrettyPrinter
import BasicBlocks
import Interpreter
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Identity
import Control.Monad.Error

interpret = case (parse e0 "" "true ==> x > x / 0") of
    Left err -> print ("Parsing error: " ++ show err)
    Right exp -> 
      case Interpreter.eval env exp of
      Left err -> print err
      Right res -> print res
  where
    env = emptyEnv { envVars = M.fromList [("x", IntValue 5)] }
      
main = do 
  result <- parseFromFile program "test.bpl" 
  case (result) of
    Left err -> print err
    Right ast -> case checkProgram ast of
      Left err -> putStr err
      Right p -> print (transformedBlockDoc (M.toList (snd (pdefBody (procedure ast)))))
  where
    procedure ast = head (envProcedures (collectDefinitions emptyEnv ast) ! "search")
      
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

  