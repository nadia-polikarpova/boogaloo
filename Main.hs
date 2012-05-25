module Main where

import Text.ParserCombinators.Parsec
import AST
import Value
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

-- | Name of the entry point procedure in a Boogie program
entryPoint = "main"

-- | Parse, type-check and execute a Boogie program from file
executeFromFile :: String -> IO ()
executeFromFile file = do 
  result <- parseFromFile program file
  case (result) of
    Left err -> print err
    Right ast -> case checkProgram ast of
      Left err -> putStr err
      Right context -> case executeProgram ast context entryPoint of
        Left err -> print err
        Right globals -> print (envDoc globals)

main = executeFromFile "test.bpl" 
      
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
          