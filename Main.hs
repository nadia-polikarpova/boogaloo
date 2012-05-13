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

main = do 
  result <- parseFromFile program "test.bpl" 
  case (result) of
    Left err -> print err
    Right ast -> case checkProgram ast of
      Left err -> putStr err
      Right context -> case executeProgram ast "main" of
        Left err -> print err
        Right env -> print env
      
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

  