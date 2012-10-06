module Main where

import Text.ParserCombinators.Parsec
import AST
import Util
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
import Control.Applicative

-- | Name of the entry point procedure in a Boogie program
defaultEntryPoint = "main"

-- | Parse, type-check and execute a Boogie program from file
executeFromFile :: String -> String -> IO ()
executeFromFile file entryPoint = do 
  result <- parseFromFile program file
  case (result) of
    Left err -> print err
    Right p -> case checkProgram p of
      Left errs -> print (typeErrorsDoc errs)
      Right context -> case executeProgram p context entryPoint of
        Left err -> print err
        Right globals -> print $ varsDoc globals

main = executeFromFile "test.bpl" "main"
      
test = do
  result <- parseFromFile program "test.bpl" 
  case (result) of
    Left err -> print err
    Right p -> do
      case parse program "test1.bpl" (show p) of
        Left err -> print err
        Right p' -> if show p == show p'
          then putStr ("Passed.\n")
          else putStr ("Failed with different ASTs.\n")
          