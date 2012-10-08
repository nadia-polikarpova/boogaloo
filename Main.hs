module Main where

import Text.ParserCombinators.Parsec
import AST
import Util
import Position
import Parser
import TypeChecker
import PrettyPrinter
import Interpreter
import Tester
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Identity
import Control.Monad.Error
import Control.Applicative

main = testFromFile "test.bpl" "search"
-- main = executeFromFile "test.bpl" "main"

-- | Execute procedure entryPoint from file
-- | and output either errors or the final values of global variables;
-- | entryPoint must have no in- or out- parameters
executeFromFile :: String -> String -> IO ()
executeFromFile file entryPoint = runOnFile printFinalState file
  where
    printFinalState p context = case executeProgram p context entryPoint of
      Left err -> print err
      Right env -> (print . varsDoc . envGlobals) env

-- | Test procedure entryPoint from file on a number of inputs
-- | and output the test outcomes
testFromFile :: String -> String -> IO ()
testFromFile file entryPoint = runOnFile printTestOutcomes file
  where
    printTestOutcomes p context = mapM_ putStrLn (testProgram p context entryPoint)

-- | Parse file, type-check the resulting program, then execute command on the resulting program and type context
runOnFile :: (Program -> Context -> IO ()) -> String -> IO ()      
runOnFile command file = do 
  parseResult <- parseFromFile program file
  case parseResult of
    Left parseErr -> print parseErr
    Right p -> case checkProgram p of
      Left typeErrs -> print (typeErrorsDoc typeErrs)
      Right context -> command p context
      
-- | Test that print . parse == print . parse . print .parse      
testParser :: String -> IO ()      
testParser file = do
  result <- parseFromFile program file
  case (result) of
    Left err -> print err
    Right p -> do
      case parse program ('*' : file) (show p) of
        Left err -> print err
        Right p' -> if show p == show p'
          then putStr ("Passed.\n")
          else putStr ("Failed with different ASTs.\n")
          