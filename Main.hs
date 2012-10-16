module Main where

import Text.ParserCombinators.Parsec (parse, parseFromFile)
import AST
import Util
import Position
import Parser (program)
import TypeChecker
import PrettyPrinter
import Interpreter
import Tester
import System.Random
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Identity
import Control.Monad.Error
import Control.Monad.State
import Control.Applicative
import Text.PrettyPrint

main = testFromFile "test.bpl" ["sum_max", "main", "search", "poly"]
-- main = harness "test.bpl"
-- main = executeFromFile "test.bpl" "main"

-- | Harness for testing various internal functions
harness file = runOnFile printOutcome file
  where
    printOutcome p context = do
      -- let env = execState (collectDefinitions p) emptyEnv { envTypeContext = context }
      randomGen <- getStdGen
      let res = evalState (combineInputs (generateInputValue context) (replicate 3 IntType)) (defaultSettings context (Just randomGen))
      -- let res = genInputsExhaustive (-3, 3) [IntType, IntType]
      print $ res    

-- | Execute procedure entryPoint from file
-- | and output either errors or the final values of global variables
executeFromFile :: String -> String -> IO ()
executeFromFile file entryPoint = runOnFile printFinalState file
  where
    printFinalState p context = case M.lookup entryPoint (ctxProcedures context) of
      Nothing -> print (text "Cannot find program entry point" <+> text entryPoint)
      Just sig -> if not (goodEntryPoint sig)
        then print (text "Program entry point" <+> text entryPoint <+> text "does not have the required signature" <+> doubleQuotes (sigDoc [] []))
        else case executeProgram p context entryPoint of
          Left err -> print err
          Right env -> (print . varsDoc . envGlobals) env
    goodEntryPoint sig = null (psigTypeVars sig) && null (psigArgTypes sig) && null (psigRetTypes sig)

-- | Test procedure entryPoint from file on a number of inputs
-- | and output the test outcomes
testFromFile :: String -> [String] -> IO ()
testFromFile file procNames = runOnFile printTestOutcomes file
  where
    printTestOutcomes p context = do
      let (present, missing) = partition (`M.member` ctxProcedures context) procNames
      when (not (null missing)) $ print (text "Cannot find procedures under test:" <+> commaSep (map text missing))
      randomGen <- getStdGen
      mapM_ print (testProgram (defaultSettings context (Just randomGen)) p context present)
      
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
          