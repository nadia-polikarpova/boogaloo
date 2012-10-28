module Main where

import Language.Boogie.Parser
import Language.Boogie.TypeChecker
import Language.Boogie.Interpreter
import Data.Map (Map, (!))
import qualified Data.Map as M
import Text.ParserCombinators.Parsec (parse, parseFromFile)
import Test.HUnit
import Distribution.TestSuite

main = runTestTT allTests

allTests = TestList [typeCheckerTests, interpreterTests]

typeCheckerTests = TestLabel "TypeChecker" $ TestList [
  TestLabel "TypeVarClash" (TestCase $ typeCheckerFailure "tests/TypeVarClash.bpl")
  ]

interpreterTests = TestLabel "Interpreter" $ TestList [
  TestLabel "NoGuards" (TestCase $ interpreterSuccess "tests/NoGuards.bpl"),
  TestLabel "EmptyDomains" (TestCase $ interpreterSuccess "tests/EmptyDomains.bpl")
  ]
  
-- | Test that type checker fails on file  
typeCheckerFailure file = do 
  parseResult <- parseFromFile program file
  case parseResult of
    Left parseErr -> assertFailure (show parseErr)
    Right p -> case checkProgram p of
      Left typeErrs -> return ()
      Right context -> assertFailure ("Undetected type error")  
      
-- | Test that type checker succeeds on file
typeCheckerSuccess file = do 
  parseResult <- parseFromFile program file
  case parseResult of
    Left parseErr -> assertFailure (show parseErr)
    Right p -> case checkProgram p of
      Left typeErrs -> assertFailure (show (typeErrorsDoc typeErrs))
      Right context -> return ()
      
-- | Entry point for test programs      
entryPoint = "Test"      

-- | Test that interpreter succeeds (no run-time failures or crashes) on procedure entryPoint in file      
interpreterSuccess file = do 
  parseResult <- parseFromFile program file
  case parseResult of
    Left parseErr -> assertFailure (show parseErr)
    Right p -> case checkProgram p of
      Left typeErrs -> assertFailure (show (typeErrorsDoc typeErrs))
      Right context -> case executeProgram p context entryPoint of
        Left err -> assertFailure (show err)
        Right env -> return ()

