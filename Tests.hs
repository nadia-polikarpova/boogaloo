module Main where

import Language.Boogie.Parser
import Language.Boogie.PrettyPrinter
import Language.Boogie.TypeChecker
import Language.Boogie.Interpreter
import Data.Map (Map, (!))
import qualified Data.Map as M
import System.FilePath
import Text.ParserCombinators.Parsec (parse, parseFromFile)
import Test.HUnit

main = runTestTT allTests

allTests = TestList [parserTests, typeCheckerTests, interpreterTests]

parserTests = TestLabel "Parser" $ TestList [
  testCase parserSuccess "AttributeParsing"
  ]

typeCheckerTests = TestLabel "TypeChecker" $ TestList [
  testCase (typeCheckerFailure 8)   "BadLabels",
  testCase (typeCheckerFailure 4)   "Orderings",
  testCase (typeCheckerFailure 4)   "WhereResolution",
  testCase (typeCheckerFailure 35)  "Arrays",
  testCase (typeCheckerFailure 15)  "Frame",
  testCase (typeCheckerFailure 3)   "FunBody",
  testCase (typeCheckerFailure 3)   "IfThenElse",
  testCase (typeCheckerFailure 4)   "Lambda",
  testCase (typeCheckerFailure 12)  "UpdateExprTyping",
  testCase (typeCheckerFailure 1)   "TypeVarClash"
  ]

interpreterTests = TestLabel "Interpreter" $ TestList [
  testCase interpreterSuccess "NoGuards",
  testCase interpreterSuccess "EmptyDomains"
  ]
  
-- | Directory with test programs  
testDir = "tests"  
-- | Entry point for test programs      
entryPoint = "Test"        
  
testCase kind name = TestLabel name (TestCase $ kind (testDir </> name <.> "bpl")) 
  
-- | Test that parser fails on file  
parserFailure file = do 
  parseResult <- parseFromFile program file
  case parseResult of
    Left parseErr -> return ()
    Right p -> assertFailure ("Undetected syntax error")  
  
-- | Test that parser succeeds on file, and re-parsing pretty printer code produces the same AST
parserSuccess file = do 
  parseResult <- parseFromFile program file
  case parseResult of
    Left parseErr -> assertFailure (show parseErr)
    Right p -> case parse program ('*' : file) (show p) of
      Left parseErr' -> assertFailure (show parseErr')
      Right p' -> if p == p'
        then return ()
        else assertFailure "Re-parsing resulted in a different AST"
  
-- | Test that type checker reports n errors on file  
typeCheckerFailure n file = do 
  parseResult <- parseFromFile program file
  case parseResult of
    Left parseErr -> assertFailure (show parseErr)
    Right p -> case typeCheckProgram p of
      Left typeErrs -> let m = length typeErrs in assertBool ("Expected " ++ show n ++ " type errors and got " ++ show m) (m == n)
      Right context -> assertFailure ("Expected " ++ show n ++ " type errors and got 0")
      
-- | Test that type checker succeeds on file
typeCheckerSuccess file = do 
  parseResult <- parseFromFile program file
  case parseResult of
    Left parseErr -> assertFailure (show parseErr)
    Right p -> case typeCheckProgram p of
      Left typeErrs -> assertFailure (show (typeErrorsDoc typeErrs))
      Right context -> return ()
      
-- | Test that interpreter succeeds (no run-time failures or crashes) on procedure entryPoint in file      
interpreterSuccess file = do 
  parseResult <- parseFromFile program file
  case parseResult of
    Left parseErr -> assertFailure (show parseErr)
    Right p -> case typeCheckProgram p of
      Left typeErrs -> assertFailure (show (typeErrorsDoc typeErrs))
      Right context -> case executeProgram p context entryPoint of
        Left err -> assertFailure (show err)
        Right env -> return ()

