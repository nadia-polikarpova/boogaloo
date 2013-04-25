module Main where

import Language.Boogie.Parser
import Language.Boogie.Pretty
import Language.Boogie.PrettyAST
import Language.Boogie.TypeChecker
import Language.Boogie.Interpreter hiding (TestCase)
import qualified Language.Boogie.Interpreter as I
import Language.Boogie.Solver
import qualified Language.Boogie.Z3.Solver as Z3
import Language.Boogie.Generator
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Stream
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
  testCase (typeCheckerFailure 1)   "TypeVarClash",
  testCase (typeCheckerFailure 8)   "GenericReturn",
  testCase (typeCheckerFailure 3)   "MissingTV",
  testCase typeCheckerSuccess       "DafnyPrelude",
  testCase typeCheckerSuccess       "VccPrelude"
  ]

interpreterTests = TestLabel "Interpreter" $ TestList [
  testCase interpreterSuccess "DivZero",
  -- testCase interpreterSuccess "NoGuards",
  testCase interpreterSuccess "EmptyDomains",
  testCase interpreterSuccess "MapInit",
  testCase interpreterSuccess "MapLocals",
  testCase interpreterSuccess "OldND",
  testCase interpreterSuccess "OldMaps",
  testCase interpreterSuccess "MapEquality",
  testCase interpreterSuccess "LambdaExec",
  testCase interpreterSuccess "ConstraintContext",
  testCase interpreterSuccess "Constraints"
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
    Right p -> case parse program ('*' : file) (show $ pretty p) of
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
      Right context -> let 
          solve :: Solver Stream
          solve = Z3.solve True Nothing
          generator = exhaustiveGenerator Nothing
        in case (head . filter (not . isInvalid) . toList) (executeProgram p context solve generator entryPoint) of
          I.TestCase _ _ _ (Just err) -> assertFailure (show $ pretty err)
          otherwise -> return ()

