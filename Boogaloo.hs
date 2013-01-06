{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Position
import qualified Language.Boogie.Parser as Parser (program)
import Language.Boogie.TypeChecker
import Language.Boogie.PrettyPrinter
import Language.Boogie.Heap
import Language.Boogie.Interpreter
import Language.Boogie.Tester
import Language.Boogie.Generator
import System.Environment
import System.Console.CmdArgs
import System.Console.ANSI
import System.Random
import Data.Time.Calendar
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Stream
import Control.Applicative
import Text.PrettyPrint hiding (mode)
import Text.ParserCombinators.Parsec (parse, parseFromFile)

programName = "boogaloo"
versionName = "0.1"
releaseDate = fromGregorian 2012 10 25

-- | Execute or test a Boogie program, according to command-line arguments
main = do
  res <- cmdArgsRun $ mode
  case res of
    Exec file entry bounds unbounded random seed btmax invalid nexec pass fail outMax debug -> 
      executeFromFile file entry (if unbounded then Nothing else Just bounds) random seed btmax invalid nexec pass fail outMax debug
    args -> testFromFile (file args) (proc_ args) (testMethod args) (verbose args)

{- Command line arguments -}

data CommandLineArgs
    = Exec { 
        file :: String, 
        entry :: String,
        bounds :: (Integer, Integer),
        unbounded :: Bool,
        random_ :: Bool,
        seed :: Maybe Int,
        btmax :: Maybe Int, 
        invalid :: Bool, 
        nexec :: Bool,
        pass :: Bool,
        fail_ :: Bool,
        outmax :: Int, 
        debug :: Bool
      }
    | Test { file :: String, proc_ :: [String], limits :: (Integer, Integer), dlimits :: (Integer, Integer), verbose :: Bool  }
    | RTest { file :: String, proc_ :: [String], limits :: (Integer, Integer), dlimits :: (Integer, Integer), tc_count :: Int, seed :: Maybe Int, verbose :: Bool }
      deriving (Data, Typeable, Show, Eq)
      
defaultBounds = (-64, 64)      

execute = Exec {
  entry     = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file      = ""              &= typFile &= argPos 0,
  bounds    = defaultBounds   &= help ("Minimum and maximum integer value to be chosen non-deterministically (default: " ++ show defaultBounds ++ ")") &= typ "NUM, NUM",
  unbounded = False           &= help "Ignore bounds; any integer value can be chosen (default: false)",
  random_   = False           &= help "Make non-deterministic choices randomly (default: false)",
  seed      = Nothing         &= help "Seed for the random number generator" &= typ "NUM",
  btmax     = Nothing         &= help "Maximum number of times execution is allowed to backtrack (default: unlimited)",
  invalid   = False           &= help "Keep unreachable states in the list of outcomes (default: false)",
  nexec     = True            &= help "Keep non-executable states in the list of outcomes (default: true)",
  pass      = True            &= help "Keep passing states in the list of outcomes (default: true)",
  fail_     = True            &= help "Keep failing states in the list of outcomes (default: true)",
  outmax    = 1               &= help "Maximum number of outcomes to display (default: 1)",
  debug     = False           &= help "Debug output (default: false)"
  } &= auto &= help "Execute program"
      
test_ = Test {
  proc_   = []      &= help "Procedures to test" &= typ "PROCEDURE",
  limits  = (-3, 3) &= help "Interval of input values to try for an integer variable" &= typ "NUM, NUM",
  dlimits = (0, 2)  &= help dlimitsMsg &= typ "NUM, NUM" ,
  file    = ""      &= typFile &= argPos 0,
  verbose = False   &= help verboseMsg
  } &= help "Test program exhaustively"
  
rtest = RTest {
  proc_     = []        &= help "Procedures to test" &= typ "PROCEDURE",
  limits    = (-32, 32) &= help "Interval of input values to draw from for an integer variable" &= typ "NUM, NUM",
  dlimits   = (0, 2)    &= help dlimitsMsg &= typ "NUM, NUM",
  tc_count  = 10        &= help "Number of test cases to generate per procedure implementation" &= name "n" &= typ "NUM",
  seed      = Nothing   &= help "Seed for the random number generator" &= typ "NUM",
  file      = ""        &= typFile &= argPos 0,
  verbose = False       &= help verboseMsg
  } &= help "Test program on random inputs"
  
dlimitsMsg = "Given a map with an integer domain, different range values will be tried for domain values in this interval"
verboseMsg = "Output all executed test cases"
    
mode = cmdArgsMode $ modes [execute, test_, rtest] &= 
  help "Boogie interpreter" &= 
  program programName &= 
  summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)
  
-- | Set up a test method depending on command-line arguments  
testMethod :: CommandLineArgs -> Program -> Context -> [Id] -> IO [TestCase]
testMethod (Test _ _ limits dlimits _ ) program context procNames = 
  let settings = ExhaustiveSettings {
      esIntRange = interval limits,
      esIntMapDomainRange = interval dlimits,
      esGenericTypeRange = defaultGenericTypeRange context,
      esMapTypeRange = defaultMapTypeRange context
    }
  in return $ testProgram settings program context procNames
testMethod (RTest _ _ limits dlimits tc_count seed _) program context procNames = do
  randomGen <- case seed of
    Nothing -> getStdGen
    Just s -> return $ mkStdGen s
  let settings = RandomSettings {
      rsRandomGen = randomGen,
      rsCount = tc_count,
      rsIntLimits = limits,
      rsIntMapDomainRange = interval dlimits,
      rsGenericTypeRange = defaultGenericTypeRange context,
      rsMapTypeRange = defaultMapTypeRange context     
    }  
  return $ testProgram settings program context procNames
    
{- Interfacing internal modules -}

-- | Execute procedure entryPoint from file
-- | and output either errors or the final values of global variables
executeFromFile :: String -> String -> Maybe (Integer, Integer) -> Bool -> Maybe Int -> Maybe Int -> Bool -> Bool -> Bool -> Bool -> Int -> Bool -> IO ()
executeFromFile file entryPoint bounds random seed btMax invalid nexec pass fail outMax debug = runOnFile printFinalState file
  where
    printFinalState p context = case M.lookup entryPoint (ctxProcedures context) of
      Nothing -> printError (text "Cannot find program entry point" <+> text entryPoint)
      Just _ -> do
        rGen <- case seed of
          Nothing -> getStdGen
          Just s -> return $ mkStdGen s      
        let generator = if random then randomGenerator rGen bounds else exhaustiveGenerator bounds
        let outs = (take outMax . filter keep . limitBT) (outcomes p context generator)
        if null outs
          then printAux $ text "No outcomes to display"
          else zipWithM_ printOne [0..] outs
    outcomes p context generator = if btMax == Just 1 || (keepAll && outMax == 1)
      then [executeProgramDet p context entryPoint]
      else executeProgram p context generator entryPoint
    keepAll = invalid && nexec && pass && fail
    limitBT = case btMax of
      Nothing -> id
      Just n -> take n
    keep out = 
      (if invalid then True else not (isInvalid out)) &&
      (if nexec then True else not (isNonexecutable out)) &&
      (if pass then True else not (isPass out)) &&
      (if fail then True else not (isFail out))
    printOutcome out = case out of
      Left err -> printError err
      Right mem -> if debug
        then print $ debugMemoryDoc mem
        else print $ userMemoryDoc mem (const True)
    printOne n out    = do
      when (n > 0) $ print newline
      printAux $ text "Outcome" <+> integer n <+> newline
      printOutcome out      

-- | Test procedures procNames from file with a testMethod
-- | and output the test outcomes
testFromFile :: String -> [String] -> (Program -> Context -> [String] -> IO [TestCase]) -> Bool -> IO ()
testFromFile file procNames testMethod printAll = runOnFile printTestOutcomes file
  where
    printTestOutcomes p context = do
      let (present, missing) = partition (`M.member` ctxProcedures context) procNames
      when (not (null missing)) $ printError (text "Cannot find procedures under test:" <+> commaSep (map text missing))
      testResults <- testMethod p context present
      print $ testSessionSummary testResults
      when printAll $ putStr "\n" >> mapM_ print testResults

-- | Parse file, type-check the resulting program, then execute command on the resulting program and type context
runOnFile :: (Program -> Context -> IO ()) -> String -> IO ()      
runOnFile command file = do 
  parseResult <- parseFromFile Parser.program file
  case parseResult of
    Left parseErr -> printError parseErr
    Right p -> case typeCheckProgram p of
      Left typeErrs -> printError (typeErrorsDoc typeErrs)
      Right context -> command p context
      
{- Output -}

-- | Output errors in red
printError e = do
  setSGR [SetColor Foreground Vivid Red]
  print e
  setSGR [Reset]
  
-- | Output auxiliary messages in khaki  
printAux msg = do
  setSGR [SetColor Foreground Dull Yellow]
  print msg
  setSGR [Reset]
      
{- Helpers for testing internal functions -}      
      
-- | Harness for testing various internal functions
harness file = runOnFile printOutcome file
  where
    printOutcome p context = do
      let env = head (toList (execStateT (collectDefinitions p) (initEnv context (exhaustiveGenerator (Just defaultBounds)))))
      print $ (debugMemoryDoc . memory) env           