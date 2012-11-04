{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Position
import qualified Language.Boogie.Parser as Parser (program)
import Language.Boogie.TypeChecker
import Language.Boogie.PrettyPrinter
import Language.Boogie.Interpreter
import Language.Boogie.Tester
import System.Environment
import System.Console.CmdArgs
import System.Console.ANSI
import System.Random
import Data.Time.Calendar
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.State
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
    Exec file entry -> executeFromFile file entry
    args -> testFromFile (file args) (proc_ args) (testMethod args) (verbose args)

{- Command line arguments -}

data CommandLineArgs
    = Exec { file :: String, entry :: String }
    | Test { file :: String, proc_ :: [String], limits :: (Integer, Integer), dlimits :: (Integer, Integer), verbose :: Bool  }
    | RTest { file :: String, proc_ :: [String], limits :: (Integer, Integer), dlimits :: (Integer, Integer), tc_count :: Int, seed :: Maybe Int, verbose :: Bool }
      deriving (Data, Typeable, Show, Eq)

execute = Exec {
  entry = "Main"  &= help "Program entry point (must not have in- or out-parameters)" &= typ "PROCEDURE",
  file  = ""      &= typFile &= argPos 0
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
  defaultGen <- getStdGen
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
executeFromFile :: String -> String -> IO ()
executeFromFile file entryPoint = runOnFile printFinalState file
  where
    printFinalState p context = case M.lookup entryPoint (ctxProcedures context) of
      Nothing -> printError (text "Cannot find program entry point" <+> text entryPoint)
      Just sig -> if not (goodEntryPoint sig)
        then printError (text "Program entry point" <+> text entryPoint <+> text "does not have the required signature" <+> doubleQuotes (sigDoc [] []))
        else case executeProgram p context entryPoint of
          Left err -> printError err
          Right env -> (print . varsDoc . envGlobals) env
    goodEntryPoint sig = null (psigTypeVars sig) && null (psigArgTypes sig) && null (psigRetTypes sig)

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
  setSGR []
      
{- Helpers for testing internal functions -}      
      
-- | Harness for testing various internal functions
harness file = runOnFile printOutcome file
  where
    printOutcome p context = do
      let env = execState (collectDefinitions p) emptyEnv { envTypeContext = context }
      print $ envGlobals env      
          