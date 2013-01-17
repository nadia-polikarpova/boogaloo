{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Position
import qualified Language.Boogie.Parser as Parser (program)
import Language.Boogie.TypeChecker
import Language.Boogie.PrettyPrinter
import Language.Boogie.Heap
import Language.Boogie.Environment
import Language.Boogie.Interpreter
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
import Control.Lens hiding (Context, at)
import Text.PrettyPrint hiding (mode)
import Text.ParserCombinators.Parsec (parse, parseFromFile)

programName = "boogaloo"
versionName = "0.1"
releaseDate = fromGregorian 2012 10 25

-- | Execute or test a Boogie program, according to command-line arguments
main = do
  res <- cmdArgsRun $ mode
  case res of
    Exec file proc_ bounds random seed btmax invalid nexec pass fail outMax sum debug -> 
      executeFromFile file proc_ (rangeToMaybe bounds) random seed btmax invalid nexec pass fail (natToMaybe outMax) sum debug
    Test file proc_ bounds outMax debug ->
      executeFromFile file proc_ (rangeToMaybe bounds) False Nothing Nothing True True True True (natToMaybe outMax) True debug
    RTest file proc_ bounds seed outMax debug ->
      executeFromFile file proc_ (rangeToMaybe bounds) True seed Nothing True True True True (natToMaybe outMax) True debug      
  where
    rangeToMaybe (min, max)
      | min <= max  = Just (min, max)
      | otherwise   = Nothing
    natToMaybe n
      | n >= 0      = Just n
      | otherwise   = Nothing

{- Command line arguments -}

data CommandLineArgs
    = Exec { 
        file :: String, 
        proc_ :: String,
        bounds :: (Integer, Integer),
        random_ :: Bool,
        seed :: Maybe Int,
        btmax :: Maybe Int, 
        invalid :: Bool, 
        nexec :: Bool,
        pass :: Bool,
        fail_ :: Bool,
        outmax :: Int, 
        summary_ :: Bool,
        debug :: Bool
      }
    | Test { 
        file :: String, 
        proc_ :: String,
        bounds :: (Integer, Integer),
        outmax :: Int, 
        debug :: Bool
      }
    | RTest { 
        file :: String, 
        proc_ :: String,
        bounds :: (Integer, Integer),
        seed :: Maybe Int,
        outmax :: Int, 
        debug :: Bool
      }
      deriving (Data, Typeable, Show, Eq)

-- | Default for the @bounds@ parameter      
defaultBounds = (-64, 64)

-- | Default for the @bounds@ parameter  in exhaustive testing
defaultExBounds = (-4, 4)

-- | Default number of test cases in random testing
defaultRTC = 100

execute = Exec {
  proc_     = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file      = ""              &= typFile &= argPos 0,
  bounds    = defaultBounds   &= help ("Minimum and maximum integer value to be chosen non-deterministically; " ++
                                       "unbounded if min > max (default: " ++ show defaultBounds ++ ")") &= typ "NUM, NUM",
  random_   = False           &= help "Make non-deterministic choices randomly (default: false)",
  seed      = Nothing         &= help "Seed for the random number generator" &= typ "NUM",
  btmax     = Nothing         &= help "Maximum number of times execution is allowed to backtrack (default: unlimited)" &= name "B",
  invalid   = False           &= help "Keep unreachable states in the list of outcomes (default: false)" &= name "I",
  nexec     = True            &= help "Keep non-executable states in the list of outcomes (default: true)" &= name "N",
  pass      = True            &= help "Keep passing states in the list of outcomes (default: true)" &= name "P",
  fail_     = True            &= help "Keep failing states in the list of outcomes (default: true)" &= name "F",
  outmax    = 1               &= help "Maximum number of outcomes to display; unbounded if negative (default: 1)",
  summary_  = False           &= help "Only print a summary of all executions and a list of unique failures (default: false)" &= name "S",
  debug     = False           &= help "Debug output (default: false)"
  } &= auto &= help "Execute program"
  
test = Test {
  proc_     = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file      = ""              &= typFile &= argPos 0,
  bounds    = defaultExBounds &= help ("Minimum and maximum integer value to be chosen non-deterministically; " ++
                                       "unbounded if min > max (default: " ++ show defaultExBounds ++ ")") &= typ "NUM, NUM",
  outmax    = -1               &= help "Maximum number of test cases; unbounded if negative (default: -1)",
  debug     = False           &= help "Debug output (default: false)"
  } &= help "Test program exhaustively"
  
rtest = RTest {
  proc_     = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file      = ""              &= typFile &= argPos 0,
  bounds    = defaultBounds   &= help ("Minimum and maximum integer value to be chosen non-deterministically; " ++
                                       "unbounded if min > max (default: " ++ show defaultBounds ++ ")") &= typ "NUM, NUM",
  seed      = Nothing         &= help "Seed for the random number generator" &= typ "NUM",
  outmax    = defaultRTC      &= help ("Number of test cases; unbounded if negative (default: " ++ show defaultRTC ++")"),
  debug     = False           &= help "Debug output (default: false)"
  } &= help "Test program on random inputs"
      
mode = cmdArgsMode $ modes [execute, test, rtest] &= 
  help "Boogie interpreter" &= 
  program programName &= 
  summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)
    
{- Interfacing internal modules -}

-- | Execute procedure proc_ from file
-- | and output either errors or the final values of global variables
executeFromFile :: String -> String -> Maybe (Integer, Integer) -> Bool -> Maybe Int -> Maybe Int -> Bool -> Bool -> Bool -> Bool -> Maybe Int -> Bool -> Bool -> IO ()
executeFromFile file proc_ bounds random seed btMax invalid nexec pass fail outMax summary debug = runOnFile printFinalState file
  where
    printFinalState p context = case M.lookup proc_ (ctxProcedures context) of
      Nothing -> printError (text "Cannot find procedure" <+> text proc_)
      Just _ -> do
        rGen <- case seed of
          Nothing -> getStdGen
          Just s -> return $ mkStdGen s      
        let generator = if random then randomGenerator rGen bounds else exhaustiveGenerator bounds
        let outs = (maybeTake outMax . filter keep . maybeTake btMax) (outcomes p context generator)
        if summary
          then do
            let sum = testSessionSummary outs 
            print $ summaryDoc sum
            zipWithM_ (printOne "Failure") [0..] (sUniqueFailures sum)
          else if null outs
            then printAux $ text "No executions to display"
            else zipWithM_ (printOne "Execution") [0..] outs
    outcomes p context generator = if btMax == Just 1 || (keepAll && outMax == Just 1)
      then [executeProgramDet p context proc_]
      else executeProgram p context generator proc_
    keepAll = invalid && nexec && pass && fail
    maybeTake mLimit = case mLimit of
      Nothing -> id
      Just n -> take n
    keep tc = 
      (if invalid then True else (not . isInvalid) tc) &&
      (if nexec then True else (not . isNonexecutable) tc) &&
      (if pass then True else (not . isPass) tc) &&
      (if fail then True else (not . isFail) tc)
    printTestCase tc = do
      print $ testCaseSummary debug tc <> newline      
      case tcFailure tc of
        Just err -> do
          printError $ runtimeFailureDoc debug err
          when debug (print $ newline <> finalStateDoc True tc)
        Nothing -> print $ finalStateDoc debug tc
    printOne title n tc = do
      when (n > 0) $ print newline
      printAux $ text title <+> integer n
      printTestCase tc

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
      print $ memoryDoc True (env^.envMemory)