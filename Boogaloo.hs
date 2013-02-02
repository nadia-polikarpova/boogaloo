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
    Exec file proc_ bound random seed btmax invalid nexec pass fail outMax sum debug -> 
      executeFromFile file proc_ (natToMaybe bound) random seed btmax invalid nexec pass fail (natToMaybe outMax) sum debug
    Test file proc_ bound outMax debug ->
      executeFromFile file proc_ (natToMaybe bound) False Nothing Nothing True True True True (natToMaybe outMax) True debug
    RTest file proc_ bound seed outMax debug ->
      executeFromFile file proc_ (natToMaybe bound) True seed Nothing True True True True (natToMaybe outMax) True debug      
  where
    natToMaybe n
      | n >= 0      = Just n
      | otherwise   = Nothing

{- Command line arguments -}

data CommandLineArgs
    = Exec { 
        file :: String, 
        proc_ :: String,
        branch_max :: Integer,
        random_ :: Bool,
        seed :: Maybe Int,
        exec_max :: Maybe Int, 
        invalid :: Bool, 
        nexec :: Bool,
        pass :: Bool,
        fail_ :: Bool,
        out_max :: Int, 
        summary_ :: Bool,
        debug :: Bool
      }
    | Test { 
        file :: String, 
        proc_ :: String,
        branch_max :: Integer,
        out_max :: Int, 
        debug :: Bool
      }
    | RTest { 
        file :: String, 
        proc_ :: String,
        branch_max :: Integer,
        seed :: Maybe Int,
        out_max :: Int, 
        debug :: Bool
      }
      deriving (Data, Typeable, Show, Eq)

-- | Default branching
defaultBranch = 128

-- | Default branching in exhaustive testing
defaultExBranch = 8

-- | Default number of test cases in random testing
defaultRTC = 100

execute = Exec {
  proc_       = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file        = ""              &= typFile &= argPos 0,
  branch_max  = defaultBranch   &= help ("Maximum number of possibilities for each non-deterministic choice; " ++
                                       "unbounded if negative (default: " ++ show defaultBranch ++ ")"),
  random_     = False           &= help "Make non-deterministic choices randomly (default: false)",
  seed        = Nothing         &= help "Seed for the random number generator" &= typ "NUM",
  exec_max    = Nothing         &= help "Maximum number of executions to try (default: unlimited)",
  invalid     = False           &= help "Display invalid executions (default: false)" &= name "I",
  nexec       = True            &= help "Display executions that cannot be carried out completely (default: true)" &= name "N",
  pass        = True            &= help "Display passing executions (default: true)" &= name "P",
  fail_       = True            &= help "Display failing executions (default: true)" &= name "F",
  out_max      = 1              &= help "Maximum number of executions to display; unbounded if negative (default: 1)",
  summary_    = False           &= help "Only print a summary of all executions and a list of unique failures (default: false)" &= name "S",
  debug       = False           &= help "Debug output (default: false)"
  } &= auto &= help "Execute program"
  
test = Test {
  proc_       = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file        = ""              &= typFile &= argPos 0,
  branch_max  = defaultExBranch &= help ("Maximum number of possibilities for each non-deterministic choice; " ++
                                         "unbounded if negative (default: " ++ show defaultExBranch ++ ")"),
  out_max     = -1              &= help "Maximum number of test cases; unbounded if negative (default: -1)",
  debug       = False           &= help "Debug output (default: false)"
  } &= help "Test program exhaustively"
  
rtest = RTest {
  proc_       = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file        = ""              &= typFile &= argPos 0,
  branch_max  = defaultBranch   &= help ("Maximum number of possibilities for each non-deterministic choice; " ++
                                         "unbounded if negative (default: " ++ show defaultBranch ++ ")"),
  seed        = Nothing         &= help "Seed for the random number generator" &= typ "NUM",
  out_max     = defaultRTC      &= help ("Number of test cases; unbounded if negative (default: " ++ show defaultRTC ++")"),
  debug       = False           &= help "Debug output (default: false)"
  } &= help "Test program on random inputs"
      
mode = cmdArgsMode $ modes [execute, test, rtest] &= 
  help "Boogie interpreter" &= 
  program programName &= 
  summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)
    
{- Interfacing internal modules -}

-- | Execute procedure proc_ from file
-- | and output either errors or the final values of global variables
executeFromFile :: String -> String -> Maybe Integer -> Bool -> Maybe Int -> Maybe Int -> Bool -> Bool -> Bool -> Bool -> Maybe Int -> Bool -> Bool -> IO ()
executeFromFile file proc_ branch_max random seed exec_max invalid nexec pass fail out_max summary debug = runOnFile printFinalState file
  where
    printFinalState p context = case M.lookup proc_ (ctxProcedures context) of
      Nothing -> printError (text "Cannot find procedure" <+> text proc_)
      Just _ -> do
        rGen <- case seed of
          Nothing -> getStdGen
          Just s -> return $ mkStdGen s      
        let generator = if random then randomGenerator rGen branch_max else exhaustiveGenerator branch_max
        let outs = (maybeTake out_max . filter keep . maybeTake exec_max) (outcomes p context generator)
        if summary
          then do
            let sum = testSessionSummary outs 
            print $ summaryDoc sum
            zipWithM_ (printOne "Failure") [0..] (sUniqueFailures sum)
          else if null outs
            then printAux $ text "No executions to display"
            else zipWithM_ (printOne "Execution") [0..] outs
    outcomes p context generator = if exec_max == Just 1 || (keepAll && out_max == Just 1)
      then [executeProgramDet p context branch_max proc_]
      else executeProgram p context generator branch_max proc_
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
      print $ testCaseSummary debug tc
      case tcFailure tc of
        Just err -> do
          printNewline
          printError $ runtimeFailureDoc debug err
          when debug (printSeparate $ finalStateDoc True tc)
        Nothing -> printSeparate $ finalStateDoc debug tc
    printOne title n tc = do
      when (n > 0) $ do printNewline; printNewline
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
  
printNewline = putStr "\n"  
  
printSeparate doc = when (not (isEmpty doc)) (do printNewline; print doc)
      
{- Helpers for testing internal functions -}      
      
-- | Harness for testing various internal functions
harness file = runOnFile printOutcome file
  where
    printOutcome p context = do
      let env = head (toList (execStateT (collectDefinitions p) (initEnv context (exhaustiveGenerator (Just defaultBranch)) (Just defaultBranch))))
      -- print $ memoryDoc True (env^.envMemory)
      putStr "DEFINITIONS:\n"
      print $ vsep (map fDoc (M.toList $ env ^. envDefinitions))
      putStr "CONSTRAINTS:\n"
      print $ vsep (map fDoc (M.toList $ env ^. envConstraints))
    fDoc (name, defs) = text name $+$ vsep (map defDoc defs)
    defDoc (FDef formals guard expr) = commaSep (map text formals) <+> text "GUARD:" <+> exprDoc guard <+> text "EXPR:" <+> exprDoc expr