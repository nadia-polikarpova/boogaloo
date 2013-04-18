{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Position
import qualified Language.Boogie.Parser as Parser (program)
import Language.Boogie.TypeChecker
import Language.Boogie.Pretty
import Language.Boogie.Environment
import Language.Boogie.Interpreter
import qualified Language.Boogie.TrivialSolver as Trivial
import qualified Language.Boogie.Z3.Solver as Z3
import System.Environment
import System.Console.CmdArgs
import System.Console.ANSI
import System.Random
import Data.Time.Calendar
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Stream
import Control.Lens hiding (Context, at)
import Text.ParserCombinators.Parsec (parse, parseFromFile)
import HtmlOutput

programName = "boogaloo"
versionName = "0.2"
releaseDate = fromGregorian 2013 2 5

-- | Execute or test a Boogie program, according to command-line arguments
main = do
  res <- cmdArgsRun $ mode
  case res of
    Exec file proc_ bound random seed btmax invalid nexec pass fail outMax sum debug format -> 
      executeFromFile file proc_ (natToMaybe bound) random seed btmax invalid nexec pass fail (natToMaybe outMax) sum debug format
    Test file proc_ bound outMax debug format ->
      executeFromFile file proc_ (natToMaybe bound) False Nothing Nothing True True True True (natToMaybe outMax) True debug format
    RTest file proc_ bound seed outMax debug format ->
      executeFromFile file proc_ (natToMaybe bound) True seed Nothing True True True True (natToMaybe outMax) True debug format      
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
        debug :: Bool,
        format :: OutputFormat
      }
    | Test { 
        file :: String, 
        proc_ :: String,
        branch_max :: Integer,
        out_max :: Int, 
        debug :: Bool,
        format :: OutputFormat
      }
    | RTest { 
        file :: String, 
        proc_ :: String,
        branch_max :: Integer,
        seed :: Maybe Int,
        out_max :: Int, 
        debug :: Bool,
        format :: OutputFormat
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
  out_max     = 1               &= help "Maximum number of executions to display; unbounded if negative (default: 1)",
  summary_    = False           &= help "Only print a summary of all executions and a list of unique failures (default: false)" &= name "S",
  debug       = False           &= help "Debug output (default: false)",
  format      = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")")
  } &= auto &= help "Execute program"
  
test = Test {
  proc_       = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file        = ""              &= typFile &= argPos 0,
  branch_max  = defaultExBranch &= help ("Maximum number of possibilities for each non-deterministic choice; " ++
                                         "unbounded if negative (default: " ++ show defaultExBranch ++ ")"),
  out_max     = -1              &= help "Maximum number of test cases; unbounded if negative (default: -1)",
  debug       = False           &= help "Debug output (default: false)",
  format      = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")")
  } &= help "Test program exhaustively"
  
rtest = RTest {
  proc_       = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file        = ""              &= typFile &= argPos 0,
  branch_max  = defaultBranch   &= help ("Maximum number of possibilities for each non-deterministic choice; " ++
                                         "unbounded if negative (default: " ++ show defaultBranch ++ ")"),
  seed        = Nothing         &= help "Seed for the random number generator" &= typ "NUM",
  out_max     = defaultRTC      &= help ("Number of test cases; unbounded if negative (default: " ++ show defaultRTC ++")"),
  debug       = False           &= help "Debug output (default: false)",
  format      = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")")
  } &= help "Test program on random inputs"
      
mode = cmdArgsMode $ modes [execute, test, rtest] &= 
  help "Boogie interpreter" &= 
  program programName &= 
  summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)
    
{- Interfacing internal modules -}

-- | Execute procedure proc_ from file
-- | and output either errors or the final values of global variables
executeFromFile :: String -> String -> Maybe Integer -> Bool -> Maybe Int -> Maybe Int -> Bool -> Bool -> Bool -> Bool -> Maybe Int -> Bool -> Bool -> OutputFormat -> IO ()
executeFromFile file proc_ branch_max random seed exec_max invalid nexec pass fail out_max summary debug format = runOnFile printFinalState file format
  where
    printFinalState p context = case M.lookup proc_ (ctxProcedures context) of
      Nothing -> printDoc format $ errorDoc (text "Cannot find procedure" <+> text proc_)
      Just _ -> do
        rGen <- case seed of
          Nothing -> getStdGen
          Just s -> return $ mkStdGen s      
        -- let solver = Z3.solve
        let solver = Trivial.solve
        let outs = maybeTake out_max . filter keep . maybeTake exec_max . toList $ executeProgram p context solver proc_
        if summary
          then printDoc format $ sessionSummaryDoc debug outs
          else if null outs
            then printDoc format $ auxDoc (text "No executions to display")
            else mapM_ (printDoc format) $ zipWith outcomeDoc [0..] outs
    keepAll = invalid && nexec && pass && fail
    maybeTake mLimit = case mLimit of
      Nothing -> id
      Just n -> take n
    keep tc = 
      (if invalid then True else (not . isInvalid) tc) &&
      (if nexec then True else (not . isNonexecutable) tc) &&
      (if pass then True else (not . isPass) tc) &&
      (if fail then True else (not . isFail) tc)
    outcomeDoc n tc = option (n > 0) linebreak <> testCaseDoc debug "Execution" n tc

-- | Parse file, type-check the resulting program, then execute command on the resulting program and type context
runOnFile :: (Program -> Context -> IO ()) -> String -> OutputFormat -> IO ()      
runOnFile command file format = do 
  parseResult <- parseFromFile Parser.program file
  case parseResult of
    Left parseErr -> printDoc format $ errorDoc $ text (show parseErr)
    Right p -> case typeCheckProgram p of
      Left typeErrs -> printDoc format $ errorDoc $ typeErrorsDoc typeErrs
      Right context -> command p context
      
{- Output -}

-- | Output format
data OutputFormat = Plain -- ^ Plain text
  | Ansi -- ^ Text with ANSI-terminal special characters
  | Html -- ^ HTML
  deriving (Typeable, Data, Eq, Show)
  
defaultFormat = Ansi  
    
-- | 'printDoc' @format doc@ : print @doc@ to the console using @format@
printDoc :: OutputFormat -> Doc -> IO()
printDoc Plain doc = putDoc (plain doc) >> putStr "\n"
printDoc Ansi doc = putDoc doc >> putStr "\n"
printDoc Html doc = putStr (showDocHtml (renderPretty 0.4 100 doc))   
      
{- Helpers for testing internal functions -}      
      
-- | Harness for testing various internal functions
-- harness file = runOnFile printOutcome file defaultFormat
  -- where
    -- printOutcome p context = do
      -- let env = head (toList (execStateT (runErrorT (preprocess p)) (initEnv context (exhaustiveGenerator (Just defaultBranch)) (Just defaultBranch))))
      -- -- print $ memoryDoc True (env^.envMemory)
      -- print $ nameConstraintsDoc (env ^. envConstraints . symGlobals)
