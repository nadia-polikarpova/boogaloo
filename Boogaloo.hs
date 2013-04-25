{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Position
import qualified Language.Boogie.Parser as Parser (program)
import Language.Boogie.TypeChecker
import Language.Boogie.Pretty
import Language.Boogie.Interpreter
import Language.Boogie.Solver
import qualified Language.Boogie.TrivialSolver as Trivial
import qualified Language.Boogie.Z3.Solver as Z3
import Language.Boogie.Generator
import System.Environment
import System.Console.CmdArgs
import System.Console.ANSI
import Data.Time.Calendar
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Stream
import Text.ParserCombinators.Parsec (parse, parseFromFile)
import HtmlOutput

programName = "boogaloo"
versionName = "0.2"
releaseDate = fromGregorian 2013 2 5

-- | Execute or test a Boogie program, according to command-line arguments
main = do
  res <- cmdArgsRun $ mode
  case res of
    Exec file proc_ solver minimize bound exec_max invalid nexec pass fail outMax sum debug format -> 
      executeFromFile file proc_ solver minimize (natToMaybe bound) (natToMaybe exec_max) invalid nexec pass fail (natToMaybe outMax) sum debug format
    Test file proc_ solver minimize exec_max outMax debug format ->
      executeFromFile file proc_ solver minimize (Just 1) (natToMaybe exec_max) False False False True (natToMaybe outMax) False debug format
  where
    natToMaybe n
      | n >= 0      = Just n
      | otherwise   = Nothing

{- Command line arguments -}

data CommandLineArgs
    = Exec { 
        file :: String, 
        proc_ :: String,
        solver :: ConstraintSolver,
        minimize :: Bool,
        branch_max :: Int,
        exec_max :: Int, 
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
        solver :: ConstraintSolver,
        minimize :: Bool,
        exec_max :: Int, 
        out_max :: Int, 
        debug :: Bool,
        format :: OutputFormat
      }
      deriving (Data, Typeable, Show, Eq)
      
-- | Available solvers      
data ConstraintSolver = 
    Exhaustive  -- ^ Trivial solver that exhaustively enumerates solutions
  | Z3          -- ^ Solver based on Z3
  deriving (Typeable, Data, Eq, Show)      
  
-- | Default constraint solver
defaultSolver = Z3  

-- | Default branching
defaultBranch = 8

-- | Default number of test cases for testing
defaultTCCount = 1024

execute = Exec {
  proc_       = "Main"          &= help "Program entry point (default: Main)" &= typ "PROCEDURE",
  file        = ""              &= typFile &= argPos 0,
  solver      = defaultSolver   &= help ("Constraint solver: Exhaustive or Z3 (default: " ++ show defaultSolver ++ ")"),
  minimize    = True            &= help ("Should solutions be minimized? (default: True)"),
  branch_max  = defaultBranch   &= help ("Maximum number of solutions to try per path; " ++
                                       "unbounded if negative (default: " ++ show defaultBranch ++ ")"),
  exec_max    = -1              &= help ("Maximum number of executions to try; unbounded if negative (default: -1)"),
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
  solver      = defaultSolver   &= help ("Constraint solver: Exhaustive or Z3 (default: " ++ show defaultSolver ++ ")"),
  minimize    = True            &= help ("Should solutions be minimized? (default: True)"),
  exec_max    = defaultTCCount  &= help ("Maximum number of executions to try (default: " ++ show defaultTCCount ++ ")"),
  out_max     = 1               &= help "Maximum number of faults to look for; unbounded if negative (default: 1)",
  debug       = False           &= help "Debug output (default: false)",
  format      = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")")
  } &= help "Test program exhaustively until an error is found"
      
mode = cmdArgsMode $ modes [execute, test] &= 
  help "Boogie interpreter" &= 
  program programName &= 
  summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)
    
{- Interfacing internal modules -}

-- | Execute procedure proc_ from file
-- | and output either errors or the final values of global variables
executeFromFile :: String -> String -> ConstraintSolver -> Bool -> Maybe Int -> Maybe Int -> Bool -> Bool -> Bool -> Bool -> Maybe Int -> Bool -> Bool -> OutputFormat -> IO ()
executeFromFile file proc_ solver minimize branch_max exec_max invalid nexec pass fail out_max summary debug format = runOnFile printFinalState file format
  where
    printFinalState p context = case M.lookup proc_ (ctxProcedures context) of
      Nothing -> printDoc format $ errorDoc (text "Cannot find procedure" <+> text proc_)
      Just _ -> let outs = maybeTake out_max . filter keep . maybeTake exec_max . toList $ executeProgram p context solve generator proc_
        in if summary
              then printDoc format $ sessionSummaryDoc debug outs
              else if null outs
                then printDoc format $ auxDoc (text "No executions to display")
                else mapM_ (printDoc format) $ zipWith outcomeDoc [0..] outs
    solve :: Solver Stream 
    solve = case solver of
      Exhaustive -> Trivial.solve branch_max
      Z3 -> Z3.solve True minimize branch_max
    generator = exhaustiveGenerator Nothing
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
