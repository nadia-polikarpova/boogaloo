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
import Control.Monad.Logic
import Text.ParserCombinators.Parsec (parse, parseFromFile)
import HtmlOutput

programName = "boogaloo"
versionName = "0.3"
releaseDate = fromGregorian 2013 5 29

-- | Execute or test a Boogie program, according to command-line arguments
main = do
  res <- cmdArgsRun $ mode
  case res of
    Exec file proc_ backtrack solver minimize concretize per_path unroll exec invalid nexec pass fail out sum debug format -> 
      executeFromFile file proc_ 
                      solver minimize concretize (natToMaybe unroll) 
                      backtrack (natToMaybe per_path) (natToMaybe exec) 
                      invalid nexec pass fail (natToMaybe out)
                      sum debug format
    Test file proc_ backtrack solver minimize concretize unroll exec out debug format ->
      executeFromFile file proc_ 
                      solver minimize concretize (natToMaybe unroll) 
                      backtrack (Just $ if concretize then defaultPerPath else 1) (natToMaybe exec) 
                      False False False True (natToMaybe out) 
                      False debug format
  where
    natToMaybe n
      | n >= 0      = Just n
      | otherwise   = Nothing

{- Command line arguments -}

data CommandLineArgs
    = Exec { 
        file :: String, 
        proc_ :: Maybe String,
        backtrack :: BacktrackStrategy,
        solver :: ConstraintSolver,
        minimize :: Bool,
        concretize :: Bool,
        per_path :: Int,
        unroll :: Int,
        exec :: Int, 
        invalid :: Bool, 
        nexec :: Bool,
        pass :: Bool,
        fail_ :: Bool,
        out :: Int, 
        summary_ :: Bool,
        debug :: Bool,
        format :: OutputFormat
      }
    | Test { 
        file :: String, 
        proc_ :: Maybe String,
        backtrack :: BacktrackStrategy,
        solver :: ConstraintSolver,
        minimize :: Bool,
        concretize :: Bool,
        unroll :: Int,
        exec :: Int, 
        out :: Int, 
        debug :: Bool,
        format :: OutputFormat
      }
      deriving (Data, Typeable, Show, Eq)
      
-- | Available solvers      
data ConstraintSolver = 
    Exhaustive  -- ^ Trivial solver that exhaustively enumerates solutions
  | Z3          -- ^ Solver based on Z3
  deriving (Typeable, Data, Eq, Show)
  
-- | Backtracking strategies
data BacktrackStrategy = 
    DF    -- ^ Depth-first backtracking (always reconsider the choice made last, until not possible)
  | Fair  -- ^ Fair backtracking (reconsider any choice made before)
  deriving (Typeable, Data, Eq, Show)  
  
-- | Default constraint solver
defaultSolver = Z3  

-- | Default backtracking strategy
defaultBT = DF

-- | Default solutions per path
defaultPerPath = 128

-- | Default number of test cases for testing
defaultTCCount = 2048

execute = Exec {
  proc_       = Nothing         &= help "Program entry point (default: Main or the only procedure in a file)" &= typ "PROCEDURE" &= name "p",
  file        = ""              &= typFile &= argPos 0,
  backtrack   = defaultBT       &= help ("Backtracking strategy: DF (depth-first) or Fair (default: " ++ show defaultBT ++ ")"),
  solver      = defaultSolver   &= help ("Constraint solver: Exhaustive or Z3 (default: " ++ show defaultSolver ++ ")"),
  minimize    = True            &= help ("Should solutions be minimized? (default: True)"),
  concretize  = True            &= help ("Concretize in the middle of an execution? (default: True)"),
  per_path    = defaultPerPath  &= help ("Maximum number of solutions to try per path; " ++
                                        "unbounded if negative (default: " ++ show defaultPerPath ++ ")") &= name "n",
  unroll      = -1              &= help ("Maximum number of unrolls for a loop or a recursive definition; unbounded if negative (default: -1)"),
  exec        = -1              &= help ("Maximum number of executions to try; unbounded if negative (default: -1)"),
  invalid     = False           &= help "Display invalid executions (default: false)" &= name "I",
  nexec       = True            &= help "Display executions that cannot be carried out completely (default: true)" &= name "N",
  pass        = True            &= help "Display passing executions (default: true)" &= name "P",
  fail_       = True            &= help "Display failing executions (default: true)" &= name "F",
  out         = 1               &= help "Maximum number of executions to display; unbounded if negative (default: 1)",
  summary_    = False           &= help "Only print a summary of all executions and a list of unique failures (default: false)" &= name "S",
  debug       = False           &= help "Debug output (default: false)",
  format      = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")")
  } &= auto &= help "Execute program"
  
test = Test {
  proc_       = Nothing         &= help "Program entry point (default: Main or the only procedure in a file)" &= typ "PROCEDURE" &= name "p",
  file        = ""              &= typFile &= argPos 0,
  backtrack   = defaultBT       &= help ("Backtracking strategy: DF (depth-first) or Fair (default: " ++ show defaultBT ++ ")"),
  solver      = defaultSolver   &= help ("Constraint solver: Exhaustive or Z3 (default: " ++ show defaultSolver ++ ")"),
  minimize    = True            &= help ("Should solutions be minimized? (default: True)"),
  concretize  = True            &= help ("Concretize in the middle of an execution? (default: True)"),
  unroll      = -1              &= help ("Maximum number of unrolls for a loop or a recursive definition; unbounded if negative (default: -1)"),  
  exec        = defaultTCCount  &= help ("Maximum number of executions to try (default: " ++ show defaultTCCount ++ ")"),
  out         = 1               &= help "Maximum number of faults to look for; unbounded if negative (default: 1)",
  debug       = False           &= help "Debug output (default: false)",
  format      = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")")
  } &= help "Test program exhaustively until an error is found"
      
mode = cmdArgsMode $ modes [execute, test] &= 
  help "Boogie interpreter" &= 
  program programName &= 
  summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)
    
{- Interfacing internal modules -}

type Interpreter = Program -> Context -> Id -> [TestCase]

-- | Execute procedure mProc from file
-- | and output either errors or the final values of global variables
executeFromFile :: String -> Maybe String ->
                   ConstraintSolver -> Bool -> Bool -> Maybe Int ->
                   BacktrackStrategy -> Maybe Int -> Maybe Int ->
                   Bool -> Bool -> Bool -> Bool -> Maybe Int ->
                   Bool -> Bool -> OutputFormat ->
                   IO ()
executeFromFile file mProc  -- Source options
                solverId minimize concretize unroll_max -- Constraint solving options
                backtrack branch_max exec_max -- Backtracking options 
                invalid nexec pass fail out_max -- Execution filtering
                summary debug format -- Output format options 
  = runOnFile printFinalState file format
  where
    printFinalState p context = let proc_ = entryPoint context 
      in case M.lookup proc_ (ctxProcedures context) of
        Nothing -> printDoc format $ errorDoc (text "Cannot find procedure" <+> text proc_)
        Just _ -> let int = interpreter backtrack solverId minimize concretize pass branch_max unroll_max
                      outs = maybeTake out_max . filter keep . maybeTake exec_max $ int p context proc_   
          in if summary
                then printDoc format $ sessionSummaryDoc debug outs
                else if null outs
                  then printDoc format $ auxDoc (text "No executions to display")
                  else mapM_ (printDoc format) $ zipWith outcomeDoc [0..] outs
    entryPoint context = case mProc of
      Just proc_ -> proc_
      Nothing -> if M.size (ctxProcedures context) == 1
        then fst $ M.findMin $ ctxProcedures context
        else "Main"
    maybeTake mLimit = case mLimit of
      Nothing -> id
      Just n -> take n
    keep tc = 
      (if invalid then True else (not . isInvalid) tc) &&
      (if nexec then True else (not . isNonexecutable) tc) &&
      (if pass then True else (not . isPass) tc) &&
      (if fail then True else (not . isFail) tc)
    outcomeDoc n tc = option (n > 0) linebreak <> testCaseDoc debug "Execution" n tc
    
interpreter :: BacktrackStrategy -> ConstraintSolver -> Bool -> Bool -> Bool -> Maybe Int -> Maybe Int -> Interpreter
interpreter DF solverId minimize concretize solvePassing branch_max unroll_max p context proc_ = toList $ executeProgram p context solver unroll_max concretize solvePassing generator proc_
  where
    solver :: Solver Logic
    solver = case solverId of
      Exhaustive -> Trivial.solver branch_max
      Z3 -> Z3.solver minimize branch_max
    generator = exhaustiveGenerator Nothing
interpreter Fair solverId minimize concretize solvePassing branch_max unroll_max p context proc_ = toList $ executeProgram p context solver unroll_max concretize solvePassing generator proc_
  where
    solver :: Solver Stream
    solver = case solverId of
      Exhaustive -> Trivial.solver branch_max
      Z3 -> Z3.solver minimize branch_max
    generator = exhaustiveGenerator Nothing

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
