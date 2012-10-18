module Tester where

import AST
import Util
import Position
import TypeChecker
import Tokens
import PrettyPrinter
import Interpreter
import DataFlow
import System.Random
import Data.Maybe
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Error
import Control.Applicative
import Control.Monad.State
import Text.PrettyPrint

{- Interface -}
    
-- | Test all implementations of all procedures procNames from program p in type context tc;
-- | requires that all procNames exist in context
testProgram :: TestSettings s => s -> Program -> Context -> [Id] -> [TestCase]
testProgram settings p tc procNames = evalState testExecution (settings, initEnvironment)
  where
    initEnvironment = emptyEnv { envTypeContext = tc }
    testExecution = do
      changeState snd (mapSnd . const) $ collectDefinitions p
      concat <$> forM procNames testProcedure
    -- | Test all implementations of procedure name
    testProcedure name = do
      sig <- gets (procSig name . envTypeContext . snd) 
      defs <- gets (lookupProcedure name . snd)
      concat <$> forM defs (testImplementation sig)
      
-- | Summary of a set of test cases   
testSessionSummary :: [TestCase] -> Summary
testSessionSummary tcs = let 
  passing = [ x | x@(TestCase _ _ _ _ Pass)         <- tcs ]
  failing = [ x | x@(TestCase _ _ _ _ (Fail _))     <- tcs ]
  invalid = [ x | x@(TestCase _ _ _ _ (Invalid _))  <- tcs ]
  in Summary {
    sPassCount = length passing,
    sFailCount = length failing,
    sInvalidCount = length invalid,  
    sUniqueFailures = nubBy equivalent failing
  }
            
{- Testing session parameters -}

class TestSettings s where
  -- | Generate all input values for an integer variable
  generateIntInput :: State s [Integer]
  -- | Generate all input values for a boolean variable
  generateBoolInput :: State s [Bool]
  -- | Combine input values for several variables  
  combineInputs :: (a -> State s [b]) -> [a] -> State s [[b]]
  -- | Settings for generating map domains (always exhaustive)
  mapDomainSettings :: s -> ExhaustiveSettings
  -- | Range of instances for a type parameter of a generic procedure under test 
  genericTypeRange :: s -> [Type]
  -- | Range of instances for a type parameter of a polymorphic map
  mapTypeRange :: s -> [Type]
  
data ExhaustiveSettings = ExhaustiveSettings {
  esIntRange :: [Integer],            -- Input range for an integer variable
  esIntMapDomainRange :: [Integer],   -- Input range for an integer map domain
  esGenericTypeRange :: [Type],       -- Range of instances for a type parameter of a generic procedure under test 
  esMapTypeRange :: [Type]            -- Range of instances for a type parameter of a polymorphic map
}

instance TestSettings ExhaustiveSettings where
  generateIntInput = gets esIntRange                            -- Return all integers within limits  
  generateBoolInput = return [False, True]                      -- Return both booleans      
  combineInputs genOne args = sequence <$> mapM genOne args     -- Use all combinations of inputs for each variable   
  mapDomainSettings s = s { esIntRange = esIntMapDomainRange s }  
  genericTypeRange = esGenericTypeRange
  mapTypeRange = esMapTypeRange
  
defaultExhaustiveSettings c = ExhaustiveSettings {
  esIntRange = [-1..1],
  esIntMapDomainRange = [0..2],
  esGenericTypeRange = [BoolType],
  esMapTypeRange = [BoolType, IntType] ++ [Instance name [] | name <- M.keys (M.filter (== 0) (ctxTypeConstructors c))]
}

data RandomSettings = RandomSettings {
  rsRandomGen :: StdGen,              -- Random number generator
  rsCount :: Int,                     -- Number of test cases to be generated (currently per type in rsGenericTypeRange, if the procedure under test is generic)
  rsIntLimits :: (Integer, Integer),  -- Lower and upper bound for integer inputs
  rsIntMapDomainRange :: [Integer],   -- Input range for an integer map domain
  rsGenericTypeRange :: [Type],       -- Range of instances for a type parameter of a generic procedure under test 
  rsMapTypeRange :: [Type]            -- Range of instances for a type parameter of a polymorphic map
}

setRandomGen gen rs = rs { rsRandomGen = gen }

instance TestSettings RandomSettings where
  -- | Generate rsCount random values within limits
  generateIntInput = do
    randomGen <- gets rsRandomGen
    limits <- gets rsIntLimits
    n <- gets rsCount
    changeState rsRandomGen setRandomGen $ replicateM n (state (randomR limits))
    
  -- | Generate rsCount random values within limits  
  generateBoolInput = do
    randomGen <- gets rsRandomGen
    n <- gets rsCount
    changeState rsRandomGen setRandomGen $ replicateM n (state random)    
  
  -- | Generate rsCount random tuples of values
  combineInputs genOne args = transpose <$> mapM genOne args
  
  -- | Integer map domains are intervals [0..rsIntMapDomainSize s - 1]  
  mapDomainSettings s = ExhaustiveSettings { 
    esIntRange = rsIntMapDomainRange s,
    esIntMapDomainRange = rsIntMapDomainRange s,
    esGenericTypeRange = rsGenericTypeRange s,
    esMapTypeRange = rsMapTypeRange s
    }  
      
  genericTypeRange = rsGenericTypeRange
  mapTypeRange = rsMapTypeRange
  
defaultRandomSettings c randomGen = RandomSettings {
  rsRandomGen = randomGen,
  rsCount = 10,
  rsIntLimits = (-32, 32),
  rsIntMapDomainRange = [0..3],
  rsGenericTypeRange = [BoolType],
  rsMapTypeRange = [BoolType, IntType] ++ [Instance name [] | name <- M.keys (M.filter (== 0) (ctxTypeConstructors c))]
}

-- | Executions that have access to testing session parameters
type TestSession s a = State (s, Environment) a
        
{- Reporting results -}        

-- | Outcome of a test case        
data Outcome = Pass | Fail RuntimeError | Invalid RuntimeError
  deriving Eq

outcomeDoc :: Outcome -> Doc
outcomeDoc Pass = text "passed"
outcomeDoc (Fail err) = text "failed with: " <+> runtimeErrorDoc err
outcomeDoc (Invalid err) = text "invalid because: " <+> runtimeErrorDoc err

instance Show Outcome where show o = show (outcomeDoc o)

-- | Description of a test case
data TestCase = TestCase {
  tcProcedure :: Id,      -- Procedure under test
  tcLiveIns :: [Id],      -- Input parameters for which an input value was generated
  tcLiveGlobals :: [Id],  -- Global variables for which an input value was generated
  tcInput :: [Value],     -- Values for in-parameters
  tcOutcome :: Outcome    -- Outcome
} deriving Eq

testCaseDoc :: TestCase -> Doc
testCaseDoc (TestCase procName liveIns liveGlobals input outcome) = text procName <> 
  parens (commaSep (zipWith argDoc (liveIns ++ (map ("var " ++) liveGlobals)) input)) <+>
  outcomeDoc outcome
  where
    argDoc name val = text name <+> text "=" <+> valueDoc val

instance Show TestCase where show tc = show (testCaseDoc tc)

-- | Test cases are considered equivalent from a user perspective
-- | if they are testing the same procedure and result in the same outcome
equivalent tc1 tc2 = tcProcedure tc1 == tcProcedure tc2 && tcOutcome tc1 == tcOutcome tc2      

-- | Test session summary
data Summary = Summary {
  sPassCount :: Int,            -- Number of passing test cases
  sFailCount :: Int,            -- Number of failing test cases
  sInvalidCount :: Int,         -- Number of invalid test cases
  sUniqueFailures :: [TestCase] -- Unique failing test cases
}

totalCount s = sPassCount s + sFailCount s + sInvalidCount s

summaryDoc :: Summary -> Doc
summaryDoc summary = 
  text "Test cases:" <+> int (totalCount summary) $+$
  text "Passed:" <+> int (sPassCount summary) $+$
  text "Invalid:" <+> int (sInvalidCount summary) $+$
  text "Failed:" <+> int (sFailCount summary) <+> parens (int (length (sUniqueFailures summary)) <+> text "unique") $+$
  vsep (map testCaseDoc (sUniqueFailures summary))
  
instance Show Summary where show s = show (summaryDoc s)  
    
{- Test execution -}

-- | Test implementation def of procedure sig on all inputs prescribed by the testing strategy
testImplementation :: TestSettings s => PSig -> PDef -> TestSession s [TestCase] 
testImplementation sig def = do
  let paramTypes = map itwType (psigParams sig)
  tc <- gets (envTypeContext . snd)
  typeRange <- gets (genericTypeRange . fst)
  -- all types the procedure signature should be instantiated with:
  let typeInputs = generateInputTypes typeRange tc { ctxTypeVars = psigTypeVars sig } paramTypes  
  concat <$> mapM typeTestCase typeInputs
  where
    -- | Execute procedure instantiated with typeInputs on all value inputs
    typeTestCase :: TestSettings s => [Type] -> TestSession s [TestCase]
    typeTestCase typeInputs = do
      -- fresh name for a parameter at position index; to be used as actual parameter
      let localName index = [nonIdChar] ++ show index
      let localNames = map localName [0..length (psigParams sig) - 1]
      -- declare local variables localNames with appropriate types:
      modify $ mapSnd (modifyTypeContext (`setLocals` (M.fromList $ zip localNames typeInputs)))
      tc <- gets (envTypeContext . snd)
      
      -- names of actual in- and out-parameters
      let (inParams, outParams) = splitAt (length (psigArgs sig)) localNames      
      
      -- names of input variables (variables for which input values are generated);
      -- input variables can be either in-parameters or global variables 
      let (liveIns, liveGlobals) = liveInputVariables sig def
      let livePositions = map (fromJust . (`elemIndex` pdefIns def)) liveIns 
      let liveActualIns = map localName livePositions
      let liveGlobalVars = filter (`M.member` ctxGlobals tc) liveGlobals
      let inputVars = liveActualIns ++ liveGlobalVars
            
      -- types of input variables
      let inTypes = map (typeInputs !!) livePositions ++ map (ctxGlobals tc !) liveGlobalVars      
      
      let execTestCase input = changeState snd (mapSnd . const) $ testCase inParams outParams inputVars input
      let reportTestCase input = TestCase (psigName sig) liveIns liveGlobalVars input <$> execTestCase input
      -- all inputs the procedure should be tested on:
      let genInputs = combineInputs (generateInputValue tc) inTypes
      inputs <- changeState fst (mapFst . const) genInputs 
      mapM reportTestCase inputs
    -- | Assign inputVals to inputVars, and execute procedure with actual in-parameter variables inParams and actual out-parameter variables outParams;
    -- | inputVars contain some inParams and some globals variables
    testCase :: [Id] -> [Id] -> [Id] -> [Value] -> SafeExecution Outcome
    testCase inParams outParams inputVars inputVals = do
      setAll inputVars inputVals
      let inExpr = map (gen . Var) inParams
      let outExpr = map (gen . Var) outParams
      execSafely (execProcedure (assumePreconditions sig) def inExpr outExpr >> return Pass) failureReport
    -- | Test case outcome in case of a runtime error err
    failureReport err = case rteInfo err of
      AssumeViolation _ _ -> return $ Invalid err
      _ -> return $ Fail err
            
{- Input generation -}
    
-- | generateInputValue c t: generate all values of type t in context c          
generateInputValue :: TestSettings s => Context -> Type -> State s [Value]
generateInputValue _ BoolType = map BoolValue <$> generateBoolInput
generateInputValue _ IntType = map IntValue <$> generateIntInput
generateInputValue c (MapType tv domains range) = do
  typeRange <- gets mapTypeRange
  let polyTypes = generateInputTypes typeRange c { ctxTypeVars = tv } (range : domains)
  -- A polymorphic map is a union of monomorphic maps with all possible instantiations for type variables:
  maps <- combineInputs monomorphicMap polyTypes
  return $ map (MapValue . M.unions) maps
  where
    monomorphicMap (range : domains) = do 
      -- Domain is always generated deterministically: 
      args <- withLocalState mapDomainSettings (combineInputs (generateInputValue c) domains)
      rets <- combineInputs (generateInputValue c) (replicate (length args) range)
      return $ map (\r -> M.fromList (zip args r)) rets
generateInputValue _ (Instance _ _) = map CustomValue <$> generateIntInput

-- | All instantiations of types ts in context c, with a range of instances for a single type variables range 
generateInputTypes :: [Type] -> Context -> [Type] -> [[Type]]
generateInputTypes range c ts = do
  let freeVars = filter (\x -> any (x `isFreeIn`) ts) (ctxTypeVars c)
  actuals <- replicateM (length freeVars) range
  let binding = M.fromList (zip freeVars actuals)
  return $ map (typeSubst binding) ts
  