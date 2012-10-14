module Tester where

import AST
import Util
import Position
import TypeChecker
import Tokens
import PrettyPrinter
import Interpreter
import DataFlow
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
testProgram :: TestSettings -> Program -> Context -> [Id] -> [TestCase]
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
            
{- Testing session parameters -}

-- | Settings for test input generation
data TestSettings = TestSettings {
  tsIntRange :: [Integer],      -- Range of input values for integer variables
  tsGenericTypeRange :: [Type], -- Range of instances for a type parameter of a generic procedure under test 
  tsMapTypeRange :: [Type]      -- Range of instances for a type parameter of a polymorphic map
}

defaultSettings c = TestSettings {
  tsIntRange = [-1..1],
  tsGenericTypeRange = [BoolType],
  tsMapTypeRange = [BoolType, IntType] ++ [Instance name [] | name <- M.keys (M.filter (== 0) (ctxTypeConstructors c))]
}

-- | Executions that have access to testing session parameters
type TestSession a = State (TestSettings, Environment) a
        
{- Reporting results -}        

-- | Outcome of a test case        
data Outcome = Pass | Fail RuntimeError | Invalid RuntimeError

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
}

testCaseDoc :: TestCase -> Doc
testCaseDoc (TestCase procName liveIns liveGlobals input outcome) = text procName <> 
  parens (commaSep (zipWith argDoc (liveIns ++ (map ("var " ++) liveGlobals)) input)) <+>
  outcomeDoc outcome
  where
    argDoc name val = text name <+> text "=" <+> valueDoc val

instance Show TestCase where show tc = show (testCaseDoc tc)

{- Test execution -}

-- | Test implementation def of procedure sig on all inputs prescribed by the testing strategy
testImplementation :: PSig -> PDef -> TestSession [TestCase] 
testImplementation sig def = do
  let paramTypes = map itwType (psigParams sig)
  tc <- gets (envTypeContext . snd)
  typeRange <- gets (tsGenericTypeRange . fst)
  -- all types the procedure signature should be instantiated with:
  let typeInputs = generateInputTypes typeRange tc { ctxTypeVars = psigTypeVars sig } paramTypes  
  concat <$> mapM typeTestCase typeInputs
  where
    -- | Execute procedure instantiated with typeInputs on all value inputs
    typeTestCase :: [Type] -> TestSession [TestCase]
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
      let (liveIns, liveGlobals) = liveInputVariables def
      let livePositions = map (fromJust . (`elemIndex` pdefIns def)) liveIns 
      let liveActualIns = map localName livePositions
      let liveGlobalVars = filter (`M.member` ctxGlobals tc) liveGlobals
      let inputVars = liveActualIns ++ liveGlobalVars
            
      -- types of input variables
      let inTypes = map (typeInputs !!) livePositions ++ map (ctxGlobals tc !) liveGlobalVars      
      
      let execTestCase input = changeState snd (mapSnd . const) $ testCase inParams outParams inputVars input
      let reportTestCase input = TestCase (psigName sig) liveIns liveGlobalVars input <$> execTestCase input
      -- all inputs the procedure should be tested on:
      inputs <- changeState fst (mapFst . const) $ listMapM (generateInputValueM tc) inTypes
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
    
-- | The version was not using state, but was using the list monad:
-- generateInputValue :: TestSettings -> Context -> Type -> [Value]
-- generateInputValue _ _ BoolType = map BoolValue [False, True]
-- generateInputValue settings _ IntType = map IntValue (tsIntRange settings)
-- generateInputValue settings c (MapType tv domains range) =
  -- let polyTypes = generateInputTypes (tsMapTypeRange settings) c { ctxTypeVars = tv } (range : domains) in
  -- -- A polymorphic map is a union of monomorphic maps with all possible instantiations for type variables
  -- map MapValue (M.unions <$> mapM monomorphicMap polyTypes)
  -- where 
    -- monomorphicMap (range : domains) = do  
      -- let args = forM domains (generateInputValue settings c)
      -- r <- replicateM (length args) (generateInputValue settings c range)
      -- return $ M.fromList (zip args r)
-- generateInputValue settings _ (Instance _ _) = map CustomValue (tsIntRange settings)

-- | generateInputValue c t: all values of type t in context c          
generateInputValueM :: Context -> Type -> State TestSettings [Value]
generateInputValueM _ BoolType = return $ map BoolValue [False, True]
generateInputValueM _ IntType = do
  settings <- get
  return $ map IntValue (tsIntRange settings)
generateInputValueM c (MapType tv domains range) = do
  typeRange <- gets tsMapTypeRange
  let polyTypes = generateInputTypes typeRange c { ctxTypeVars = tv } (range : domains)
  -- A polymorphic map is a union of monomorphic maps with all possible instantiations for type variables
  maps <- listMapM monomorphicMap polyTypes
  return $ map (MapValue . M.unions) maps
  where
    monomorphicMap :: [Type] -> State TestSettings [Map [Value] Value]
    monomorphicMap (range : domains) = do 
      args <- listMapM (generateInputValueM c) domains
      rets <- listMapM (generateInputValueM c) (replicate (length args) range)
      return $ map (\r -> M.fromList (zip args r)) rets
generateInputValueM _ (Instance _ _) = do
  settings <- get
  return $ map IntValue (tsIntRange settings)

-- | All instantiations of types ts in context c, with a range of instances for a single type variables range 
generateInputTypes :: [Type] -> Context -> [Type] -> [[Type]]
generateInputTypes range c ts = do
  let freeVars = filter (\x -> any (x `isFreeIn`) ts) (ctxTypeVars c)
  actuals <- replicateM (length freeVars) range
  let binding = M.fromList (zip freeVars actuals)
  return $ map (typeSubst binding) ts
  