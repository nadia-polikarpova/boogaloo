module Tester where

import AST
import Util
import Position
import TypeChecker
import Tokens
import PrettyPrinter
import Interpreter
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
testProgram settings p tc procNames = evalState programExecution initEnvironment
  where
    initEnvironment = emptyEnv { envTypeContext = tc }
    programExecution = do
      collectDefinitions p      
      concat <$> forM procNames testProcedure
    -- | Test all implementations of procedure name
    testProcedure name = do
      sig <- gets (procSig name . envTypeContext) 
      defs <- gets (lookupProcedure name)
      concat <$> forM defs (testImplementation settings sig)
      
{- Testing session parameters -}

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
  tcProcedure :: Id,    -- Procedure under test
  tcInput :: [Value],   -- Values for in-parameters
  tcOutcome :: Outcome  -- Outcome
}

testCaseDoc :: TestCase -> Doc
testCaseDoc (TestCase procName input outcome) = text procName <> parens (commaSep (map valueDoc input)) <+> outcomeDoc outcome

instance Show TestCase where show tc = show (testCaseDoc tc)

{- Test execution -}

-- | Test implementation def of procedure sig on all inputs prescribed by the testing strategy
testImplementation :: TestSettings -> PSig -> PDef -> SafeExecution [TestCase] 
testImplementation settings sig def = do
  let paramTypes = map itwType (psigParams sig)
  tc <- gets envTypeContext
  -- all types the procedure signature should be instantiated with:
  let typeInputs = generateInputTypes (tsGenericTypeRange settings) tc { ctxTypeVars = psigTypeVars sig } paramTypes  
  concat <$> mapM typeTestCase typeInputs
  where
    -- | Execute procedure instantiated with typeInputs on all value inputs
    typeTestCase :: [Type] -> SafeExecution [TestCase]
    typeTestCase typeInputs = do
      -- fresh names for variables to be used as actual parameters:
      let localNames = map ((\suffix -> [nonIdChar] ++ suffix) . show) [1..length (psigParams sig)]
      modify $ modifyTypeContext (`setLocals` (M.fromList $ zip localNames typeInputs))      
      let nIns = length (psigArgs sig)
      let (inNames, outNames) = splitAt nIns localNames
      let (inTypes, _) = splitAt nIns typeInputs
      tc <- gets envTypeContext
      -- all inputs the procedure should be tested on:
      let inputs = forM inTypes (generateInputValue settings tc)      
      mapM (\input -> TestCase (psigName sig) input <$> testCase inNames outNames input) inputs
    -- | Execute procedure on input, with actual in-parameter variables inNames and actual out-parameter variables outNames
    testCase :: [Id] -> [Id] -> [Value] -> SafeExecution Outcome
    testCase inNames outNames input = do
      setAll inNames input
      let inExpr = map (gen . Var) inNames
      let outExpr = map (gen . Var) outNames
      execSafely (execProcedure (assumePreconditions sig) def inExpr outExpr >> return Pass) failureReport
    -- | Test case outcome in case of a runtime error err
    failureReport err = case rteInfo err of
      AssumeViolation _ _ -> return $ Invalid err
      _ -> return $ Fail err

{- Input generation -}
    
-- | generateInputValue c t: all values of type t in context c    
generateInputValue :: TestSettings -> Context -> Type -> [Value]
generateInputValue _ _ BoolType = map BoolValue [False, True]
generateInputValue settings _ IntType = map IntValue (tsIntRange settings)
generateInputValue settings c (MapType tv domains range) = 
  let polyTypes = generateInputTypes (tsMapTypeRange settings) c { ctxTypeVars = tv } (range : domains) in
  -- A polymorphic map is a union of monomorphic maps with all possible instantiations for type variables
  map MapValue (M.unions <$> mapM monomorphicMap polyTypes)
  where 
    monomorphicMap (range : domains) = do  
      let args = forM domains (generateInputValue settings c)
      r <- replicateM (length args) (generateInputValue settings c range)
      return $ M.fromList (zip args r)
generateInputValue settings _ (Instance _ _) = map CustomValue (tsIntRange settings)

-- | All instantiations of types ts in context c, with a range of instances for a single type variables range 
generateInputTypes :: [Type] -> Context -> [Type] -> [[Type]]
generateInputTypes range c ts = do
  let freeVars = filter (\x -> any (x `isFreeIn`) ts) (ctxTypeVars c)
  actuals <- replicateM (length freeVars) range
  let binding = M.fromList (zip freeVars actuals)
  return $ map (typeSubst binding) ts
  