module Tester where

import AST
import Util
import Position
import TypeChecker
import Tokens
import PrettyPrinter
import Interpreter
import DataFlow
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Error
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Text.PrettyPrint

{- Interface -}
    
-- | Test all implementations of all procedures procNames from program p in type context tc;
-- | requires that all procNames exist in context
testProgram :: TestSettings -> Program -> Context -> [Id] -> [TestCase]
testProgram settings p tc procNames = evalState (runReaderT programExecution settings) initEnvironment
  where
    initEnvironment = emptyEnv { envTypeContext = tc }
    programExecution = do
      inSession $ collectDefinitions p
      concat <$> forM procNames testProcedure
    -- | Test all implementations of procedure name
    testProcedure name = do
      sig <- gets (procSig name . envTypeContext) 
      defs <- gets (lookupProcedure name)
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
type TestSession a = ReaderT TestSettings (State Environment) a

-- | Embed a program execution into a testing session
inSession :: SafeExecution a -> TestSession a
inSession e = ReaderT (\_ -> e) 
        
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
testImplementation :: PSig -> PDef -> TestSession [TestCase] 
testImplementation sig def = do
  let paramTypes = map itwType (psigParams sig)
  tc <- gets envTypeContext
  typeRange <- asks tsGenericTypeRange
  -- all types the procedure signature should be instantiated with:
  let typeInputs = generateInputTypes typeRange tc { ctxTypeVars = psigTypeVars sig } paramTypes  
  concat <$> mapM typeTestCase typeInputs
  where
    -- | Execute procedure instantiated with typeInputs on all value inputs
    typeTestCase :: [Type] -> TestSession [TestCase]
    typeTestCase typeInputs = do
      -- fresh names for variables to be used as actual parameters:
      let localNames = map ((\suffix -> [nonIdChar] ++ suffix) . show) [1..length (psigParams sig)]
      modify $ modifyTypeContext (`setLocals` (M.fromList $ zip localNames typeInputs))      
      let nIns = length (psigArgs sig)
      let (inNames, outNames) = splitAt nIns localNames
      let (inTypes, _) = splitAt nIns typeInputs
      tc <- gets envTypeContext
      settings <- ask
      let execTestCase input = inSession $ testCase inNames outNames input
      let reportTestCase input = TestCase (psigName sig) input <$> execTestCase input
      -- all inputs the procedure should be tested on:
      let inputs = forM inTypes (generateInputValue settings tc)      
      mapM reportTestCase inputs
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
  