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
testProgram :: Program -> Context -> [Id] -> [TestCase]
testProgram p tc procNames = fromRight res -- All exceptions are caught in test cases (ToDo: introduce safe execution type)
  where
    initEnvironment = emptyEnv { envTypeContext = tc }
    (res, _) = runState (runErrorT programExecution) initEnvironment
    programExecution = do
      collectDefinitions p
      concat <$> forM procNames testProcedure
    -- | Test all implementations of procedure name
    testProcedure name = do
      sig <- gets (procSig name . envTypeContext) 
      defs <- gets (lookupProcedure name)
      concat <$> forM defs (testImplementation sig)
        
{- Reporting results -}        
        
data Outcome = Pass | Fail RuntimeError | Invalid RuntimeError

outcomeDoc :: Outcome -> Doc
outcomeDoc Pass = text "passed"
outcomeDoc (Fail err) = text "failed with: " <+> runtimeErrorDoc err
outcomeDoc (Invalid err) = text "invalid because: " <+> runtimeErrorDoc err

instance Show Outcome where show o = show (outcomeDoc o)

data TestCase = TestCase {
  tcProcedure :: Id,
  tcInput :: [Value],
  tcOutcome :: Outcome
}

testCaseDoc :: TestCase -> Doc
testCaseDoc (TestCase procName input outcome) = text procName <> parens (commaSep (map valueDoc input)) <+> outcomeDoc outcome

instance Show TestCase where show tc = show (testCaseDoc tc)

{- Test execution -}

testImplementation :: PSig -> PDef -> Execution [TestCase] 
testImplementation sig def = do
  tc <- gets envTypeContext
  let ins = psigArgs sig
  let outs = psigRets sig
  let localNames = map ((\suffix -> [nonIdChar] ++ suffix) . show) [1..length ins + length outs]
  let localTypes = map itwType (ins ++ outs)
  let typeInputs = generateInputTypes tc { ctxTypeVars = psigTypeVars sig} localTypes
  concat <$> mapM (typeTestCase (length ins) localNames) typeInputs
  where
    typeTestCase :: Int -> [Id] -> [Type] -> Execution [TestCase]
    typeTestCase nIns localNames actualTypes = do
      modify $ modifyTypeContext (`setLocals` (M.fromList $ zip localNames actualTypes))      
      let (inNames, outNames) = splitAt nIns localNames
      let (inTypes, _) = splitAt nIns actualTypes
      tc <- gets envTypeContext
      let inputs = forM inTypes (generateInputValue tc)      
      mapM (\input -> TestCase (psigName sig) input <$> testCase inNames outNames input) inputs
    testCase :: [Id] -> [Id] -> [Value] -> Execution Outcome
    testCase inNames outNames vals = do
      setAll inNames vals
      let inExpr = map (gen . Var) inNames
      let outExpr = map (gen . Var) outNames
      (execProcedure (assumePreconditions sig) def inExpr outExpr >> return Pass) `catchError` failureReport vals               
    failureReport vals err = case rteInfo err of
      AssumeViolation _ _ -> return $ Invalid err
      _ -> return $ Fail err

{- Input generation -}
    
intRange = [-1..1]
    
generateInputValue :: Context -> Type -> [Value]
generateInputValue _ BoolType = map BoolValue [False, True]
generateInputValue _ IntType = map IntValue intRange
generateInputValue c (MapType tv domains range) = let polyTypes = generateInputTypes c { ctxTypeVars = tv } (range : domains) in
  -- A polymorphic map is a union of monomorphic maps with all possible instantiations for type variables
  map MapValue (M.unions <$> mapM monomorphicMap polyTypes)
  where 
    monomorphicMap (range : domains) = do  
      let args = forM domains (generateInputValue c)
      r <- replicateM (length args) (generateInputValue c range)
      return $ M.fromList (zip args r)
generateInputValue _ (Instance _ _) = map CustomValue intRange

typeVarRange c = [IntType, BoolType]
-- typeVarRange c = [BoolType, IntType] ++ [Instance name [] | name <- M.keys (M.filter (== 0) (ctxTypeConstructors c))]

generateInputTypes :: Context -> [Type] -> [[Type]]
generateInputTypes c ts = do
  let freeVars = filter (\x -> any (x `isFreeIn`) ts) (ctxTypeVars c)
  actuals <- replicateM (length freeVars) (typeVarRange c)
  let binding = M.fromList (zip freeVars actuals)
  return $ map (typeSubst binding) ts
  