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
import Control.Monad.Identity
import Control.Monad.Error
import Control.Applicative
import Control.Monad.State
import Control.Monad.Trans.List
import Text.PrettyPrint
    
testProgram :: Program -> Context -> Id -> [String]
testProgram p tc main = testReports
  where
    initEnvironment = emptyEnv { envTypeContext = tc }
    testReports = case runState (runErrorT programState) initEnvironment of
      (Left err, _) -> []
      (Right list, env) -> list            
    programState = do
      collectDefinitions p
      env <- get
      case lookupProcedure main env of
        [] -> throwRuntimeError (OtherError (text "Cannot find program entry point" <+> text main)) noPos
        def : _ -> testProcedure main def

testProcedure :: Id -> PDef -> Execution [String] 
testProcedure name def = do
  tc <- gets envTypeContext
  let sig = procSig name tc
  let ins = psigArgs sig
  let outs = psigRets sig
  let localNames = map ((\suffix -> [nonIdChar] ++ suffix) . show) [1..length ins + length outs]
  let localTypes = map itwType (ins ++ outs)
  let typeInputs = generateInputTypes tc { ctxTypeVars = psigTypeVars sig} localTypes
  concat <$> mapM (typeTestCase tc (length ins) localNames) typeInputs
  where
    typeTestCase :: Context -> Int -> [Id] -> [Type] -> Execution [String]
    typeTestCase tc nIns localNames actualTypes = do
      let (inNames, outNames) = splitAt nIns localNames
      let (inTypes, _) = splitAt nIns actualTypes
      let inputs = forM inTypes (generateInputValue tc)
      modify $ \env -> env { envTypeContext = setLocals tc (M.fromList $ zip localNames actualTypes) }
      mapM (testCase inNames outNames) inputs 
    testCase :: [Id] -> [Id] -> [Value] -> Execution String
    testCase inNames outNames vals = do
      setAll inNames vals
      let inExpr = map (gen . Var) inNames
      let outExpr = map (gen . Var) outNames
      (execProcedure name def inExpr outExpr >> return "Success") `catchError` failureReport vals      
   
failureReport :: [Value] -> RuntimeError -> Execution String   
failureReport vals err = return $ "Execution with " ++ show (commaSep (map valueDoc vals)) ++ " resulted in error: " ++ show (runtimeErrorDoc err)
    
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
  