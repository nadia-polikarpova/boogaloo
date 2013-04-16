{-# LANGUAGE TupleSections #-}

module Language.Boogie.TrivialForcer where

import           Control.Applicative
import           Control.Monad.Stream
import           Control.Monad.Identity
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Error

import           Data.Map (Map)
import qualified Data.Map as Map

import           Language.Boogie.AST
import           Language.Boogie.Environment
import           Language.Boogie.Generator
import           Language.Boogie.Interpreter
import           Language.Boogie.Position
import           Language.Boogie.Pretty
import           Language.Boogie.TypeChecker
import           Language.Boogie.Z3.Solver

trivialForcers :: [Expression] -> Stream Forcer
trivialForcers constrs = error "trivialForcers:"

evalThenLookup :: LogicMap -> Expression -> Value
evalThenLookup logicMap e =
    case node (eval' e) of
      Literal v -> v
      LogicalVar ttype ref -> logicMap Map.! LogicPoint ref ttype
    where
      emptyEnv = initEnv emptyContext defaultGenerator Nothing

      runExecution :: Execution Identity a
                   -> Environment Identity
                   -> Either RuntimeFailure a
      runExecution m env =
          fst $ runIdentity $ runStateT (runErrorT m) env

      eval' :: Expression -> Expression
      eval' e = case runExecution (eval e) emptyEnv of
                  Left err -> error $ "evalThenLookup: " ++ show (pretty err)
                  Right expr -> error "evalThenLookup: wrong type for now"


genValOfType :: Generator Stream -> Type -> Stream Value
genValOfType gen ttype =
    case ttype of
      IntType -> IntValue <$> genInteger gen
      BoolType -> BoolValue <$> genBool gen
      _ -> error $ "genValOfType: can't generate value for " ++ show ttype

getLogPoint :: Generator Stream -> LogicPoint -> Stream (LogicPoint, Value)
getLogPoint gen pt@(LogicPoint ref ttype) =
    (pt,) <$> genValOfType gen ttype

getMapPoint :: Generator Stream
            -> LogicMap
            -> MapPoint [Expression] -- ^ Assuming this doesn't contain
                                     -- any maps selections as an argument.
            -> Stream (MapPoint [Value], Value)
getMapPoint gen logicMap (MapPoint ref ttype@(MapType _ _ resType) arg) =
    (pt',) <$> genValOfType gen resType
    where
      pt' = MapPoint ref ttype (map (evalThenLookup logicMap) arg)

-- | Forcer creation
mkForcer :: Generator Stream -> [Expression] -> Stream Forcer
mkForcer gen constrs =
    do lgMap <- lgMapM
       mapValuePts <- mapM (updMapPt lgMap) mpPts
       let mpReprs = foldr (uncurry updMapRepr) Map.empty mapValuePts
       return (Forcer mpReprs lgMap)
    where
      lgMapM = Map.fromList <$> mapM (getLogPoint gen) lgPts
      lgPts  = mineLogPoints constrs

      updMapPt = getMapPoint gen
      mpPts = mineMapPoints constrs

      updMapRepr :: MapPoint [Value] -> Value -> MapReprMap -> MapReprMap
      updMapRepr (MapPoint ref ttype arg) result reprMap =
          Map.insertWith 
              Map.union
              (MapPoint ref ttype ())
              (Map.singleton arg result)
              reprMap
