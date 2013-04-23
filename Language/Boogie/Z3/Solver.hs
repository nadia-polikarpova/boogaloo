{-# LANGUAGE RecordWildCards #-}
module Language.Boogie.Z3.Solver (solve) where

import           Control.Monad

import           Data.Foldable (Foldable)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import qualified Data.Set as Set

import           Language.Boogie.AST
import           Language.Boogie.Generator
import           Language.Boogie.Z3.Solution
import           Language.Boogie.Position
import           Language.Boogie.Solver
import           Language.Boogie.TypeChecker
import           Language.Boogie.Util ((|=|), conjunction, enot)
import           Language.Boogie.Z3.GenMonad

import           System.IO.Unsafe

solve :: (MonadPlus m, Foldable m) => Maybe Int -> [Expression] -> m Solution
solve mBound constrs = 
    case stepConstrs constrs of
      Just (soln, neq) -> return soln `mplus` go
          where
            go = if mBound == Nothing || (fromJust mBound > 1)
                    then do 
                      -- (ref, e) <- fromList (Map.toList soln)
                      -- let notE = enot (gen (Logical (thunkType e) ref) |=| e)
                      -- solve (fmap pred mBound) (notE : constrs)
                      solve (fmap pred mBound) (neq : constrs)
                    else mzero
      Nothing -> mzero    

stepConstrs :: [Expression] -> Maybe (Solution, Expression)
stepConstrs constrs = unsafePerformIO $ evalZ3Gen $
    do solnMb <- solveConstr constrs
       case solnMb of
         Just soln -> return $ Just (soln, newConstraint soln)
         Nothing -> return Nothing

newConstraint :: Solution -> Expression
newConstraint soln = enot (conjunction (logicEqs ++ customEqs))
    where
      logicEq :: Ref -> Expression -> Expression
      logicEq r e = logic e r |=| e
      
      -- Logical equations only for non-idType values.
      logicEqs :: [Expression]
      logicEqs = Map.foldrWithKey go [] soln
          where
            go ref expr es =
                case thunkType expr of
                  t@(IdType {..}) -> es
                  _ -> logicEq ref expr : es

      logict t r = gen (Logical t r)
      logic e r = gen (Logical (thunkType e) r)

      customEqs :: [Expression]
      customEqs = eqs ++ notEqs
          where
            eqs = concatMap (uncurry eqFold) (Map.toList customEqRel)
            notEqs = concat $ map snd $
                     Map.toList $ Map.mapWithKey allNeqs neqMaps
                where
                  neq t e r = enot (e |=| logict t r)
                  neqs t e = map (neq t e)

                  allNeqs :: Type -> [Ref] -> [Expression]
                  allNeqs t [] = []
                  allNeqs t (r:rs) = neqs t (logict t r) rs ++ allNeqs t rs

                  neqMaps :: Map Type [Ref]
                  neqMaps = Map.mapKeysWith (++) thunkType
                              (Map.map mkNeqData customEqRel)
                  mkNeqData refs = [head $ Set.toList refs]

            eqOp e r1 r2  = logic e r1 |=| logic e r2
            neqOp e r1 r2 = enot (eqOp e r1 r2)

            interPair op e [r1]       = [op e r1 r1]
            interPair op e (r1:r2:rs) = (op e r1 r2):(interPair op e (r2:rs))

            eqFold expr = interPair eqOp expr . Set.toList
            neqFold expr = interPair neqOp expr

      -- Equality relation on customs.
      customEqRel = Map.foldWithKey go Map.empty soln
          where
            go ref expr m =
                case thunkType expr of
                  t@(IdType {..}) -> 
                      Map.insertWith Set.union expr (Set.singleton ref) m
                  _ -> m
