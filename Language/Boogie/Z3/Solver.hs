module Language.Boogie.Z3.Solver (solve) where

import           Control.Monad

import           Data.Foldable (Foldable)
import qualified Data.Map as Map
import           Data.Maybe

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
                      (ref, e) <- fromList (Map.toList soln)
                      let notE = enot (gen (Logical (thunkType e) ref) |=| e)
                      solve (fmap pred mBound) (notE : constrs)
                    else mzero
      Nothing -> mzero    

stepConstrs :: [Expression] -> Maybe (Solution, Expression)
stepConstrs constrs = unsafePerformIO $ evalZ3Gen $
    do solnMb <- solveConstr constrs
       case solnMb of
         Just soln -> return $ Just (soln, newConstraint soln)
         Nothing -> return Nothing

newConstraint :: Solution -> Expression
newConstraint soln = enot (conjunction logicEqs)
    where
      logicEq :: Ref -> Expression -> Expression
      logicEq r e = gen (Logical (thunkType e) r) |=| e
      
      logicEqs :: [Expression]
      logicEqs = map (uncurry logicEq) (Map.toList soln)
