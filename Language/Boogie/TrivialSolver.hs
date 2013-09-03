{-# LANGUAGE TupleSections #-}

module Language.Boogie.TrivialSolver (solve, solver) where

import           Control.Applicative
import           Control.Monad.Identity
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Error

import           Data.Maybe
import           Data.Generics
import           Data.List (nub)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Language.Boogie.AST
import           Language.Boogie.Generator
import           Language.Boogie.Position
import           Language.Boogie.Pretty
import           Language.Boogie.Solver

solver :: (MonadPlus m, Functor m)
      => Maybe Int     -- ^ Bound on number of solutions
      -> Solver m
solver mBound = Solver {
  solPick = \cs n -> liftM ((flip (,) n) . fromJust) $ solve mBound cs,
  solCheck = \cs n -> (True, n)
}      

genValOfType :: (MonadPlus m, Functor m) => Generator m -> Type -> m Thunk
genValOfType gtor ttype = gen <$> Literal <$> val
    where
     val = case ttype of
             IntType -> IntValue <$> genInteger gtor
             BoolType -> BoolValue <$> genBool gtor
             IdType _ _ -> CustomValue ttype <$> fromIntegral <$> genInteger gtor
             _ -> error $ "genValOfType: can't generate value for " ++ show ttype

getLogPoint :: (MonadPlus m, Functor m) => Generator m -> Ref -> Type -> m (Ref, Thunk)
getLogPoint gen ref ttype =
    (ref,) <$> genValOfType gen ttype

-- | Solve
solve :: (MonadPlus m, Functor m) => Maybe Int -> ConstraintSet -> m (Maybe Solution)
solve mBound constrs = 
    (Just . Map.fromList) <$> mapM (uncurry (getLogPoint gtor)) (nub lgPts)
    where
      gtor = exhaustiveGenerator (fmap toInteger mBound)
      lgPts = everything (++) (mkQ [] go) constrs
          where
            go expr = 
                case node expr of
                  Logical t ref -> [(ref, t)]
                  e -> concat (gmapQ (mkQ [] go) e)
          
