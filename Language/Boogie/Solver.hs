{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

-- | Constraint solver interface
module Language.Boogie.Solver where

import Language.Boogie.AST
import Language.Boogie.Pretty
import Language.Boogie.PrettyAST
import Data.Map (Map, (!))

import Z3.Monad as Z3 (Context)

-- | Set of constraints
type ConstraintSet = [Expression]

constraintSetDoc :: ConstraintSet -> Doc
constraintSetDoc = vsep . map pretty

-- | Mapping from logical variables to their values
type Solution = Map Ref Thunk

instance Pretty Solution where
  pretty = vMapDoc logDoc pretty

-- | Solver: produces solutions of constraint sets
data Solver m = Solver {
  solCheck :: ConstraintSet -> Int -> (Bool, Int),      -- | Given a constraint set and a current solver state id, return whether the constraint set is satisfiable and the new state id
  solPick :: ConstraintSet -> Int -> m (Solution, Int)  -- | Given a constraint set and a current solver state id, return solution(s) and the new state id
}
