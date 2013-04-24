{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

-- | Constraint solver interface
module Language.Boogie.Solver where

import Language.Boogie.AST
import Language.Boogie.Pretty
import Language.Boogie.PrettyAST
import Data.Map (Map, (!))

-- | Set of constraints
type ConstraintSet = [Expression]

constraintSetDoc :: ConstraintSet -> Doc
constraintSetDoc = vsep . map pretty

-- | Mapping from logical variables to their values
type Solution = Map Ref Thunk

instance Pretty Solution where
  pretty = vMapDoc logDoc pretty

-- | Solver: produces solutions of constraint sets
type Solver m = ConstraintSet -> m (Maybe Solution)
