-- | Constraint solver interface
module Language.Boogie.Solver where

import Language.Boogie.AST
import Data.Map (Map, (!))

-- | Set of constraints
type ConstraintSet = [Expression]

-- | Mapping from logical variables to their values
type Solution = Map Ref Thunk

-- | Solver: produces solutions of constraint sets
type Solver m = ConstraintSet -> m Solution
