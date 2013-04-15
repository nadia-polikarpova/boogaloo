module Language.Boogie.Z3Solver where

import Language.Boogie.Heap
import Language.Boogie.AST
import Language.Boogie.ConstraintSolver

data MapPoint = MapPoint
     { mapPtMap :: Ref
     , mapPtArg :: [Value]
     , mapPtRes :: Value
     }

data LogicPoint = LogicPoint
     { logPtRef :: Ref
     , logPtVal :: Value
     }

data Point 
     = PtLog LogicPoint
     | PtMap MapPoint

mineMapPoints :: [Expression] -> [MapPoint]
mineMapPoints = error "mineMapPoints"

updateMapPoint :: Solution -> MapPoint -> MapPoint
updateMapPoint = error "updateMapPoints"

mineLogPoints :: [Expression] -> [LogicPoint]
mineLogPoints = error "mineLogPoints"

updateLogPoint :: Solution -> LogicPoint -> LogicPoint
updateLogPoint = error "updateLogPoint"

newConstraint :: [Expression] -> Solution -> Expression
newConstraint constrs soln = error "newConstraint"