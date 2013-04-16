module Language.Boogie.Z3.Solver where

import           Control.Monad
import           Control.Monad.Stream

import           Data.Either
import           Data.Foldable (Foldable)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Language.Boogie.AST
import           Language.Boogie.Z3.Solution
import           Language.Boogie.Heap
import           Language.Boogie.Position
import           Language.Boogie.TypeChecker
import           Language.Boogie.Z3.Eval
import           Language.Boogie.Z3.GenMonad

import           System.IO.Unsafe

import           Z3.Monad

ex1 :: String
ex1 = show (take 10 $ toList fcrs)
    where
      fcrs :: Stream Forcer
      fcrs = forcers constrs

      p0 = Pos noPos
      int = p0 . Literal . IntValue
      v0 = p0 (LogicalVar IntType 57)
      m0 = p0 (Literal $ Reference (MapType [] [IntType, IntType] IntType) 50)
      sel0 = p0 (MapSelection m0 [int 42, int 100])
      constrs = [ p0 (BinaryExpression Gt 
                       (p0 (BinaryExpression Plus v0 v0))
                       (int 4))
                , p0 (BinaryExpression Gt sel0 v0)
                ]

forcers :: (MonadPlus m, Foldable m) => [Expression] -> m Forcer
forcers constrs = return forcer `mplus`  forcers (neq : constrs)
    where
      (forcer, neq) = stepConstrs constrs

stepConstrs :: [Expression] -> (Forcer, Expression)
stepConstrs constrs = unsafePerformIO $ evalZ3Gen $
    do (model, soln) <- solveConstr constrs
       forcer <- mkForcer model constrs soln
       return (forcer, newConstraint forcer)

data MapPoint e = MapPoint
     { mapPtMap :: Ref
     , mapPtType :: Type
     , mapPtArg :: e
     } deriving (Eq, Ord, Show)

data LogicPoint = LogicPoint
     { logPtRef :: Ref
     , logPtType :: Type
     } deriving (Eq, Ord, Show)

type MapReprMap = Map (MapPoint ()) MapRepr
type LogicMap = Map LogicPoint Value

data Forcer = Forcer
    { forcerMapRepr :: MapReprMap
    , forcerLogic :: LogicMap
    } deriving Show

unsafeEval :: Model -> Expression -> Z3Gen Value
unsafeEval model e =
    do let t = exprType emptyContext e
       ast <- evalExpr e
       extract model t ast

-- | Forcer creation
mkForcer :: Model -> [Expression] -> Solution -> Z3Gen Forcer
mkForcer model constrs soln =
    do mapValuePts <- mapM updMapPt mpPts
       let mpReprs = foldr (uncurry updMapRepr) Map.empty mapValuePts
       return (Forcer mpReprs lgMap)
    where
      lgMap = Map.fromList (map (updateLogPoint soln) lgPts)
      lgPts = mineLogPoints constrs

      updMapPt = updateMapPoint model soln
      mpPts = mineMapPoints constrs

      updMapRepr :: MapPoint [Value] -> Value -> MapReprMap -> MapReprMap
      updMapRepr (MapPoint ref ttype arg) result reprMap =
          Map.insertWith 
              Map.union
              (MapPoint ref ttype ())
              (Map.singleton arg result)
              reprMap

updateMapPoint :: Model -> Solution -> MapPoint [Expression]
               -> Z3Gen (MapPoint [Value], Value)
updateMapPoint model soln (MapPoint ref ttype args) =
    do args' <- mapM (unsafeEval model) args
       return (MapPoint ref ttype args', arrMap ! args')
    where
      arrMap = solnMaps soln Map.! ref

updateLogPoint :: Solution -> LogicPoint -> (LogicPoint, Value)
updateLogPoint soln pt@(LogicPoint ref _ttype) =
    (pt, solnLogical soln Map.! ref)


-- | Converts the forcer information to an expression
-- which forces at leaset one of the assignments to change
-- upon adding it to the list of constraints.
newConstraint :: Forcer -> Expression
newConstraint forcer = not' (and' (logicEqs ++ mapEqs))
    where
      p0 = Pos noPos
      not' = p0 . UnaryExpression Not
      lit = p0 . Literal
      select m args = p0 (MapSelection m args)
      and' = foldr (\ x y -> p0 (BinaryExpression And x y)) 
                   (lit (BoolValue True))
      eq e1 e2 = p0 (BinaryExpression Eq e1 e2)

      logicEq :: LogicPoint -> Value -> Expression
      logicEq (LogicPoint r t) v = eq (p0 $ LogicalVar t r) (lit v)
      
      logicEqs :: [Expression]
      logicEqs = map (uncurry logicEq) (Map.toList $ forcerLogic forcer)

      mapEqs :: [Expression]
      mapEqs = concatMap (uncurry mapEq) (Map.toList $ forcerMapRepr forcer)

      mapEq :: MapPoint () -> MapRepr -> [Expression]
      mapEq (MapPoint ref t ()) repr = map (uncurry mapEntryEq) (Map.toList repr)
          where
            m = lit (Reference t ref)
            mapEntryEq args val =
                eq (select m (map (p0 . Literal) args)) (lit val)

-- Mining points
mineLogPoints :: [Expression] -> [LogicPoint]
mineLogPoints = rights . miners

mineMapPoints :: [Expression] -> [MapPoint [Expression]]
mineMapPoints = lefts . miners

miners :: [Expression] -> [Either (MapPoint [Expression]) LogicPoint]
miners = concatMap mine
    where
      mine expr =
          case node expr of
            UnaryExpression _op e -> mine e
            BinaryExpression _op e1 e2 -> mine e1 ++ mine e2
            IfExpr c e1 e2 -> concat [mine c, mine e1, mine e2]
            MapSelection a args -> 
                case node a of
                  Literal (Reference t r) ->
                      Left (MapPoint r t args) : miners args
                  _ ->
                      error $ unwords ["mineMapPoints: cannot mine map points"
                                      ,"with a selection on"
                                      ,show a
                                      ]
            MapUpdate m args val -> miners $ m:val:args
            Literal _v -> []
            LogicalVar t ref -> [Right $ LogicPoint ref t]
            e -> error $ "mineMapPoints: " ++ show e