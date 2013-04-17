module Language.Boogie.Z3.Solver (solve) where

import           Control.Monad

import           Data.Foldable (Foldable)
import qualified Data.Map as Map

import           Language.Boogie.AST
import           Language.Boogie.Z3.Solution
import           Language.Boogie.Position
import           Language.Boogie.Solver
import           Language.Boogie.TypeChecker
import           Language.Boogie.Z3.GenMonad

import           System.IO.Unsafe

solve :: (MonadPlus m, Foldable m) => [Expression] -> m Solution
solve constrs = return solution `mplus` solve (neq : constrs)
    where
      (solution, neq) = stepConstrs constrs

stepConstrs :: [Expression] -> (Solution, Expression)
stepConstrs constrs = unsafePerformIO $ evalZ3Gen $
    do (_model, soln) <- solveConstr constrs
       return (soln, newConstraint soln)

newConstraint :: Solution -> Expression
newConstraint soln = not' (and' logicEqs)
    where
      p0 = Pos noPos
      not' = p0 . UnaryExpression Not
      lit = p0 . Literal
      and' = foldr (\ x y -> p0 (BinaryExpression And x y)) 
                   (lit (BoolValue True))
      eq e1 e2 = p0 (BinaryExpression Eq e1 e2)

      logicEq :: Ref -> Expression -> Expression
      logicEq r e = eq (p0 $ Logical (thunkType e) r) e
      
      logicEqs :: [Expression]
      logicEqs = map (uncurry logicEq) (Map.toList soln)
