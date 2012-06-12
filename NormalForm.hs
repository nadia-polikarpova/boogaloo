{- Various normal forms of Boolean expressions -}
module NormalForm where

import AST
import Position
import Util
import TypeChecker
import Data.Map (Map, (!))
import qualified Data.Map as M

-- | Negation normal form of a Boolean expression:
-- | no negation above boolean connectives, quantifiers or relational operators;
-- | no boolean connectives except && and ||.
negationNF :: Context -> Expression -> Expression
negationNF c boolExpr = case contents boolExpr of
  UnaryExpression Not e -> case contents e of
    UnaryExpression Not e' -> negationNF c e'
    BinaryExpression And e1 e2 -> negationNF c (enot e1) ||| negationNF c (enot e2)
    BinaryExpression Or e1 e2 -> negationNF c (enot e1) |&| negationNF c (enot e2)
    BinaryExpression Implies e1 e2 -> negationNF c e1 |&| negationNF c (enot e2)
    BinaryExpression Equiv e1 e2 -> (negationNF c e1 |&| negationNF c (enot e2)) |&| (negationNF c (enot e1) |&| negationNF c e2)
    BinaryExpression Eq e1 e2 -> case exprType c e1 of
      BoolType -> negationNF c (enot (e1 |<=>| e2))
      _ -> e1 |!=| e2
    BinaryExpression Neq e1 e2 -> case exprType c e1 of
      BoolType -> negationNF c (e1 |<=>| e2)
      _ -> e1 |=| e2
    BinaryExpression Leq ae1 ae2 -> ae1 |>| ae2
    BinaryExpression Ls ae1 ae2 -> ae1 |>=| ae2
    BinaryExpression Geq ae1 ae2 -> ae1 |<| ae2
    BinaryExpression Gt ae1 ae2 -> ae1 |<=| ae2
    Quantified Forall tv vars e' -> attachPos (position e) $ Quantified Exists tv vars (negationNF (enterQuantified tv vars c) (enot e'))
    Quantified Exists tv vars e' -> attachPos (position e) $ Quantified Forall tv vars (negationNF (enterQuantified tv vars c) (enot e'))
    _ -> boolExpr
  BinaryExpression Implies e1 e2 -> negationNF c (enot e1) ||| negationNF c e2
  BinaryExpression Equiv e1 e2 -> (negationNF c (enot e1) ||| negationNF c e2) |&| (negationNF c e1 ||| negationNF c (enot e2))
  BinaryExpression Eq e1 e2 -> case exprType c e1 of
    BoolType -> negationNF c (e1 |<=>| e2)
    _ -> boolExpr
  BinaryExpression Neq e1 e2 -> case exprType c e1 of
    BoolType -> negationNF c (enot (e1 |<=>| e2))
    _ -> boolExpr
  BinaryExpression op e1 e2 | op == And || op == Or -> inheritPos2 (BinaryExpression op) (negationNF c e1) (negationNF c e2)    
  Quantified qop tv vars e -> attachPos (position boolExpr) $ Quantified qop tv vars (negationNF (enterQuantified tv vars c) e)
  _ -> boolExpr

-- | Prenex normal form of a Boolean expression:
-- | all quantifiers are pushed to the outside and any two quantifiers of the same kind in a row are glued together.
-- | Requires expression to be in the negation normal form.  
prenexNF :: Expression -> Expression
prenexNF boolExpr = (glue . rawPrenex) boolExpr
  where
    -- | Push all quantifiers to the front
    rawPrenex boolExpr = case contents boolExpr of
      -- We only ahve to consider && and || because boolExpr is in negation normal form
      BinaryExpression op e1 e2 | op == And || op == Or -> merge (++ "1") (++ "2") op (rawPrenex e1) (rawPrenex e2)
      _ -> boolExpr
    merge r1 r2 op e1 e2 = attachPos (position e1) (merge' r1 r2 op e1 e2)
    merge' r1 r2 op (Pos _ (Quantified qop tv vars e)) e2 = case renameBound r1 (Quantified qop tv vars e) of
      Quantified qop tv' vars' e' -> Quantified qop tv' vars' (merge r1 r2 op e' e2)
    merge' r1 r2 op e1 (Pos _ (Quantified qop tv vars e)) = case renameBound r2 (Quantified qop tv vars e) of
      Quantified qop tv' vars' e' -> Quantified qop tv' vars' (merge r1 r2 op e1 e')
    merge' _ _ op e1 e2 = BinaryExpression op e1 e2
    -- | Rename all bound variables and type variables in a quantified expression with a renaming function r
    renameBound r (Quantified qop tv vars e) = Quantified qop (map r tv) (map (renameVar r tv) vars) (exprSubst (varBinding r (map fst vars)) e)
    varBinding r ids = M.fromList $ zip ids (map (Var . r) ids)
    typeBinding r tv = M.fromList $ zip tv (map (nullaryType . r) tv)
    renameVar r tv (id, t) = (r id, typeSubst (typeBinding r tv) t)
    -- | Glue together any two quantifiers of the same kind in a row
    glue boolExpr = attachPos (position boolExpr) (glue' (contents boolExpr))
    glue' boolExpr = case boolExpr of
      Quantified qop tv vars e -> case contents e of
        Quantified qop' tv' vars' e' | qop == qop' -> glue' (Quantified qop (tv ++ tv') (vars ++ vars') e')
                                     | otherwise -> Quantified qop tv vars (glue e)
        _ -> boolExpr
      _ -> boolExpr

-- | Negation and prenexNF normal form of a Boolean expression
normalize :: Context -> Expression -> Expression      
normalize c boolExpr = prenexNF $ negationNF c boolExpr
