module Language.Boogie.ConstraintSolver where

import           Control.Applicative
import           Control.Monad

import qualified Data.Foldable as Fold
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Map as Map
import           Data.Map (Map)

import           System.IO.Unsafe

import           Z3.Monad

import           Language.Boogie.AST
import           Language.Boogie.Heap
import           Language.Boogie.Position
import           Language.Boogie.PrettyAST ()
import           Language.Boogie.Pretty

ex1 :: Map Ref String
ex1 = Map.map (show . pretty) (solveConstr constrs)
    where
      p0 = Pos noPos
      v0 = p0 (Literal $ LogicalVar IntType 0)
      c4 = p0 (Literal $ IntValue 4)
      constrs = [p0 (BinaryExpression Eq 
                     (p0 (BinaryExpression Plus v0 v0))
                     c4)]

solveConstr :: [Expression] -> Map Ref Value
solveConstr constrs = unsafePerformIO (evalZ3 checkConstraints)
    where
      checkConstraints :: Z3 (Map Ref Value)
      checkConstraints = 
          do (valueMap, funcMap) <- mkValueMap (valueUnion constrs)
             assert' valueMap funcMap
             (_result, modelMb) <- getModel
             case modelMb of
               Just model -> reconstruct model valueMap
                   -- do str <- showModel model
                   --    error ("model: " ++ str)
               Nothing -> error "solveConstr.evalZ3: no model"

      reconstruct :: Model -> Map Value AST -> Z3 (Map Ref Value)
      reconstruct model = fmap Map.fromList . reconstruct' . Map.toList
          where
            extract :: Type -> AST -> Z3 Value
            extract IntType ast = IntValue <$> getInt ast
            extract BoolType ast = 
                getBool ast >>= \ bMb -> case bMb of
                                           Just b -> return $ BoolValue b

            reconstruct' :: [(Value, AST)] -> Z3 [(Ref, Value)]
            reconstruct' [] = return []
            reconstruct' ((v,ast):rest) =
                case v of
                  LogicalVar t ref ->
                      do Just ast' <- eval model ast
                         v <- extract t ast'
                         rest' <- reconstruct' rest
                         return ((ref, v) : rest')
                  _ -> reconstruct' rest

      assert' :: Map Value AST -> Map Value FuncDecl -> Z3 ()
      assert' m funcM = mapM_ (evalExpr m funcM >=> assertCnstr) constrs

      evalExpr :: Map Value AST      -- ^ Map from constants/vars to AST
               -> Map Value FuncDecl -- ^ Map from function ids to function decls
               -> Expression         -- ^ Expression to evaluate
               -> Z3 AST
      evalExpr m funcM expr =
          case node expr of
            Literal v -> return (m Map.! v)
            MapSelection (Pos _ (Literal v)) es -> 
                mkApp (funcM Map.! v) =<< mapM go es
            UnaryExpression op e -> go e >>= unOp op
            BinaryExpression op e1 e2 ->
                join (binOp op <$> go e1 <*> go e2)
            IfExpr c e1 e2 ->
                join (mkIte <$> go c <*> go e1 <*> go e2)
            MapUpdate _ _ _ -> 
                error "solveConstr.evalExpr: map update not implemented"
            e -> error $ "solveConstr.evalExpr: " ++ show e
          where go = evalExpr m funcM

      unOp Neg = mkUnaryMinus
      unOp Not = mkNot

      binOp op =
          case op of
            Eq -> mkEq
            Gt -> mkGt
            Ls -> mkLt
            Leq -> mkLe
            Geq -> mkGe
            Neq -> \ x y -> mkEq x y >>= mkNot

            Plus -> list2 mkAdd
            Minus -> list2 mkSub
            Times -> list2 mkMul
            Div   -> mkDiv
            Mod   -> mkMod

            And   -> list2 mkAnd
            Or    -> list2 mkOr
            Implies -> mkImplies
            Equiv -> mkIff
            Explies -> flip mkImplies
            Lc -> error "solveConstr.binOp: Lc not implemented"
          where list2 o x y = o [x, y]

      valueUnion :: [Expression] -> Set Value
      valueUnion = Set.unions . map values

      values :: Expression -> Set Value
      values expr =
          case node expr of
            Literal v                -> Set.singleton v
            MapSelection e es        -> valueUnion (e:es)
            MapUpdate e1 es e2       -> valueUnion (e1:e2:es)
            Old e                    -> values e
            IfExpr c e1 e2           -> valueUnion [c,e1,e2]
            UnaryExpression _ e      -> values e
            BinaryExpression _ e1 e2 -> valueUnion [e1, e2]
            Quantified _ _ _ e       -> values e
            e -> error $ "solveConstr.values: " ++ show e

      -- Function types are not `Sort`, so this won't work for them.
      typeToSort :: Type -> Z3 Sort
      typeToSort IntType  = mkIntSort
      typeToSort BoolType = mkBoolSort

      -- FIXME: Functions (maps) must be declared differently, so this won't
      -- work due to the use of `typeToSort`.
      -- Should treat functions separately.
      declareValue :: Value -> Z3 (Either AST FuncDecl)
      declareValue (IntValue i)      = Left <$> mkInt i
      declareValue (BoolValue True)  = Left <$> mkTrue
      declareValue (BoolValue False) = Left <$> mkFalse
      declareValue v@(Reference (MapType _ args res) _ref) =
          do symbol <- mkStringSymbol (valueName v)
             args'  <- mapM typeToSort args
             res'   <- typeToSort res
             Right <$> mkFuncDecl symbol args' res'
      declareValue v =
          do symbol <- mkStringSymbol (valueName v)
             sort   <- typeToSort (valueType v)
             Left <$> mkConst symbol sort

      mkValueMap :: Set Value -> Z3 (Map Value AST, Map Value FuncDecl)
      mkValueMap = Fold.foldrM go (Map.empty, Map.empty)
          where
            go val (m, funcM) =
                do resEi <- declareValue val
                   case resEi of
                     Left ast -> return (Map.insert val ast m, funcM)
                     Right fDecl -> return (m, Map.insert val fDecl funcM)
