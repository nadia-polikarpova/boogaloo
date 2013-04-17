{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
module Language.Boogie.Z3.Solution 
    ( solveConstr
    , extract
    ) where

import           Control.Applicative
import           Control.Lens ((%=), uses)
import           Control.Monad

import           Data.Generics (everything, mkQ, gmapQ)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Map as Map
import           Data.Map (Map)

import           Z3.Monad

import           Language.Boogie.AST
import           Language.Boogie.Position
import           Language.Boogie.PrettyAST ()
import           Language.Boogie.Solver
import           Language.Boogie.Z3.Eval
import           Language.Boogie.Z3.GenMonad


-- | Update the state's reference map with the references in the
-- supplied expressions. This requires that the sorts already be
-- in place in the state.
updateRefMap :: [Expression] -> Z3Gen ()
updateRefMap = mapM_ addRefs
    where
      addRefs :: Expression -> Z3Gen ()
      addRefs e =
          do let rs = refs e
             pairs <- mapM (\r -> (r,) <$> declareRef r) (Set.toList rs)
             let updMap = Map.fromList pairs
             refMap %= Map.union updMap

      -- | Get the values from a single expression.
      refs :: Expression -> Set TaggedRef
      refs = everything Set.union (mkQ Set.empty go)
          where
            go (Logical t ref) = Set.singleton (LogicRef t ref)
            go e               = Set.unions (gmapQ (mkQ Set.empty go) e)

      refStr :: TaggedRef -> String
      refStr (LogicRef _ r) = "logical_" ++ show r

      refType :: TaggedRef -> Type
      refType (LogicRef t _) = t

      declareRef :: TaggedRef -> Z3Gen AST
      declareRef tRef =
          do symbol <- mkStringSymbol (refStr tRef)
             sort   <- lookupSort (refType tRef)
             mkConst symbol sort

-- | Given a set of constraint expressions produce a mapping
-- of references to their concrete values.
--
-- The constraint expressions will have no regular variables,
-- only logical variables and map variables.

solveConstr :: [Expression] -> Z3Gen (Model, Solution)
solveConstr constrs = 
    do updateRefMap constrs
       -- setOldCustoms constrs
       mapM_ (evalExpr >=> assertCnstr) constrs
       (_result, modelMb) <- getModel
       case modelMb of
         Just model -> (model,) <$> reconstruct model
         Nothing -> error "solveConstr.evalZ3: no model"


-- | Extracts a particular type from an AST node, evaluating
-- the node first.
extract :: Model -> Type -> AST -> Z3Gen Value
extract model t ast = 
    do Just ast' <- eval model ast
       case t of 
         IntType -> IntValue <$> getInt ast'
         BoolType -> 
             do bMb <- getBool ast'
                case bMb of
                  Just b -> return $ BoolValue b
                  Nothing -> error "solveConstr.reconstruct.extract: not bool"
         IdType ident types ->
             do proj <- lookupCustomProj ident types
                extr <- mkApp proj [ast']
                Just evald <- eval model extr
                int <- getInt evald
                -- let custom = Custom t (fromIntegral int)
                -- isInOld <- uses oldCustoms (Set.member custom)
                -- when (not isInOld) (newCustoms %= Set.insert custom)
                return (CustomValue t $ fromIntegral int)
         _ ->
             error $ concat [ "solveConstr.reconstruct.extract: can't "
                            , "extract maptypes like "
                            , show t
                            ]

-- | From a model and a mapping of values to Z3 AST nodes reconstruct
-- a mapping from references to values. This extracts the appropriate
-- values from the model.
reconstruct :: Model -> Z3Gen Solution
reconstruct model =
    do logicMap <- reconMaps
       return (Map.map (gen . Literal) logicMap)
    where
      extract' = extract model

      -- | Reconstruct all maps
      reconMaps :: Z3Gen (Map Ref Value)
      reconMaps = 
          do refAssoc <- uses refMap Map.toList 
             foldM go Map.empty refAssoc
          where go m (tRef, ast) =
                    case tRef of
                      LogicRef _ _ ->
                          do (r, v) <- reconLogicRef tRef ast
                             return (Map.insert r v m)

      -- | Reconstruct a ref/value pair for a logical reference.
      reconLogicRef :: TaggedRef -> AST -> Z3Gen (Ref, Value)
      reconLogicRef (LogicRef t ref) ast =
          do Just ast' <- eval model ast
             x <- extract' t ast'
             return (ref, x)

-- getOldCustom :: [Expression] -> Set Custom
-- getOldCustom = everything Set.union (mkQ Set.empty getCustom)
--     where
--       getCustom (CustomValue t i) = Set.singleton (Custom t i)
--       getCustom _ = Set.empty

-- setOldCustoms :: [Expression] -> Z3Gen ()
-- setOldCustoms exprs = oldCustoms .= getOldCustom exprs
