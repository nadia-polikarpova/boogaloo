{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
module Language.Boogie.Z3.Solution 
    ( solveConstr
    , (!)
    , Solution(..)
    , extract
    ) where

import           Control.Applicative
import           Control.Lens ((%=), (.=), _1, _2, over, use, uses)
import           Control.Monad

import           Data.Generics (everything, mkQ, gmapQ)
import           Data.List (intercalate)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Map as Map
import           Data.Map (Map)

import           Z3.Monad

import           Language.Boogie.AST
import           Language.Boogie.Heap
import           Language.Boogie.PrettyAST ()
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
      refs expr = valueT expr `Set.union` exprT expr
          where
            valueT = everything Set.union (mkQ Set.empty valueRef)
            exprT = everything Set.union (mkQ Set.empty go)

            go (LogicalVar t ref) = Set.singleton (LogicRef t ref)
            go e                  = Set.unions (gmapQ (mkQ Set.empty go) e)

            valueRef (Reference t r) = Set.singleton (MapRef t r)
            valueRef _ = Set.empty

      refStr :: TaggedRef -> String
      refStr (LogicRef _ r) = "logical_" ++ show r
      refStr (MapRef t r)   = intercalate "_" ["map", show r, typeString t]
                              -- Z3 doesn't have generics, so we incorporate
                              -- the type into the name of the symbol
                              -- to avoid this name clash.

      refType :: TaggedRef -> Type
      refType (LogicRef t _) = t
      refType (MapRef t _)   = t

      declareRef :: TaggedRef -> Z3Gen AST
      declareRef tRef =
          do symbol <- mkStringSymbol (refStr tRef)
             sort   <- lookupSort (refType tRef)
             mkConst symbol sort

data MapWithElse = MapWithElse
    { _mapPart :: MapRepr
    , _elsepart :: Value
    } deriving Show

-- instance Show MapWithElse where
--   show (MapWithElse m v) = show (pretty m)

(!) :: MapWithElse -> [Value] -> Value
(!) (MapWithElse m el) i = maybe el id (Map.lookup i m)

data Solution = Solution 
    { solnLogical :: Map Ref Value
    , solnMaps    :: Map Ref MapWithElse
    , solnCustoms :: Set Custom
    }

instance Show Solution where
  show (Solution logMap mapMap _) = 
    unlines [ "logical variables:"
            , show logMap 
            , "maps"
            , show mapMap
            ]

-- | Given a set of constraint expressions produce a mapping
-- of references to their concrete values.
--
-- The constraint expressions will have no regular variables,
-- only logical variables and map variables.

solveConstr :: [Expression] -> Z3Gen (Model, Solution)
solveConstr constrs = 
    do updateRefMap constrs
       setOldCustoms constrs
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
                let custom = Custom t (fromIntegral int)
                isInOld <- uses oldCustoms (Set.member custom)
                when (not isInOld) (newCustoms %= Set.insert custom)
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
    do (logicMap, mapMap) <- reconMaps
       customs <- customSet
       return (Solution logicMap mapMap customs)
    where
      extract' = extract model

      -- | Extract an argument to a 'select' or 'store', which is stored
      -- as a tuple. This 'untuples' the ast into a list of Boogaloo values.
      extractArg :: [Type] -> AST -> Z3Gen [Value]
      extractArg types tuple =
          do (_, _, projs) <- lookupCtor types
             debug ("extractArg start: " ++ show types)
             asts <- mapM (\ proj -> mkApp proj [tuple]) projs
             astsStr <- mapM astToString (tuple:asts)
             debug (unlines (map ("extArg: " ++) astsStr))
             zipWithM extract' types asts

      -- | Extract a Boogaloo function entry
      extractEntry :: [Type] -> Type -> [AST] -> AST -> Z3Gen ([Value], Value)
      extractEntry argTypes resType [argTuple] res =
          do debug "Entry start" 
             args <- extractArg argTypes argTuple
             debug "Extracted arg"
             res' <- extract' resType res
             debug "Extracted res"
             return (args, res')
      extractEntry _argTypes _resType _args _res =
          error "reconstruct.extractEntry: argument should be a single tuple"

      -- | Extract the new custom values from the model.
      customSet :: Z3Gen (Set Custom)
      customSet = use newCustoms

      -- | Reconstruct all maps
      reconMaps :: Z3Gen (Map Ref Value, Map Ref MapWithElse)
      reconMaps = 
          do refAssoc <- uses refMap Map.toList 
             foldM go (Map.empty, Map.empty) refAssoc
          where go mapTup  (tRef, ast) =
                    case tRef of
                      LogicRef _ _ ->
                          do (r, v) <- reconLogicRef tRef ast
                             return (over _1 (Map.insert r v) mapTup)
                      MapRef _ _ ->
                          do (r, v) <- reconMapWithElse tRef ast
                             return (over _2 (Map.insert r v) mapTup)

      -- | Reconstruct a map with else part from an array AST node.
      -- The argument must be a `MapRef`.
      reconMapWithElse :: TaggedRef -> AST -> Z3Gen (Ref, MapWithElse)
      reconMapWithElse (MapRef (MapType _ args res) ref) ast =
          do debug "reconMap start" 
             Just funcModel <- evalArray model ast
             !elsePart <- extract' res (interpElse funcModel)
             debug "extracted else"
             entries <- mapM (uncurry (extractEntry args res))
                             (interpMap funcModel)
             let m = Map.fromList entries
                 mapWithElse = MapWithElse m elsePart
             debug "reconMap end"
             return (ref, mapWithElse)
      reconMapWithElse _tRef _ast =
          error "reconstruct.reconMapWithElse: not a tagged map argument"

      -- | Reconstruct a ref/value pair for a logical reference.
      reconLogicRef :: TaggedRef -> AST -> Z3Gen (Ref, Value)
      reconLogicRef (LogicRef t ref) ast =
          do Just ast' <- eval model ast
             x <- extract' t ast'
             return (ref, x)
      reconLogicRef tr _ast = 
          error $ "reconLogicRef: not a logical ref" ++ show tr

getOldCustom :: [Expression] -> Set Custom
getOldCustom = everything Set.union (mkQ Set.empty getCustom)
    where
      getCustom (CustomValue t i) = Set.singleton (Custom t i)
      getCustom _ = Set.empty

setOldCustoms :: [Expression] -> Z3Gen ()
setOldCustoms exprs = oldCustoms .= getOldCustom exprs
