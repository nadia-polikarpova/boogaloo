{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}

module Language.Boogie.ConstraintSolver where

import           Control.Applicative
import           Control.Lens ((%=), _1, _2, over, uses, use, makeLenses)
import           Control.Monad
import           Control.Monad.Trans.State
import           Control.Monad.Trans

import qualified Data.Foldable as Fold
import           Data.List (intercalate)
import           Data.Maybe
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
import           Language.Boogie.TypeChecker

data TaggedRef 
    = LogicRef Type Ref 
    | MapRef Type Ref
      deriving (Eq, Ord, Show)

data Z3Env = Z3Env
    { _ctorMap :: 
          Map [Type] 
                 (Sort, FuncDecl, [FuncDecl]) -- ^ Maps a list of types to a
                                              -- a tuple of them, and the
                                              -- associated constructor.
    , _sortMap :: Map Type Sort               -- ^ Maps types to sorts
    , _customVals :: Map Int AST              -- ^ Map custom value tags to
                                              -- their AST.
    , _refMap  :: Map TaggedRef AST           -- ^ Maps references to their
                                              -- Z3 AST node.
    -- , _solution :: Solution
    }

makeLenses ''Z3Env

instance MonadZ3 Z3Gen where
    getSolver = lift getSolver
    getContext = lift getContext

type Z3Gen = StateT Z3Env Z3

emptyEnv :: Z3Env
emptyEnv = Z3Env Map.empty Map.empty Map.empty Map.empty

evalZ3Gen :: Z3Gen a -> IO a
evalZ3Gen act = evalZ3 $ evalStateT act emptyEnv

lookup' :: Ord k => String -> k -> Map k a -> a
lookup' errMsg key m =
  case Map.lookup key m of
    Just a -> a
    Nothing -> error errMsg

-- | Evaluate an expression to a Z3 AST.
evalExpr :: Expression -- ^ Expression to evaluate
         -> Z3Gen AST
evalExpr expr = debug ("evalExpr: " ++ show expr) >>
    case node expr of
      Literal v -> evalValue v
      LogicalVar t ref -> uses refMap (lookup' "evalExpr" (LogicRef t ref))
      MapSelection m args ->
          do m' <- go m
             arg <- tupleArg args
             mkSelect m' arg
      MapUpdate m args val ->
          do m' <- go m
             arg <- tupleArg args
             val' <- go val
             mkStore m' arg val'
      UnaryExpression op e -> go e >>= unOp op
      BinaryExpression op e1 e2 -> join (binOp op <$> go e1 <*> go e2)
      IfExpr c e1 e2 -> join (mkIte <$> go c <*> go e1 <*> go e2)
      e -> error $ "solveConstr.evalExpr: " ++ show e
    where
      evalValue :: Value -> Z3Gen AST
      evalValue v =
          case v of
            IntValue i      -> mkInt i
            BoolValue True  -> mkTrue
            BoolValue False -> mkFalse
            Reference t ref -> uses refMap (lookup' "evalValue" (MapRef t ref))
            CustomValue t i -> 
                error "evalValue: FIXME: add custom value to custom value map"
            MapValue _ _    -> error "evalValue: map value found"

      go = evalExpr

      tupleArg :: [Expression] -> Z3Gen AST
      tupleArg es =
          do let ts = map (exprType emptyContext) es
             debug (show ts)
             (_sort, ctor, _projs) <- lookupCtor ts
             es' <- mapM go es
             c <- mkApp ctor es'
             return c

      unOp :: UnOp -> AST -> Z3Gen AST
      unOp Neg = mkUnaryMinus
      unOp Not = mkNot

      binOp :: BinOp -> AST -> AST -> Z3Gen AST
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


justElse :: Maybe a -> a -> a
justElse = flip fromMaybe

justElseM :: Monad m => Maybe a -> m a -> m a
justElseM mb v = maybe v return mb

lookupSort :: Type -> Z3Gen Sort
lookupSort t =
    do sortMb <- uses sortMap (Map.lookup t)
       justElseM sortMb $
         do s <- typeToSort t
            sortMap %= Map.insert t s
            return s
    where
      -- | Construct a type map.
      typeToSort :: Type -> Z3Gen Sort
      typeToSort t =
          case t of
            IntType  -> mkIntSort
            BoolType -> mkBoolSort
            MapType _ argTypes resType ->
                do tupleArgSort <- lookupTupleSort argTypes
                   resSort <- lookupSort resType
                   mkArraySort tupleArgSort resSort
            _ ->
                error $ "typeToSort: cannot construct sort from " ++ show t

lookupTupleSort :: [Type] -> Z3Gen Sort
lookupTupleSort types = ( \ (a,_,_) -> a) <$> lookupCtor types

-- | Construct a tuple from the given arguments
lookupCtor :: [Type] -> Z3Gen (Sort, FuncDecl, [FuncDecl])
lookupCtor types =
    do sortMb <- uses ctorMap (Map.lookup types)
       justElseM sortMb $
         do sorts   <- mapM lookupSort types
            let tupStr = tupleSymbol types
            argSyms <- mapM (mkStringSymbol . (tupStr ++) . show) 
                             [1 .. length types]
            sym     <- mkStringSymbol tupStr
            tupRes  <- mkTupleSort sym (zip argSyms sorts)
            ctorMap %= Map.insert types tupRes
            return tupRes

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
      refs expr =
          case node expr of
            Literal v                -> valueRef v
            LogicalVar t ref         -> Set.singleton (LogicRef t ref)
            MapSelection e es        -> refUnion (e:es)
            MapUpdate e1 es e2       -> refUnion (e1:e2:es)
            Old e                    -> refs e
            IfExpr c e1 e2           -> refUnion [c,e1,e2]
            UnaryExpression _ e      -> refs e
            BinaryExpression _ e1 e2 -> refUnion [e1, e2]
            Quantified _ _ _ e       -> refs e
            e -> error $ "solveConstr.refs: " ++ show e

      -- | Get the refs of a list of expressions
      refUnion :: [Expression] -> Set TaggedRef
      refUnion = Set.unions . map refs

      -- | Get the value from a ref
      valueRef :: Value -> Set TaggedRef
      valueRef v =
          case v of
            Reference t r   -> Set.singleton (MapRef t r)
            MapValue _ repr -> Set.unions . map go . Map.toList $ repr
                where
                  go (vals, v) = Set.unions (map valueRef (v:vals))
            _ -> Set.empty

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

-- | Type name for the symbol for the sort
tupleSymbol :: [Type] -> String
tupleSymbol ts = intercalate "_" (map typeString ts) ++ "SYMBOL"

-- | Symbol name for a type
typeString :: Type -> String
typeString t =
   case t of
     IntType -> "int"
     BoolType -> "bool"
     MapType _ args res -> 
         concat ["(", tupleSymbol args, ")->", typeString res]

data MapWithElse = MapWithElse
    { mapPart :: MapRepr
    , elsepart :: Value
    } deriving Show

-- instance Show MapWithElse where
--   show (MapWithElse m v) = show (pretty m)

(!) :: MapWithElse -> [Value] -> Value
(!) (MapWithElse m el) i = maybe el id (Map.lookup i m)

data NewCustomVal = NewCustomVal Type Int

data Solution = Solution 
    { forcerLogical :: Map Ref Value
    , forcerMaps    :: Map Ref MapWithElse
    , forcerCustoms :: Set NewCustomVal
    }

instance Show Solution where
  show (Solution logMap mapMap _) = 
    unlines [ "logical variables:"
            , show logMap 
            , "maps"
            , show mapMap
            ]

ex1 :: String
ex1 = show (solveConstr constrs)
    where
      p0 = Pos noPos
      int = p0 . Literal . IntValue
      v0 = p0 (LogicalVar IntType 57)
      m0 = p0 (Literal $ Reference (MapType [] [IntType, IntType] IntType) 50)
      sel0 = p0 (MapSelection m0 [int 42, int 100])
      constrs = [ p0 (BinaryExpression Eq 
                       (p0 (BinaryExpression Plus v0 v0))
                       (int 4))
                , p0 (BinaryExpression Gt sel0 v0)
                ]

-- | Given a set of constraint expressions produce a mapping
-- of references to their concrete values.
--
-- The constraint expressions will have no regular variables,
-- only logical variables and map variables.

solveConstr :: [Expression] -> Solution
solveConstr constrs = unsafePerformIO (evalZ3Gen checkConstraints)
    where
      -- | Produce a the result in the Z3 monad, to be extracted later.
      checkConstraints :: Z3Gen Solution
      checkConstraints = 
          do updateRefMap constrs
             mapM_ (evalExpr >=> assertCnstr) constrs
             (_result, modelMb) <- getModel
             case modelMb of
               Just model -> reconstruct model
               Nothing -> error "solveConstr.evalZ3: no model"

-- | From a model and a mapping of values to Z3 AST nodes reconstruct
-- a mapping from references to values. This extracts the appropriate
-- values from the model.
reconstruct :: Model -> Z3Gen Solution
reconstruct model =
    do (logicMap, mapMap) <- reconMaps
       customs <- customSet
       return (Solution logicMap mapMap customs)
    where
      extract :: Type -> AST -> Z3Gen Value
      extract t ast = do -- astToString ast >>= \ str -> debug (show (str, t)) >>
        Just ast' <- eval model ast
        case t of 
          IntType -> IntValue <$> getInt ast'
          BoolType -> 
            do bMb <- getBool ast'
               case bMb of
                 Just b -> return $ BoolValue b
                 Nothing -> error "solveConstr.reconstruct.extract: not bool"
          _ ->
            error $ concat [ "solveConstr.reconstruct.extract: can't "
                           , "extract for type "
                           , show t
                           ]

      -- | Extract an argument to a 'select' or 'store', which is stored
      -- as a tuple. This 'untuples' the ast into a list of Boogaloo values.
      extractArg :: [Type] -> AST -> Z3Gen [Value]
      extractArg types tuple =
          do (_, _, projs) <- lookupCtor types
             debug ("extractArg start: " ++ show types)
             asts <- mapM (\ proj -> mkApp proj [tuple]) projs
             astsStr <- mapM astToString (tuple:asts)
             debug (unlines (map ("extArg: " ++) astsStr))
             zipWithM extract types asts

      -- | Extract a Boogaloo function entry
      extractEntry :: [Type] -> Type -> [AST] -> AST -> Z3Gen ([Value], Value)
      extractEntry argTypes resType [argTuple] res =
          do debug "Entry start" 
             args <- extractArg argTypes argTuple
             debug "Extracted arg"
             res' <- extract resType res
             debug "Extracted res"
             return (args, res')

      -- | Extract the new custom values from the model.
      customSet :: Z3Gen (Set NewCustomVal)
      customSet = return (Set.singleton (error "customSet"))

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
             !elsePart <- extract res (interpElse funcModel)
             debug "extracted else"
             entries <- mapM (uncurry (extractEntry args res))
                             (interpMap funcModel)
             let m = Map.fromList entries
                 mapWithElse = MapWithElse m elsePart
             debug "reconMap end"
             return (ref, mapWithElse)

      -- | Reconstruct a ref/value pair for a logical reference.
      reconLogicRef :: TaggedRef -> AST -> Z3Gen (Ref, Value)
      reconLogicRef (LogicRef t ref) ast =
          do Just ast' <- eval model ast
             x <- extract t ast'
             return (ref, x)
      reconLogicRef tr _ast = 
          error $ "reconLogicRef: not a logical ref" ++ show tr

debug :: MonadIO m => String -> m ()
debug = const (return ()) -- liftIO . putStrLn