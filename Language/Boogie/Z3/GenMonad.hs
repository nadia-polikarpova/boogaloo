{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Boogie.Z3.GenMonad where

import           Control.Applicative
import           Control.Lens ((%=), uses, makeLenses)
import           Control.Monad.Trans.State
import           Control.Monad.Trans

import           Data.List (intercalate)
import           Data.Maybe
import qualified Data.Map as Map
import           Data.Map (Map)

import           Z3.Monad

import           Language.Boogie.AST
import           Language.Boogie.Heap
import           Language.Boogie.PrettyAST ()

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

debug :: MonadIO m => String -> m ()
debug = const (return ()) -- liftIO . putStrLn

lookup' :: Ord k => String -> k -> Map k a -> a
lookup' errMsg key m =
  case Map.lookup key m of
    Just a -> a
    Nothing -> error errMsg

justElse :: Maybe a -> a -> a
justElse = flip fromMaybe

justElseM :: Monad m => Maybe a -> m a -> m a
justElseM mb v = maybe v return mb



lookupSort :: Type -> Z3Gen Sort
lookupSort ttype =
    do sortMb <- uses sortMap (Map.lookup ttype)
       justElseM sortMb $
         do s <- typeToSort ttype
            sortMap %= Map.insert ttype s
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
     _ -> error $ "typeString: no string for " ++ show t
