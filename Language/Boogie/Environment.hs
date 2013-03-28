{-# LANGUAGE TemplateHaskell, Rank2Types #-}

-- | Execution state for the interpreter
module Language.Boogie.Environment ( 
  flattenMap,
  mapSource,
  mapValues,
  deepDeref,
  objectEq,
  mustAgree,
  mustDisagree,
  Store,
  emptyStore,
  userStore,
  storeDoc,
  Memory,
  StoreLens,
  memLocals,
  memGlobals,
  memOld,
  memModified,
  memConstants,
  memHeap,
  emptyMemory,
  visibleVariables,
  memoryDoc,
  SymbolicMemory,
  symLocals,
  symGlobals,
  symHeap,
  Environment,
  envMemory,
  envProcedures,
  envConstraints,
  envTypeContext,
  envGenerator,
  envCustomCount,
  envQBound,
  envInOld,
  envLastTerm,
  initEnv,
  lookupProcedure,
  lookupNameConstraints,
  lookupValueConstraints,
  lookupCustomCount,
  addProcedureImpl,
  addGlobalDefinition,
  addGlobalConstraint,
  addValueDefinition,
  addValueConstraint,
  setCustomCount,
  withHeap,
) where

import Language.Boogie.Util
import Language.Boogie.Position
import Language.Boogie.AST
import Language.Boogie.Heap
import Language.Boogie.Generator
import Language.Boogie.TypeChecker (Context)
import Language.Boogie.Pretty
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Lens hiding (Context, at)
  
{- Map operations -}

-- | Source reference and key-value pairs of a reference in a heap
flattenMap :: Heap Value -> Ref -> (Ref, (Map [Value] Value))
flattenMap h r = case unValueMap $ h `at` r of
  Source vals -> (r, vals)
  Derived base override -> let (s, v) = flattenMap h base
    in (s, override `M.union` v)
    
-- | First component of 'flattenMap'
mapSource h r = flattenMap h r ^. _1

-- | Second component of 'flattenMap'
mapValues h r = flattenMap h r ^. _2

-- | 'deepDeref' @h v@: Completely dereference value @v@ given heap @h@ (so that no references are left in @v@)
deepDeref :: Heap Value -> Value -> Value
deepDeref h v = deepDeref' v
  where
    deepDeref' (Reference r) = let vals = mapValues h r
      in MapValue . Source $ (M.map deepDeref' . M.mapKeys (map deepDeref') . M.filter (not . isAux)) vals -- Here we do not assume that keys contain no references, as this is used for error reporting
    deepDeref' (MapValue _) = internalError $ text "Attempt to dereference a map directly"
    deepDeref' v = v
    isAux (CustomValue id _) | id == refIdTypeName = True
    isAux _ = False

-- | 'objectEq' @h v1 v2@: is @v1@ equal to @v2@ in the Boogie semantics? Nothing if cannot be determined.
objectEq :: Heap Value -> Value -> Value -> Maybe Bool
objectEq h (Reference r1) (Reference r2) = if r1 == r2
  then Just True -- Equal references point to equal maps
  else let 
    (s1, vals1) = flattenMap h r1
    (s2, vals2) = flattenMap h r2
    in if mustDisagree h vals1 vals2
      then Just False
      else if s1 == s2 && mustAgree h vals1 vals2
        then Just True
        else Nothing
objectEq _ (MapValue _) (MapValue _) = internalError $ text "Attempt to compare two maps"
objectEq _ v1 v2 = Just $ v1 == v2

mustEq h v1 v2 = case objectEq h v1 v2 of
  Just True -> True
  _ -> False  
mustNeq h v1 v2 = case objectEq h v1 v2 of
  Just False -> True
  _ -> False  
mayEq h v1 v2 = not $ mustNeq h v1 v2
mayNeq h v1 v2 = not $ mustEq h v1 v2

mustDisagree h vals1 vals2 = M.foldl (||) False $ (M.intersectionWith (mustNeq h) vals1 vals2)

mustAgree h vals1 vals2 = let common = M.intersectionWith (mustEq h) vals1 vals2 in
      M.size vals1 == M.size common && M.size vals2 == M.size common && M.foldl (&&) True common
  
{- Store -}  

-- | Store: stores variable values at runtime 
type Store = Map Id Value

-- | A store with no variables
emptyStore :: Store
emptyStore = M.empty

-- | Pretty-printed store
storeDoc :: Store -> Doc
storeDoc vars = vsep $ map varDoc (M.toList vars)
  where varDoc (id, val) = text id <+> text "=" <+> pretty val
  
-- | 'userStore' @heap store@ : @store@ with all reference values completely dereferenced given @heap@, and all auxiliary values removed
userStore :: Heap Value -> Store -> Store
userStore heap store = M.map (deepDeref heap) store

{- Memory -}

-- | Memory: stores concrete values associated with names and references
data Memory = Memory {
  _memLocals :: Store,      -- ^ Local variable store
  _memGlobals :: Store,     -- ^ Global variable store
  _memOld :: Store,         -- ^ Old global variable store (in two-state contexts)
  _memModified :: Set Id,   -- ^ Set of global variables, which have been modified since the beginning of the current procedure
  _memConstants :: Store,   -- ^ Constant and function cache
  _memHeap :: Heap Value    -- ^ Heap
} deriving Eq

makeLenses ''Memory

-- | Lens that selects a store from memory
type StoreLens = SimpleLens Memory Store

-- | Empty memory
emptyMemory = Memory {
  _memLocals = emptyStore,
  _memGlobals = emptyStore,
  _memOld = emptyStore,
  _memModified = S.empty,
  _memConstants = emptyStore,
  _memHeap = emptyHeap
}

-- | Visible values of all identifiers in a memory (locals shadow globals) 
visibleVariables :: Memory -> Store
visibleVariables mem = (mem^.memLocals) `M.union` (mem^.memGlobals) `M.union` (mem^.memConstants)

-- | 'memoryDoc' @debug mem@ : either user or debug representation of @mem@, depending on @debug@
memoryDoc :: Bool -> Memory -> Doc
memoryDoc debug mem = vsep $ [text "Locals:" <+> storeDoc (storeRepr $ mem^.memLocals),
  text "Globals:" <+> storeDoc (storeRepr $ (mem^.memGlobals) `M.union` (mem^.memConstants)),
  text "Old values:" <+> storeDoc (storeRepr $ mem^.memOld),
  text "Modified:" <+> commaSep (map text (S.toList $ mem^.memModified))]
  ++ if debug then [text "Heap:" <+> heapDoc (mem^.memHeap)] else []
  where
    storeRepr store = if debug then store else userStore (mem^.memHeap) store
    
instance Pretty Memory where
  pretty mem = memoryDoc True mem
  
{- Symbolic memory -}

-- | Symbolic heap: maps logical variables to ground constraints
type SymbolicHeap = Map Ref ConstraintSet

-- | Symbolic memory: stores name and value constraints
data SymbolicMemory = SymbolicMemory {
  _symLocals :: SymbolicStore,       -- ^ Local name constraints
  _symGlobals :: SymbolicStore,      -- ^ Global name constraints
  _symHeap :: SymbolicHeap           -- ^ Value constraints
}

makeLenses ''SymbolicMemory

-- | Empty abstract memory
emptySymbolicMemory = SymbolicMemory {
  _symLocals = M.empty,
  _symGlobals = M.empty,
  _symHeap = M.empty
}

{- Environment -}
  
-- | Execution state
data Environment m = Environment
  {
    _envMemory :: Memory,                   -- ^ Concrete values
    _envConstraints :: SymbolicMemory,      -- ^ Abstract values
    _envProcedures :: Map Id [PDef],        -- ^ Procedure implementations
    _envTypeContext :: Context,             -- ^ Type context
    _envGenerator :: Generator m,           -- ^ Input generator (used for non-deterministic choices)
    _envCustomCount :: Map Id Int,          -- ^ For each user-defined type, number of distinct values of this type already generated
    _envQBound :: Maybe Integer,            -- ^ Maximum number of values to try for a quantified variable (unbounded if Nothing)
    _envInOld :: Bool,                      -- ^ Is an old expression currently being evaluated?
    _envLastTerm :: Maybe Expression        -- ^ Last evaluated term (used to determine which part of short-circuit expression determined its result)
  }
  
makeLenses ''Environment
   
-- | 'initEnv' @tc gen@: Initial environment in a type context @tc@ with a value generator @gen@  
initEnv tc gen qbound = Environment
  {
    _envMemory = emptyMemory,
    _envConstraints = emptySymbolicMemory,
    _envProcedures = M.empty,
    _envTypeContext = tc,
    _envGenerator = gen,
    _envCustomCount = M.empty,
    _envQBound = qbound,
    _envInOld = False,
    _envLastTerm = Nothing
  }
  
-- | 'lookupGetter' @getter def key env@ : lookup @key@ in a map accessible with @getter@ from @env@; if it does not occur return @def@
lookupGetter getter def key env = case M.lookup key (env ^. getter) of
  Nothing -> def
  Just val -> val
  
combineGetters f g1 g2 = to $ \env -> (env ^. g1) `f` (env ^. g2)  
  
-- Environment queries  
lookupProcedure = lookupGetter envProcedures []  
lookupNameConstraints = lookupGetter (combineGetters M.union (envConstraints.symLocals) (envConstraints.symGlobals)) ([], [])
lookupValueConstraints = lookupGetter (envConstraints.symHeap) ([], [])
lookupCustomCount = lookupGetter envCustomCount 0

-- Environment modifications  
addProcedureImpl name def env = over envProcedures (M.insert name (lookupProcedure name env ++ [def])) env
addGlobalDefinition name def env = over (envConstraints.symGlobals) (M.insert name (over _1 (++ [def]) (lookupGetter (envConstraints.symGlobals) ([], []) name env))) env
addGlobalConstraint name def env = over (envConstraints.symGlobals) (M.insert name (over _2 (++ [def]) (lookupGetter (envConstraints.symGlobals) ([], []) name env))) env
addValueDefinition r def env = over (envConstraints.symHeap) (M.insert r (over _1 (++ [def]) (lookupValueConstraints r env))) env
addValueConstraint r constraint env = over (envConstraints.symHeap) (M.insert r (over _2 (++ [constraint]) (lookupValueConstraints r env))) env
setCustomCount t n = over envCustomCount (M.insert t n)
withHeap f env = let (res, h') = f (env^.envMemory.memHeap) 
  in (res, set (envMemory.memHeap) h' env )  
