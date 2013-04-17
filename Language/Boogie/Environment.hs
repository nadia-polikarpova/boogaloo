{-# LANGUAGE TemplateHaskell, Rank2Types, FlexibleInstances, TypeSynonymInstances #-}

-- | Execution state for the interpreter
module Language.Boogie.Environment ( 
  -- deepDeref,
  Store,
  emptyStore,
  userStore,
  storeDoc,
  MapCache,
  Solution,
  Memory,
  StoreLens,
  memLocals,
  memGlobals,
  memOld,
  memModified,
  memConstants,
  memMaps,
  memLogical,
  emptyMemory,
  visibleVariables,
  userMemory,
  memoryDoc,
  ConstraintSet,
  Solver,
  NameConstraints,
  nameConstraintsDoc,
  MapConstraints,
  mapConstraintsDoc,
  constraintUnion,  
  ConstraintMemory,
  conLocals,
  conGlobals,
  conMaps,
  conLogical,
  Environment,
  envMemory,
  envProcedures,
  envConstraints,
  envTypeContext,
  envSolver,
  envCustomCount,
  envLogicalCount,
  envInOld,
  initEnv,
  lookupProcedure,
  lookupNameConstraints,
  lookupMapConstraints,
  lookupCustomCount,
  addProcedureImpl,
  addNameConstraint,
  addMapConstraint,
  addConstraints,
  setCustomCount,
  withHeap,
  markModified
) where

import Language.Boogie.Util
import Language.Boogie.Position
import Language.Boogie.AST
import Language.Boogie.Heap
import Language.Boogie.TypeChecker (Context, ctxGlobals)
import Language.Boogie.Pretty
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Lens hiding (Context, at)
  
{- Map operations -}

-- -- | 'deepDeref' @h v@: Completely dereference value @v@ given heap @h@ (so that no references are left in @v@)
-- deepDeref :: Heap MapCache -> Value -> Value
-- deepDeref h v = deepDeref' v
  -- where
    -- deepDeref' (Reference t r) = MapValue t $ M.map deepDeref' (M.mapKeys (map deepDeref') (h `at` r)) -- Dereference all keys and values
    -- deepDeref' v = v
  
{- Store -}  

-- | Store: stores variable values at runtime 
type Store = Map Id Thunk

-- | A store with no variables
emptyStore :: Store
emptyStore = M.empty

-- | Pretty-printed store
storeDoc vars = vsep $ map varDoc (M.toList vars)
  where varDoc (id, val) = pretty id <+> text "=" <+> pretty val
    
-- | 'userStore' @heap store@ : @store@ with all reference values completely dereferenced given @heap@
userStore :: Heap MapCache -> Store -> Store
userStore heap store = store-- M.map (deepDeref heap . fromLiteral) store    

-- | Partial map instance
type MapCache = Map [Value] Thunk

instance Pretty MapCache where
  pretty cache = let
      keysDoc keys = ((if length keys > 1 then parens else id) . commaSep . map pretty) keys
      itemDoc (keys, v) = keysDoc keys  <+> text "->" <+> pretty v
    in brackets (commaSep (map itemDoc (M.toList cache)))
        
type Solution = Map Ref Thunk

{- Memory -}

-- | Memory: stores thunks associated with names, map references and logical variables
data Memory = Memory {
  _memLocals :: Store,          -- ^ Local variable store
  _memGlobals :: Store,         -- ^ Global variable store
  _memOld :: Store,             -- ^ Old global variable store (in two-state contexts)
  _memModified :: Set Id,       -- ^ Set of global variables, which have been modified since the beginning of the current procedure  
  _memConstants :: Store,       -- ^ Constant store  
  _memMaps :: Heap MapCache,    -- ^ Partial instances of maps
  _memLogical :: Solution       -- ^ Logical variable store
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
  _memMaps = emptyHeap,
  _memLogical = M.empty
}

-- | Visible values of all identifiers in a memory (locals shadow globals) 
visibleVariables :: Memory -> Store
visibleVariables mem = (mem^.memLocals) `M.union` (mem^.memGlobals) `M.union` (mem^.memConstants)

-- | Clear cached values if maps that have guard-less definitions
clearDefinedCache :: MapConstraints -> Heap MapCache -> Heap MapCache
clearDefinedCache conMaps heap = heap --foldr (\r -> update r emptyMap) heap definedRefs -- ToDo: fix!
  -- where
    -- definedRefs = [r | (r, (defs, _)) <- M.toList conMaps, any (\def -> node (defGuard def) == tt) defs]

-- | 'userStore' @conMem mem@ : @mem@ with all reference values completely dereferenced and cache of defined maps removed 
userMemory :: ConstraintMemory -> Memory -> Memory
userMemory conMem mem = let heap' = clearDefinedCache (_conMaps conMem) (mem^.memMaps)
  in over memLocals (userStore heap') $
     over memGlobals (userStore heap') $
     over memOld (userStore heap') $
     over memModified (const S.empty) $
     over memConstants (userStore heap') $
     over memMaps (const emptyHeap)
     mem

-- | 'memoryDoc' @inNames outNames mem@ : pretty-printed @mem@ where
-- locals in @inNames@ will be printed as input variables
-- and locals in @outNames@ will be printed as output variables
memoryDoc :: [Id] -> [Id] -> Memory -> Doc
memoryDoc inNames outNames mem = vsep $ 
  docNonEmpty ins (labeledStoreDoc "Ins") ++
  docNonEmpty locals (labeledStoreDoc "Locals") ++
  docNonEmpty outs (labeledStoreDoc "Outs") ++
  docNonEmpty ((mem^.memGlobals) `M.union` (mem^.memConstants)) (labeledStoreDoc "Globals") ++
  docNonEmpty (mem^.memOld) (labeledStoreDoc "Old globals") ++
  docWhen (not (S.null $ mem^.memModified)) (text "Modified:" <+> commaSep (map text (S.toList $ mem^.memModified))) ++
  docWhen (mem^.memMaps /= emptyHeap) (text "Maps:" <+> align (heapDoc (mem^.memMaps))) ++
  docNonEmpty (mem^.memLogical) (labeledStoreDoc "Logical")
  where
    allLocals = mem^.memLocals
    ins = restrictDomain (S.fromList inNames) allLocals
    outs = restrictDomain (S.fromList outNames) allLocals
    locals = removeDomain (S.fromList $ inNames ++ outNames) allLocals
    labeledStoreDoc label store = (text label <> text ":") <+> align (storeDoc store)
    docWhen flag doc = if flag then [doc] else [] 
    docNonEmpty m mDoc = docWhen (not (M.null m)) (mDoc m)
    
instance Pretty Memory where
  pretty mem = memoryDoc [] [] mem
  
{- Constraint memory -}

-- | Set of constraints
type ConstraintSet = [Expression]

-- | Solver: produces solutions of constraint sets
type Solver m = ConstraintSet -> m Solution

-- | Mapping from names to their constraints
type NameConstraints = Map Id ConstraintSet

-- | Pretty-printed variable constraints
nameConstraintsDoc :: NameConstraints -> Doc
nameConstraintsDoc vars = vsep $ map varDoc (M.toList vars)
  where varDoc (name, cs) = nest 2 (text name <+> pretty cs)

-- | Mapping from map references to their parametrized constraints
type MapConstraints = Map Ref ConstraintSet

mapConstraintsDoc heap = vsep $ map valDoc (M.toList heap)
  where valDoc (r, cs) = nest 2 (refDoc r <+> pretty cs)
  
-- | Union of constraints (values at the same key are concatenated)
constraintUnion s1 s2 = M.unionWith (++) s1 s2  

-- | Constraint memory: stores constraints associated with names, map references and logical variables
data ConstraintMemory = ConstraintMemory {
  _conLocals :: NameConstraints,        -- ^ Local name constraints
  _conGlobals :: NameConstraints,       -- ^ Global name constraints
  _conMaps :: MapConstraints,           -- ^ Parametrized map constraints
  _conLogical :: ConstraintSet          -- ^ Constraint on logical variables
}

makeLenses ''ConstraintMemory

-- | Symbolic memory with no constraints
emptyConstraintMemory = ConstraintMemory {
  _conLocals = M.empty,
  _conGlobals = M.empty,
  _conMaps = M.empty,
  _conLogical = []
}

symbolicMemoryDoc :: ConstraintMemory -> Doc
symbolicMemoryDoc mem = vsep $ 
  docNonEmpty (mem^.conLocals) (labeledStoreDoc "Local con") ++
  docNonEmpty (mem^.conGlobals) (labeledStoreDoc "Global con") ++
  docNonEmpty (mem^.conMaps) (\h -> text "Map con:" <+> align (mapConstraintsDoc h)) ++
  docWhen (not $ null (mem^.conLogical)) (text "Logical con:" <+> align (vsep (map pretty (mem^.conLogical))))
  where
    labeledStoreDoc label store = (text label <> text ":") <+> align (nameConstraintsDoc store)
    docWhen flag doc = if flag then [doc] else [] 
    docNonEmpty m mDoc = docWhen (not (M.null m)) (mDoc m)
    
instance Pretty ConstraintMemory where
  pretty = symbolicMemoryDoc

{- Environment -}
  
-- | Execution state
data Environment m = Environment
  {
    _envMemory :: Memory,                   -- ^ Values
    _envConstraints :: ConstraintMemory,    -- ^ Constraints
    _envProcedures :: Map Id [PDef],        -- ^ Procedure implementations
    _envTypeContext :: Context,             -- ^ Type context
    _envSolver :: Solver m,                 -- ^ Constraint solver
    _envLogicalCount :: Int,                -- ^ Number of logical varibles currently in use
    _envCustomCount :: Map Type Int,        -- ^ For each user-defined type, number of distinct values of this type already generated
    _envInOld :: Bool                       -- ^ Is an old expression currently being evaluated?
  }
  
makeLenses ''Environment
   
-- | 'initEnv' @tc s@: Initial environment in a type context @tc@ with constraint solver @s@  
initEnv tc s = Environment
  {
    _envMemory = emptyMemory,
    _envConstraints = emptyConstraintMemory,
    _envProcedures = M.empty,
    _envTypeContext = tc,
    _envSolver = s,
    _envCustomCount = M.empty,
    _envLogicalCount = 0,
    _envInOld = False
  }
  
-- | 'lookupGetter' @getter def key env@ : lookup @key@ in a map accessible with @getter@ from @env@; if it does not occur return @def@
lookupGetter getter def key env = case M.lookup key (env ^. getter) of
  Nothing -> def
  Just val -> val
  
combineGetters f g1 g2 = to $ \env -> (env ^. g1) `f` (env ^. g2)  
  
-- Environment queries  
lookupProcedure = lookupGetter envProcedures []  
lookupNameConstraints = lookupGetter (combineGetters M.union (envConstraints.conLocals) (envConstraints.conGlobals)) []
lookupMapConstraints = lookupGetter (envConstraints.conMaps) []
lookupCustomCount = lookupGetter envCustomCount 0

-- Environment modifications  
addProcedureImpl name def env = over envProcedures (M.insert name (lookupProcedure name env ++ [def])) env
addNameConstraint :: Id -> SimpleLens (Environment m) NameConstraints -> Expression -> Environment m -> Environment m
addNameConstraint name lens con env = over lens (M.insert name (nub $ lookupGetter lens [] name env ++ [con])) env
addMapConstraint r con env = over (envConstraints.conMaps) (M.insert r (nub $ lookupMapConstraints r env ++ [con])) env
addConstraints cs = over (envConstraints.conLogical) (++ cs)
setCustomCount t n = over envCustomCount (M.insert t n)
withHeap f env = let (res, h') = f (env^.envMemory.memMaps) 
  in (res, set (envMemory.memMaps) h' env )
markModified name env = if M.member name (env^.envTypeContext.to ctxGlobals) 
  then over (envMemory.memModified) (S.insert name) env
  else env
