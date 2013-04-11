{-# LANGUAGE TemplateHaskell, Rank2Types #-}

-- | Execution state for the interpreter
module Language.Boogie.Environment ( 
  deepDeref,
  objectEq,
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
  userMemory,
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
  envInDef,
  envLastTerm,
  initEnv,
  lookupProcedure,
  lookupNameConstraints,
  lookupValueConstraints,
  lookupCustomCount,
  addProcedureImpl,
  addGlobalDefinition,
  addGlobalConstraint,
  addMapDefinition,
  addMapConstraint,
  setCustomCount,
  withHeap,
  markModified
) where

import Language.Boogie.Util
import Language.Boogie.Position
import Language.Boogie.AST
import Language.Boogie.Heap
import Language.Boogie.Generator
import Language.Boogie.TypeChecker (Context, ctxGlobals)
import Language.Boogie.Pretty
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Lens hiding (Context, at)
  
{- Map operations -}

-- | 'deepDeref' @h v@: Completely dereference value @v@ given heap @h@ (so that no references are left in @v@)
deepDeref :: Heap MapRepr -> Value -> Value
deepDeref h v = deepDeref' v
  where
    deepDeref' (Reference t r) = MapValue t $ M.map deepDeref' (M.mapKeys (map deepDeref') (h `at` r)) -- Dereference all keys and values
    deepDeref' v = v

-- | 'objectEq' @h v1 v2@: is @v1@ equal to @v2@ in the Boogie semantics? Nothing if cannot be determined.
objectEq :: Heap MapRepr -> Value -> Value -> Maybe Bool
objectEq h (Reference t1 r1) (Reference t2 r2) = if r1 == r2
  then Just True -- Equal references point to equal maps
  else if t1 /= t2 -- Different types can occur in a generic context
    then Just False
    else let 
      vals1 = h `at` r1
      vals2 = h `at` r2
      in if mustDisagree h vals1 vals2
          then Just False
          else Nothing
objectEq _ (MapValue _ _) (MapValue _ _) = internalError $ text "Attempt to compare two maps"
objectEq _ v1 v2 = Just $ v1 == v2

mustNeq h v1 v2 = case objectEq h v1 v2 of
  Just False -> True
  _ -> False  

mustDisagree h vals1 vals2 = M.foldl (||) False $ (M.intersectionWith (mustNeq h) vals1 vals2)
  
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
    
-- | 'userStore' @heap store@ : @store@ with all reference values completely dereferenced given @heap@
userStore :: Heap MapRepr -> Store -> Store
userStore heap store = M.map (deepDeref heap) store    

{- Memory -}

-- | Memory: stores concrete values associated with names and references
data Memory = Memory {
  _memLocals :: Store,      -- ^ Local variable store
  _memGlobals :: Store,     -- ^ Global variable store
  _memOld :: Store,         -- ^ Old global variable store (in two-state contexts)
  _memModified :: Set Id,   -- ^ Set of global variables, which have been modified since the beginning of the current procedure
  _memConstants :: Store,   -- ^ Constant and function cache
  _memHeap :: Heap MapRepr  -- ^ Heap
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

-- | Clear cached values if maps that have guard-less definitions
clearDefinedCache :: MapConstraints -> Heap MapRepr -> Heap MapRepr
clearDefinedCache symHeap heap = foldr (\r -> update r emptyMap) heap definedRefs
  where
    definedRefs = [r | (r, (defs, _)) <- M.toList symHeap, any (\def -> node (defGuard def) == tt) defs]

-- | 'userStore' @symMem mem@ : @mem@ with all reference values completely dereferenced and cache of defined maps removed 
userMemory :: SymbolicMemory -> Memory -> Memory
userMemory symMem mem = let heap' = clearDefinedCache (_symHeap symMem) (mem^.memHeap)
  in over memLocals (userStore heap') $
     over memGlobals (userStore heap') $
     over memOld (userStore heap') $
     over memModified (const S.empty) $
     over memConstants (userStore heap') $
     over memHeap (const emptyHeap)
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
  docWhen (mem^.memHeap /= emptyHeap) (text "Heap:" <+> align (heapDoc (mem^.memHeap)))
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

-- | Symbolic memory: stores name and value constraints
data SymbolicMemory = SymbolicMemory {
  _symLocals :: NameConstraints,       -- ^ Local name constraints
  _symGlobals :: NameConstraints,      -- ^ Global name constraints
  _symHeap :: MapConstraints           -- ^ Value constraints
}

makeLenses ''SymbolicMemory

-- | Empty abstract memory
emptySymbolicMemory = SymbolicMemory {
  _symLocals = M.empty,
  _symGlobals = M.empty,
  _symHeap = M.empty
}

symbolicMemoryDoc :: SymbolicMemory -> Doc
symbolicMemoryDoc mem = vsep $ 
  docNonEmpty (mem^.symLocals) (labeledStoreDoc "SLocals") ++
  docNonEmpty (mem^.symGlobals) (labeledStoreDoc "SGlobals") ++
  docNonEmpty (mem^.symHeap) (\h -> text "SHeap:" <+> align (mapConstraintsDoc h))
  where
    labeledStoreDoc label store = (text label <> text ":") <+> align (nameConstraintsDoc store)
    docWhen flag doc = if flag then [doc] else [] 
    docNonEmpty m mDoc = docWhen (not (M.null m)) (mDoc m)
    
instance Pretty SymbolicMemory where
  pretty = symbolicMemoryDoc

{- Environment -}
  
-- | Execution state
data Environment m = Environment
  {
    _envMemory :: Memory,                   -- ^ Concrete values
    _envConstraints :: SymbolicMemory,      -- ^ Abstract values
    _envProcedures :: Map Id [PDef],        -- ^ Procedure implementations
    _envTypeContext :: Context,             -- ^ Type context
    _envGenerator :: Generator m,           -- ^ Input generator (used for non-deterministic choices)
    _envCustomCount :: Map Type Int,        -- ^ For each user-defined type, number of distinct values of this type already generated
    _envQBound :: Maybe Integer,            -- ^ Maximum number of values to try for a quantified variable (unbounded if Nothing)
    _envInOld :: Bool,                      -- ^ Is an old expression currently being evaluated?
    _envInDef :: Bool,                      -- ^ Is a definition currently being evaluated?
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
    _envInDef = False,
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
addMapDefinition r def env = over (envConstraints.symHeap) (M.insert r (over _1 (++ [def]) (lookupValueConstraints r env))) env
addMapConstraint r constraint env = over (envConstraints.symHeap) (M.insert r (over _2 (++ [constraint]) (lookupValueConstraints r env))) env
setCustomCount t n = over envCustomCount (M.insert t n)
withHeap f env = let (res, h') = f (env^.envMemory.memHeap) 
  in (res, set (envMemory.memHeap) h' env )
markModified name env = if M.member name (env^.envTypeContext.to ctxGlobals) 
  then over (envMemory.memModified) (S.insert name) env
  else env
