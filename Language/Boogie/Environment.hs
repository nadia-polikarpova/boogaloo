{-# LANGUAGE TemplateHaskell, Rank2Types #-}

-- | Execution state for the interpreter
module Language.Boogie.Environment ( 
  MapRepr (..),
  emptyMap,
  stored,
  Value (..),
  valueFromInteger,
  vnot,
  unValueBool,
  unValueMap,
  flattenMap,
  mapSource,
  mapValues,
  deepDeref,
  objectEq,
  mustAgree,
  mustDisagree,
  valueDoc,
  Store,
  emptyStore,
  userStore,
  storeDoc,
  Memory,
  StoreLens,
  memLocals,
  memGlobals,
  memOld,
  memConstants,
  memHeap,
  emptyMemory,
  visibleVariables,
  memoryDoc,
  AbstractMemory,
  amLocals,
  amGlobals,
  amHeap,
  Environment,
  envMemory,
  envProcedures,
  envConstraints,
  envTypeContext,
  envGenerator,
  envCustomCount,
  envQBound,
  envInOld,
  initEnv,
  lookupProcedure,
  lookupNameConstraints,
  lookupMapConstraints,
  lookupCustomCount,
  addProcedureImpl,
  addGlobalDefinition,
  addGlobalConstraint,
  addMapDefinition,
  addMapConstraint,
  setCustomCount,
  withHeap,
) where

import Language.Boogie.Util
import Language.Boogie.Position
import Language.Boogie.AST
import Language.Boogie.Heap
import Language.Boogie.Generator
import Language.Boogie.TypeChecker (Context)
import Language.Boogie.PrettyPrinter
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Lens hiding (Context, at)
import Text.PrettyPrint

{- Values -}

-- | Representation of a map value
data MapRepr = 
  Source (Map [Value] Value) |    -- ^ Map that comes directly from a non-deterministic choice, possibly with some key-value pairs defined
  Derived Ref (Map [Value] Value) -- ^ Map that is derived from another map by redefining values at some keys
  deriving (Eq, Ord)
  
-- | Representation of an empty map  
emptyMap = Source M.empty

-- | Key-value pairs stored explicitly in a map representation
stored :: MapRepr -> Map [Value] Value
stored (Source vals) = vals
stored (Derived _ override) = override
  
-- | Pretty-printed map representation  
mapReprDoc :: MapRepr -> Doc
mapReprDoc repr = case repr of
  Source vals -> brackets (commaSep (map itemDoc (M.toList vals)))
  Derived base override -> refDoc base <> 
    brackets (commaSep (map itemDoc (M.toList override))) 
  where
    keysDoc keys = ((if length keys > 1 then parens else id) . commaSep . map valueDoc) keys
    itemDoc (keys, v) = keysDoc keys  <+> text "->" <+> valueDoc v

-- | Run-time value
data Value = IntValue Integer |  -- ^ Integer value
  BoolValue Bool |               -- ^ Boolean value
  CustomValue Id Int |           -- ^ Value of a user-defined type
  MapValue MapRepr |             -- ^ Value of a map type: consists of an optional reference to the base map (if derived from base by updating) and key-value pairs that override base
  Reference Ref                  -- ^ Reference to a map stored in the heap
  deriving (Eq, Ord)
  
-- | 'valueFromInteger' @t n@: value of type @t@ with an integer code @n@
valueFromInteger :: Type -> Integer -> Value  
valueFromInteger IntType n        = IntValue n
valueFromInteger (IdType id _) n  = CustomValue id (fromInteger n)
valueFromInteger _ _              = error "cannot create a boolean or map value from integer" 
  
unValueBool (BoolValue b) = b  
vnot (BoolValue b) = BoolValue (not b)

unValueMap (MapValue repr) = repr

-- | Pretty-printed value
valueDoc :: Value -> Doc
valueDoc (IntValue n) = integer n
valueDoc (BoolValue False) = text "false"
valueDoc (BoolValue True) = text "true"
valueDoc (MapValue repr) = mapReprDoc repr
valueDoc (CustomValue t n) = text t <+> int n
valueDoc (Reference r) = refDoc r

instance Show Value where
  show v = show (valueDoc v)
  
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
    deepDeref' (MapValue _) = internalError "Attempt to dereference a map directly"
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
objectEq _ (MapValue _) (MapValue _) = internalError "Attempt to compare two maps"
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
  where varDoc (id, val) = text id <+> text "=" <+> valueDoc val
  
-- | 'userStore' @heap store@ : @store@ with all reference values completely dereferenced given @heap@, and all auxiliary values removed
userStore :: Heap Value -> Store -> Store
userStore heap store = M.map (deepDeref heap) store

{- Memory -}

-- | Memory: stores concrete values associated with names and references
data Memory = Memory {
  _memLocals :: Store,      -- ^ Local variable store
  _memGlobals :: Store,     -- ^ Global variable store
  _memOld :: Store,         -- ^ Old global variable store (in two-state contexts)
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
  text "Old values:" <+> storeDoc (storeRepr $ mem^.memOld)]
  ++ if debug then [text "Heap:" <+> heapDoc (mem^.memHeap)] else []
  where
    storeRepr store = if debug then store else userStore (mem^.memHeap) store
    
instance Show Memory where
  show mem = show $ memoryDoc True mem
  
{- Abstract memory -}

-- | Abstract memory: stores constraints associated with names and references
data AbstractMemory = AbstractMemory {
  _amLocals :: AbstractStore,       -- ^ Local name constraints
  _amGlobals :: AbstractStore,      -- ^ Global name constraints
  _amHeap :: Map Ref ConstraintSet  -- ^ Reference constraints
}

makeLenses ''AbstractMemory

-- | Empty abstract memory
emptyAbstractMemory = AbstractMemory {
  _amLocals = M.empty,
  _amGlobals = M.empty,
  _amHeap = M.empty
}

{- Environment -}
  
-- | Execution state
data Environment m = Environment
  {
    _envMemory :: Memory,                   -- ^ Concrete values
    _envConstraints :: AbstractMemory,      -- ^ Abstract values
    _envProcedures :: Map Id [PDef],        -- ^ Procedure implementations
    _envTypeContext :: Context,             -- ^ Type context
    _envGenerator :: Generator m,           -- ^ Input generator (used for non-deterministic choices)
    _envCustomCount :: Map Id Int,          -- ^ For each user-defined type, number of distinct values of this type already generated
    _envQBound :: Maybe Integer,            -- ^ Maximum number of values to try for a quantified variable (unbounded if Nothing)
    _envInOld :: Bool                       -- ^ Is an old expression currently being evaluated?
  }
  
makeLenses ''Environment
   
-- | 'initEnv' @tc gen@: Initial environment in a type context @tc@ with a value generator @gen@  
initEnv tc gen qbound = Environment
  {
    _envMemory = emptyMemory,
    _envConstraints = emptyAbstractMemory,
    _envProcedures = M.empty,
    _envTypeContext = tc,
    _envGenerator = gen,
    _envCustomCount = M.empty,
    _envQBound = qbound,
    _envInOld = False
  }
  
-- | 'lookupGetter' @getter def key env@ : lookup @key@ in a map accessible with @getter@ from @env@; if it does not occur return @def@
lookupGetter getter def key env = case M.lookup key (env ^. getter) of
  Nothing -> def
  Just val -> val
  
combineGetters f g1 g2 = to $ \env -> (env ^. g1) `f` (env ^. g2)  
  
-- Environment queries  
lookupProcedure = lookupGetter envProcedures []  
lookupNameConstraints = lookupGetter (combineGetters M.union (envConstraints.amLocals) (envConstraints.amGlobals)) ([], [])
lookupMapConstraints = lookupGetter (envConstraints.amHeap) ([], [])
lookupCustomCount = lookupGetter envCustomCount 0

-- Environment modifications  
addProcedureImpl name def env = over envProcedures (M.insert name (lookupProcedure name env ++ [def])) env
addGlobalDefinition name def env = over (envConstraints.amGlobals) (M.insert name (over _1 (++ [def]) (lookupGetter (envConstraints.amGlobals) ([], []) name env))) env
addGlobalConstraint name def env = over (envConstraints.amGlobals) (M.insert name (over _2 (++ [def]) (lookupGetter (envConstraints.amGlobals) ([], []) name env))) env
addMapDefinition r def env = over (envConstraints.amHeap) (M.insert r (over _1 (++ [def]) (lookupMapConstraints r env))) env
addMapConstraint r constraint env = over (envConstraints.amHeap) (M.insert r (over _2 (++ [constraint]) (lookupMapConstraints r env))) env
setCustomCount t n = over envCustomCount (M.insert t n)
withHeap f env = let (res, h') = f (env^.envMemory.memHeap) 
  in (res, set (envMemory.memHeap) h' env )  
