{-# LANGUAGE TemplateHaskell #-}

-- | Generic heap with reference counting.
-- This module provides relatively low-level interface to the heap data structure, while keeping its internal representation hidden and consistent.
module Language.Boogie.Heap (
  Ref,
  refDoc,
  Heap,
  emptyHeap,
  at,
  alloc,
  hasGarbage,
  dealloc,
  update,
  incRefCount,
  decRefCount,
  heapDoc
) where

import Language.Boogie.Pretty
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Lens hiding (Context, at)

-- | Reference (index in the heap)
type Ref = Int

-- | Pretty-printed reference
refDoc :: Ref -> Doc
refDoc r = text "r'" <> int r

-- | Heap
data Heap a = Heap {
    _hValCounts :: Map Ref (a, Int),   -- ^ Mapping of references of values and reference counts
    _hGarbage :: Set Ref,              -- ^ Set of unused references (exactly those references for which snd hValCounts = 0, stored for efficiency)
    _hFree :: Set Ref,                 -- ^ Set of references that have been removed from the heap and are ready to be reused (stored for efficiency)
    _hFresh :: Ref                     -- ^ Smallest reference that has never been used
  } deriving Eq
  
makeLenses ''Heap  

{- Initialization -}

-- | Empty heap
emptyHeap = Heap {
  _hValCounts = M.empty,
  _hGarbage = S.empty,
  _hFree = S.empty,
  _hFresh = 0
}

{- Access -}

-- | 'at' @h r@: value of @r@ in heap @h@
at :: Heap a -> Ref -> a
at h r = case M.lookup r (h^.hValCounts) of
  Nothing -> internalError $ text "Cannot find reference" <+> refDoc r <+> text "in the heap"
  Just (v, c) -> v
  
-- | Does the heap have any garbage?
hasGarbage :: Heap a -> Bool
hasGarbage h = h ^. hGarbage . to S.null . to not

{- Modification -}  
  
-- | 'alloc' @v h@ : choose a free reference in heap @h@ and store value @v@ in there; return the reference and the updated heap
alloc :: a -> Heap a -> (Ref, Heap a)
alloc v h = let (r, h') = getFreshRef h in (r, insert r v h')
  where
    getFreshRef h = if h ^. hFree . to S.null
      then let r = h^.hFresh in (r, h & hFresh .~ r + 1)
      else let (r, f') = S.deleteFindMin (h^.hFree) in (r, h & hFree .~ f')
    insert r v h = h & (over hValCounts (M.insert r (v, 0))) . (over hGarbage (S.insert r))

-- | Collect some garbage reference in the heap and return that reference and the new heap;
-- the heap must have garbage
dealloc :: Heap a -> (Ref, Heap a)
dealloc h = let (r, g') = S.deleteFindMin (h^.hGarbage) in (r, 
  h & (over hValCounts (M.delete r)) .
      (hGarbage .~ g') .
      (over hFree (S.insert r)) 
  )
    
-- | 'update' @r v h@ : set the value at reference @r@ to @v@ in @h@;
-- @r@ must be present in @h@
update :: Ref -> a -> Heap a -> Heap a
update r v = over hValCounts (M.adjust (over _1 (const v)) r)

-- | 'incRefCount' @r h@ : increase reference count of @r@ in @h@;
-- @r@ must be present in @h@
incRefCount :: Ref -> Heap a -> Heap a
incRefCount r h = let (v, c) = (h^.hValCounts) ! r
  in h & (over hValCounts (M.insert r (v, c + 1))) .
         (over hGarbage (if c == 0 then S.delete r else id)
     )

-- | 'decRefCount' @r h@ : decrease reference count of @r@ in @h@;
-- @r@ must be present in @h@          
decRefCount :: Ref -> Heap a -> Heap a
decRefCount r h = let (v, c) = (h^.hValCounts) ! r
  in h & (over hValCounts (M.insert r (v, c - 1))) .
         (over hGarbage (if c == 1 then S.insert r else id))
          
{- Ouput -}          

-- | Pretty-printed heap
heapDoc :: Pretty a => Heap a -> Doc
heapDoc h = (vsep $ map entryDoc (M.toList (h^.hValCounts)))
  -- $+$ text "Garbage" <+> braces (commaSep (map refDoc (S.toList (h^.hGarbage))))
  -- $+$ text "Free" <+> braces (commaSep (map refDoc (S.toList (h^.hFree))))
  where entryDoc (ref, (val, count)) = refDoc ref <> braces (int count) <+> text "->" <+> pretty val
  
instance Pretty a => Pretty (Heap a) where
  pretty h = heapDoc h
  