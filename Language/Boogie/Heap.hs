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

import Data.Word
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Text.PrettyPrint
import Language.Boogie.PrettyPrinter
import Language.Boogie.Util

-- | Reference (index in the heap)
type Ref = Word

-- | Pretty-printed reference
refDoc :: Ref -> Doc
refDoc r = text ("ref_" ++ show r)

-- | Heap
data Heap a = Heap {
  hValCounts :: Map Ref (a, Int),   -- | Mapping of references of values and reference counts
  hGarbage :: Set Ref,              -- | Set of unused references (exactly those references for which snd hValCounts = 0, stored for efficiency)
  hFree :: Set Ref,                 -- | Set of references that have been removed from the heap and are ready to be reused (stored for efficiency)
  hFresh :: Ref                     -- | Smallest reference that has never been used
}

-- | Empty heap
emptyHeap = Heap {
  hValCounts = M.empty,
  hGarbage = S.empty,
  hFree = S.empty,
  hFresh = 0
}

-- | Pretty-printed heap
heapDoc :: Show a => Heap a -> Doc
heapDoc h = (vsep $ map entryDoc (M.toList (hValCounts h))) $+$
  text "Garbage" <+> braces (commaSep (map refDoc (S.toList (hGarbage h)))) $+$
  text "Free" <+> braces (commaSep (map refDoc (S.toList (hFree h))))
  where entryDoc (ref, (val, count)) = refDoc ref <> braces (int count) <+> text "->" <+> text (show val)
  
instance Show a => Show (Heap a) where
  show h = show $ heapDoc h

-- | 'at' @h r@: value of @r@ in heap @h@
at :: Show a => Heap a -> Ref -> a
at h r = case M.lookup r (hValCounts h) of
  Nothing -> internalError . show $ text "Cannot find reference" <+> refDoc r <+> text "in heap" <+> heapDoc h
  Just (v, c) -> v
  
-- | 'alloc' @v h@ : choose a free reference in heap @h@ and store value @v@ in there; return the reference and the updated heap
alloc :: a -> Heap a -> (Ref, Heap a)
alloc v h = let (r, h') = getFreshRef h in (r, insert r v h')
  where
    getFreshRef h = if S.null (hFree h)
      then let r = hFresh h in (r, h { hFresh = r + 1 })
      else let (r, f') = S.deleteFindMin (hFree h) in (r, h { hFree = f' })
    insert r v h = h { hValCounts = M.insert r (v, 0) (hValCounts h), hGarbage = S.insert r (hGarbage h) }

-- | Does the heap have any garbage?
hasGarbage :: Heap a -> Bool
hasGarbage h = (not . S.null . hGarbage) h

-- | Collect some garbage reference in the heap and return the value previously stored at that reference and the new heap;
-- the heap must have garbage
dealloc :: Heap a -> (a, Heap a)
dealloc h = let (r, g') = S.deleteFindMin (hGarbage h) in (fst (hValCounts h ! r), 
  h { 
    hValCounts = M.delete r (hValCounts h),
    hGarbage = g' ,
    hFree = S.insert r (hFree h) 
  })
    
-- | 'update' @r v h@ : set the value at reference @r@ to @v@ in @h@;
-- @r@ must be present in @h@
update :: Ref -> a -> Heap a -> Heap a
update r v h = h { hValCounts = M.adjust (mapFst (const v)) r (hValCounts h) }

-- | 'incRefCount' @r h@ : increase reference count of @r@ in @h@;
-- @r@ must be present in @h@
incRefCount :: Ref -> Heap a -> Heap a
incRefCount r h = let (v, c) = hValCounts h ! r
  in h {  hValCounts  = M.insert r (v, c + 1) (hValCounts h),
          hGarbage    = if c == 0 then S.delete r (hGarbage h) else hGarbage h }

-- | 'decRefCount' @r h@ : decrease reference count of @r@ in @h@;
-- @r@ must be present in @h@          
decRefCount :: Ref -> Heap a -> Heap a
decRefCount r h = let (v, c) = hValCounts h ! r
  in h {  hValCounts  = M.insert r (v, c - 1) (hValCounts h),
          hGarbage    = if c == 1 then S.insert r (hGarbage h) else hGarbage h }
