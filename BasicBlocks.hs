{- Basic block transformation for imperative Boogie code -}
module BasicBlocks (toBasicBlocks) where

import AST
import Position
import Data.Map (Map, (!))
import qualified Data.Map as M

-- | Transform procedure body into a sequence of basic blocks.
-- | A basic block starts with a label and contains no just, if or while statements,
-- | except for the last statement, which can be a goto or return
toBasicBlocks :: Block -> [BasicBlock]
toBasicBlocks body = let 
  tbs = concatMap (transform M.empty) (map contents body)
  -- By the properties of transform, bs' is a sequence of basic blocks
  tbs' = attach "start" (tbs ++ [([], gen Return)])  
  -- The first statement in tbs' cannot have empty label
  convert bbs ([l], Pos _ Skip) = (l, []) : bbs
  convert bbs ([l], s) = (l, [s]) : bbs
  convert ((l, ss) : bbs) ([], s) = (l, ss ++ [s]) :  bbs  
  in
    -- First flatten control flow with transform, and then convert to basic blocks
    reverse (foldl convert [] tbs')

-- | Attach a label to the first statement (with an empty label) in a non-empty list of labeled statements    
attach :: Id -> [BareLStatement] -> [BareLStatement]
attach l (([], stmts) : lsts) = ([l], stmts) : lsts

-- | LStatement with no label
justStatement s = ([], gen s)

-- | LStatement with no statement
justLabel l = ([l], gen Skip)   

-- | transform m st: transform st into a sequence of basic blocks
-- | m is a map from statement labels to labels of their exit points (used for break)  
transform :: Map Id Id -> BareLStatement -> [BareLStatement]  
transform m (l:lbs, Pos p Skip) =
  (justStatement $ Goto [l]) : attach l (transform m (lbs, Pos p Skip))
transform m (l:lbs, stmt) =
  [justStatement $ Goto [l]] ++
  attach l (transform (M.insert l "done" m) (lbs, stmt)) ++
  [justStatement $ Goto ["done"], justLabel "done"]
transform m ([], Pos p stmt) = case stmt of  
  Goto lbs -> [justStatement $ Goto lbs, justLabel "unreachable"]
  Break (Just l) -> [justStatement $ Goto [m ! l], justLabel "unreachable"]
  Break Nothing -> [justStatement $ Goto [m ! "closest"], justLabel "unreachable"]
  Return -> [justStatement Return, justLabel "unreachable"]
  If cond thenBlock Nothing -> transform m (justStatement $ If cond thenBlock (Just []))
  If Wildcard thenBlock (Just elseBlock) -> 
    [justStatement $ Goto ["l0", "l1"]] ++
    attach "l0" (transBlock m thenBlock ++ [justStatement $ Goto ["done"]]) ++
    attach "l1" (transBlock m elseBlock ++ [justStatement $ Goto ["done"]]) ++
    [justLabel "done"]
  If (Expr e) thenBlock (Just elseBlock) -> 
    [justStatement $ Goto ["l0", "l1"]] ++
    [(["l0"], gen $ Assume e)] ++ transBlock m thenBlock ++ [justStatement $ Goto ["done"]] ++
    [(["l1"], gen $ Assume (gen $ UnaryExpression Not e))] ++ transBlock m elseBlock ++ [justStatement $ Goto ["done"]] ++
    [justLabel "done"]
  While Wildcard _ body ->
    [justStatement $ Goto ["head"]] ++
    [(["head"], gen $ Goto ["body", "done"])] ++ -- ToDo: loop invariants
    attach "body" (transBlock (M.insert "closest" "done" m) body ++ [justStatement $ Goto ["head"]]) ++
    [justLabel "done"]
  While (Expr e) _ body ->
    [justStatement $ Goto ["head"]] ++
    [(["head"], gen $ Goto ["body", "guarded_done"])] ++ -- ToDo: loop invariants
    [(["body"], gen $ Assume e)] ++ transBlock (M.insert "closest" "done" m) body ++ [justStatement $ Goto ["head"]] ++
    [(["guarded_done"], gen $ Assume (gen $ UnaryExpression Not e))] ++ [justStatement $ Goto ["done"]] ++
    [justLabel "done"]    
  s -> [([], gen stmt)]  
  where
    gen = Pos p
    transBlock m b = concatMap (transform m) (map contents b)