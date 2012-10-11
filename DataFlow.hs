module DataFlow (liveVariables, liveInputVariables) where

import AST
import Util
import Position hiding (gen)
import BasicBlocks
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

{- Interface -}

-- | Input parameters and global names, whose initial value might be read by the procedure implementation def
liveInputVariables :: PDef -> ([Id], [Id])
liveInputVariables def = let
  body = pdefBody def
  liveVars = liveVariables (snd body)
  liveLocals = liveVars `intersect` map itwId (fst body)
  liveIns = liveVars `intersect` pdefIns def
  liveOuts = liveVars `intersect` pdefOuts def
  liveGlobals = liveVars \\ (liveLocals ++ liveIns ++ liveOuts)
  in (liveIns, liveGlobals)

-- | Identifiers whose initial value might be read in body
liveVariables :: Map Id [Statement] -> [Id]
liveVariables body = let
    empty = M.map (\_ -> S.empty) body
    insertExitBlock i = M.insert i (transition (body ! i) S.empty)
    entry0 = S.foldr insertExitBlock empty (exitBlocks body)
    changed0 = M.keysSet body <-> exitBlocks body
  in S.toList (analyse body entry0 empty changed0 ! startLabel)

{- Implementation -}

-- | Analyse live variable in body, 
-- | starting from live variables at the entry to each block entry,
-- | live variables at the exit of each block exit,
-- | and the set of blocks whose exit set might have changed changed.
analyse :: Map Id [Statement] -> Map Id (Set Id) -> Map Id (Set Id) -> Set Id -> Map Id (Set Id)
analyse body entry exit changed = if S.null changed
  then entry
  else let 
      (i, changed') = S.deleteFindMax changed
      newExit = setUnions $ S.map (entry !) (successors body i)
      newEntry = transition (body ! i) newExit
      exit' = M.insert i newExit exit
      entry' = M.insert i newEntry entry
      changed'' = if entry ! i == newEntry then changed' else changed' <+> predecessors body i
    in analyse body entry' exit' changed''

(<+>) = (S.union)
(<->) = (S.\\)
-- | Union of a set of sets
setUnions sets = S.foldl S.union S.empty sets

-- | Variables that are live before a sequence of statements sts,
-- | if the final live variables are exit
transition :: [Statement] -> Set Id -> Set Id
transition sts exit = foldr transition1 exit sts
  where
    transition1 st exit = exit <-> kill st <+> gen st

-- | Variables that are not live anymore as a result of st    
kill :: Statement -> Set Id
kill st = case contents st of
  Havoc ids     -> S.fromList ids
  Assign lhss _ -> S.fromList (map fst lhss)
  Call lhss _ _ -> S.fromList lhss
  otherwise -> S.empty

-- | Variables that become live as a result of st  
gen :: Statement -> Set Id
gen st = case contents st of
  Assume _ e -> S.fromList (freeVars e)
  Assert _ e -> S.fromList (freeVars e)
  Assign lhss rhss -> let allIndexes = concat $ concatMap snd lhss in
    S.unions (map (S.fromList . freeVars) rhss) <+> S.unions (map (S.fromList . freeVars) allIndexes)
  Call _ _ args -> S.unions (map (S.fromList . freeVars) args)
  CallForall _ args -> S.unions (map (S.fromList . freeVars') args)
  otherwise -> S.empty
  where 
    freeVars' Wildcard = []
    freeVars' (Expr e) = freeVars e

-- | Blocks in body that end with a return statement
exitBlocks :: Map Id [Statement] -> Set Id
exitBlocks body = M.keysSet $ M.filter isExit body
  where
    isExit block = case contents (last block) of
      Return -> True
      _ -> False
      
-- | Blocks in body that have an outgoing edge to label
predecessors :: Map Id [Statement] -> Id -> Set Id
predecessors body label = M.keysSet $ M.filter (goesTo label) body
  where
    goesTo label block = case contents (last block) of
      Goto lbs -> label `elem` lbs
      _ -> False
      
-- | Blocks in body that have an incoming edge from label  
successors :: Map Id [Statement] -> Id -> Set Id
successors body label = case contents (last (body ! label)) of
  Goto lbs -> S.fromList lbs
  _ -> S.empty
      
