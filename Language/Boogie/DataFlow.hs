-- | Data-flow analysis on Boogie code
module Language.Boogie.DataFlow (liveVariables, liveInputVariables) where

import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Position hiding (gen)
import Language.Boogie.BasicBlocks
import Data.List
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

{- Interface -}

-- | 'liveInputVariables' @sig def@ : 
-- Input parameters (in the order they appear in @sig@) and global names, 
-- whose initial value might be read by the procedure implementation @def@
liveInputVariables :: PSig -> PDef -> ([Id], [Id])
liveInputVariables sig def = let
  body = pdefBody def
  liveVars = liveVariables (attachContractChecks sig def)
  liveLocals = filter (`elem` liveVars) (map itwId (fst body))
  liveIns = filter (`elem` liveVars) (pdefIns def)
  liveOuts = filter (`elem` liveVars) (pdefOuts def)
  liveGlobals = liveVars \\ (liveLocals ++ liveIns ++ liveOuts)
  in (liveIns, liveGlobals)
  
-- | Identifiers whose initial value might be read in body
liveVariables :: Map Id [Statement] -> [Id]
liveVariables body = let
    empty = M.map (const S.empty) body
    insertExitBlock i = M.insert i (transition (body ! i) S.empty)
    entry0 = S.foldr insertExitBlock empty (exitBlocks body)
    changed0 = M.keysSet body <-> exitBlocks body
    oldVariables = S.unions (map (\block -> S.unions (map genOld block)) (M.elems body))
  in S.toList (oldVariables `S.union` (analyse body entry0 empty changed0 ! startLabel))

{- Implementation -}

-- | Analyse live variable in body, 
-- starting from live variables at the entry to each block entry,
-- live variables at the exit of each block exit,
-- and the set of blocks whose exit set might have changed changed.
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
-- if the final live variables are exit
transition :: [Statement] -> Set Id -> Set Id
transition sts exit = foldr transition1 exit sts
  where
    transition1 st exit = exit <-> kill st <+> gen st

-- | Variables that are not live anymore as a result of st    
kill :: Statement -> Set Id
kill st = case node st of
  Havoc ids     -> S.fromList ids
  Assign lhss _ -> S.fromList (map fst lhss)
  Call lhss _ _ -> S.fromList lhss
  otherwise -> S.empty

-- | Variables that become live as a result of st
gen :: Statement -> Set Id
gen st = genTwoState fst st

-- | Variables whose pre-state is mentioned in st
genOld :: Statement -> Set Id
genOld st = genTwoState snd st
  
-- | Variables mentioned in st in either current state or old state
genTwoState :: (([Id], [Id]) -> [Id]) -> Statement -> Set Id
genTwoState select st = case node st of
  Predicate (SpecClause _ _ e) -> (S.fromList . select . freeVarsTwoState) e
  Assign lhss rhss -> let 
    allSubscipts = concat $ concatMap snd lhss
    subsciptedLhss = [fst lhs | lhs <- lhss, not (null (snd lhs))] -- Left-hand sides with a subscript are also read (consider desugaring)
    in S.unions (map (S.fromList . select . freeVarsTwoState) (rhss ++ allSubscipts)) <+> S.fromList subsciptedLhss
  Call _ _ args -> S.unions (map (S.fromList . select . freeVarsTwoState) args)
  CallForall _ args -> S.unions (map (S.fromList . select . freeVarsTwoState') args)
  otherwise -> S.empty
  where 
    freeVarsTwoState' Wildcard = ([], [])
    freeVarsTwoState' (Expr e) = freeVarsTwoState e
    
-- | Blocks in body that end with a return statement
exitBlocks :: Map Id [Statement] -> Set Id
exitBlocks body = M.keysSet $ M.filter isExit body
  where
    isExit block = case node (last block) of
      Return -> True
      _ -> False
      
-- | Blocks in body that have an outgoing edge to label
predecessors :: Map Id [Statement] -> Id -> Set Id
predecessors body label = M.keysSet $ M.filter (goesTo label) body
  where
    goesTo label block = case node (last block) of
      Goto lbs -> label `elem` lbs
      _ -> False
      
-- | Blocks in body that have an incoming edge from label  
successors :: Map Id [Statement] -> Id -> Set Id
successors body label = case node (last (body ! label)) of
  Goto lbs -> S.fromList lbs
  _ -> S.empty
  
-- | Body of the implementation def of procedure sig with pre- and postcondition checks embedded;
-- (used to extract live variables from contracts)
attachContractChecks :: PSig -> PDef -> Map Id [Statement]
attachContractChecks sig def = let
  preChecks = map (attachPos (pdefPos def) . Predicate . subst sig) (psigRequires sig)
  postChecks = map (attachPos (pdefPos def) . Predicate . subst sig) (psigEnsures sig)
  subst sig (SpecClause t f e) = SpecClause t f (paramSubst sig def e)
  attachPreChecks = M.adjust (preChecks ++) startLabel (snd (pdefBody def))
  attachPostChecks block = let jump = last block
    in case node jump of
      Return -> init block ++ postChecks ++ [jump]
      _ -> block
  in M.map attachPostChecks attachPreChecks  
      
