{- Various properties and transformations of Boogie program elements -}
module Util where

import AST
import Position
import Tokens
import Data.Maybe
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Control.Applicative

{- Types -}

-- | Mapping from type variables to types
type TypeBinding = Map Id Type

-- | typeSubst binding t : substitute all free type variables in t according to binding.
-- | All variables in the domain of bindings are considered free if not explicitly bound. 
typeSubst :: TypeBinding -> Type -> Type
typeSubst _ BoolType = BoolType
typeSubst _ IntType = IntType
typeSubst binding (Instance id []) = case M.lookup id binding of
  Just t -> t
  Nothing -> Instance id []
typeSubst binding (Instance id args) = Instance id (map (typeSubst binding) args)
typeSubst binding (MapType bv domains range) = MapType bv (map (typeSubst removeBound) domains) (typeSubst removeBound range)
  where removeBound = deleteAll bv binding
  
-- | isFree x t : does x occur as a free type variable in t?
-- x must not be a name of a type constructor.  
isFree :: Id -> Type -> Bool
isFree x (Instance y []) = x == y
isFree x (Instance y args) = any (isFree x) args
isFree x (MapType bv domains range) = x `notElem` bv && any (isFree x) (range:domains)
isFree x _ = False
  
-- | unifier fv xs ys : most general unifier of xs and ys with free type variables fv   
unifier :: [Id] -> [Type] -> [Type] -> Maybe TypeBinding
unifier _ [] [] = Just M.empty
unifier fv (IntType:xs) (IntType:ys) = unifier fv xs ys
unifier fv (BoolType:xs) (BoolType:ys) = unifier fv xs ys
unifier fv ((Instance id1 args1):xs) ((Instance id2 args2):ys) | id1 == id2 = unifier fv (args1 ++ xs) (args2 ++ ys)
unifier fv ((Instance id []):xs) (y:ys) | id `elem` fv = 
  if isFree id y then Nothing 
  else M.insert id y <$> unifier fv (update xs) (update ys)
    where update = map (typeSubst (M.singleton id y))
unifier fv (x:xs) ((Instance id []):ys) | id `elem` fv = 
  if isFree id x then Nothing 
  else M.insert id x <$> unifier fv (update xs) (update ys)
    where update = map (typeSubst (M.singleton id x))
unifier fv ((MapType bv1 domains1 range1):xs) ((MapType bv2 domains2 range2):ys) =
  case boundUnifier fv bv1 (range1:domains1) bv2 (range2:domains2) of
    Nothing -> Nothing
    Just u -> M.union u <$> (unifier fv (update u xs) (update u ys))
  where
    update u = map (typeSubst u)
unifier _ _ _ = Nothing

-- | boundUnifier fv bv1 xs bv2 ys: most general unifier of xs and ys,
-- | where bv1 are bound type variables in xs and bv2 are bound type variables in ys,
-- | and fv are free type variables of the enclosing context
boundUnifier :: [Id] -> [Id] -> [Type] -> [Id] -> [Type] -> Maybe TypeBinding
boundUnifier fv bv1 xs bv2 ys = if length bv1 /= length bv2 || length xs /= length ys 
  then Nothing
  else case unifier (fv ++ bv1) xs (map replacedBV ys) of
    Nothing -> Nothing
    Just u -> if all isFreshBV (M.elems (bound u)) && not (any hasFreshBV (M.elems (free u)))
      then Just (free u)
      else Nothing
    where
      -- typeSubst of bound variables of m2 with fresh names
      replacedBV = typeSubst (M.fromList (zip bv2 (map idType freshBVNames)))
      -- fresh names for bound variables of m2: with non-identifier chanarcter prepended 
      freshBVNames = map (nonIdChar:) bv2
      -- does a type correspond to one of the fresh bound variables of m2?
      isFreshBV (Instance id []) = id `elem` freshBVNames
      isFreshBV _ = False
      -- does type t contain any fresh bound variables of m2?
      hasFreshBV t = any (flip isFree t) freshBVNames
      -- binding restricted to free variables
      free = deleteAll bv1
      -- binding restricted to bound variables
      bound = deleteAll (fv \\ bv1)
      -- type list updated with all free variables updated according to binding u      

-- | Equality of types
instance Eq Type where
  t1 == t2 = isJust (unifier [] [t1] [t2])

{- Expressions -}

-- | Mapping from variables to expressions
type VarBinding = Map Id BareExpression

-- | exprSubst binding e : substitute all free variables in e according to binding.
-- | All variables in the domain of bindings are considered free if not explicitly bound. 
exprSubst :: VarBinding -> Expression -> Expression
exprSubst binding (Pos pos e) = attachPos pos $ exprSubst' binding e

exprSubst' binding (Var id) = case M.lookup id binding of
  Nothing -> Var id
  Just e -> e
exprSubst' binding (Application id args) = Application id (map (exprSubst binding) args)
exprSubst' binding (MapSelection m args) = MapSelection (exprSubst binding m) (map (exprSubst binding) args)
exprSubst' binding (MapUpdate m args val) = MapUpdate (exprSubst binding m) (map (exprSubst binding) args) (exprSubst binding val)
exprSubst' binding (Old e) = Old (exprSubst binding e)
exprSubst' binding (UnaryExpression op e) = UnaryExpression op (exprSubst binding e)
exprSubst' binding (BinaryExpression op e1 e2) = BinaryExpression op (exprSubst binding e1) (exprSubst binding e2)
exprSubst' binding (Quantified qop tv boundVars e) = Quantified qop tv boundVars (exprSubst binding' e)
  where binding' = deleteAll (map fst boundVars) binding
exprSubst' _ e = e

-- | Binding of parameter names from procedure signature sig to their equivalents from procedure definition def
paramBinding :: PSig -> PDef -> VarBinding
paramBinding sig def = M.fromList $ zip (sigIns ++ sigOuts) (defIns ++ defOuts)
  where
    sigIns = map itwId $ psigArgs sig
    sigOuts = map itwId $ psigRets sig
    defIns = map Var $ pdefIns def
    defOuts = map Var $ pdefOuts def
  
-- | Substitute parameter names from sig in an expression with their equivalents from def  
paramSubst :: PSig -> PDef -> Expression -> Expression  
paramSubst sig def = exprSubst (paramBinding sig def)   

{- Specs -}

-- | Statement that checks specification clause c at runtime
check :: SpecClause -> BareStatement 
check c = if specFree c 
  then Assume (specType c) (specExpr c) 
  else Assert (specType c) (specExpr c)

-- | All precondition clauses in specs  
preconditions :: [Contract] -> [SpecClause]
preconditions specs = catMaybes (map extractPre specs)
  where 
    extractPre (Requires f e) = Just (SpecClause Precondition f e)
    extractPre _ = Nothing

-- | All postcondition clauses in specs    
postconditions :: [Contract] -> [SpecClause]
postconditions specs = catMaybes (map extractPost specs)
  where 
    extractPost (Ensures f e) = Just (SpecClause Postcondition f e)
    extractPost _ = Nothing
   
-- | All modifies clauses in specs   
modifies :: [Contract] -> [Id]
modifies specs = (nub . concat . catMaybes) (map extractMod specs)
  where
    extractMod (Modifies _ ids) = Just ids
    extractMod _ = Nothing 

{- Functions and procedures -}

-- | Function signature
data FSig = FSig {
    fsigName :: Id,         -- Function name
    fsigTypeVars :: [Id],   -- Type variables
    fsigArgTypes :: [Type], -- Argument types
    fsigRetType :: Type     -- Return type
  }
  
-- | Function definition
data FDef = FDef {
    fdefArgs :: [Id],       -- Argument names (in the same order as fsigArgTypes in the corresponding signature)
    fdefBody :: Expression  -- Body 
  }
 
-- | Procedure signature 
data PSig = PSig {
    psigName :: Id,               -- Procedure name
    psigTypeVars :: [Id],         -- Type variables
    psigArgs :: [IdTypeWhere],    -- In-parameters
    psigRets :: [IdTypeWhere],    -- Out-parameters
    psigContracts :: [Contract]   -- Contracts
  }
  
psigArgTypes = (map itwType) . psigArgs
psigRetTypes = (map itwType) . psigRets
psigModifies = modifies . psigContracts
psigRequires = preconditions . psigContracts
psigEnsures = postconditions . psigContracts    
  
-- | Procedure definition;
-- | a single procedure might have multiple definitions (one per body)
data PDef = PDef { 
    pdefIns :: [Id],        -- In-parameter names (in the same order as psigArgsTypes in the corresponding signature)
    pdefOuts :: [Id],       -- Out-parameter names (in the same order as psigRetTypes in the corresponding signature) 
    pdefBody :: BasicBody   -- Body
  }  
  
{- Misc -}

-- | Extracts the element out of a Right and throws an error if its argument is Left 
fromRight :: Either a b -> b
fromRight (Right x) = x

-- | deleteAll keys m : map m with keys removed from its domain
deleteAll :: Ord k => [k] -> Map k a -> Map k a
deleteAll keys m = foldr M.delete m keys    