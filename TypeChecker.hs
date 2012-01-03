module TypeChecker where

import AST
import Tokens
import Printer
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Control.Monad.Identity
import Control.Monad.Error
import Control.Applicative

-- | Result of type checking: either 'a' or an error with strings message
type Checked a = ErrorT String Identity a

{- Context -}

-- | Typechecking context: variable-type binding, constant-type binding, free type variables
type Context = (M.Map Id Type, M.Map Id Type, [Id])

-- | Variable-type binding of a context
variables (v, c, fv) = v

-- | Variable-type binding of a context
constants (v, c, fv) = c

-- | Free type variables of a context
freeTypeVars (v, c, fv) = fv

-- | Empty context
emptyContext = (M.empty, M.empty, [])

-- | Change variable-type binding of a context to v
setVariables (_, c, fv) v = (v, c, fv)

-- | Change constant-type binding of a context to c
setConstants (v, _, fv) c = (v, c, fv)

-- | Change free type variables of a context to fv
setFV (v, c, _) fv = (v, c, fv)

-- | deleteAll keys m : map m with keys removed from its domain
deleteAll :: Ord k => [k] -> M.Map k a -> M.Map k a
deleteAll keys m = foldr M.delete m keys

{- Types -}

-- | substitution binding t : type t with all free type variables instantiated according to binding.
-- All variables in the domain of bindings are considered free if not explicitly bound. 
substitution :: M.Map Id Type -> Type -> Type
substitution _ BoolType = BoolType
substitution _ IntType = IntType
substitution binding (Instance id []) = case M.lookup id binding of
	Just t -> t
	Nothing -> Instance id []
substitution binding (Instance id args) = Instance id (map (substitution binding) args)
substitution binding (MapType bv domains range) = MapType bv (map (substitution removeBound) domains) (substitution removeBound range)
	where removeBound = deleteAll bv binding
	
-- | isFree x t : does x occur as a free type variable in t?
-- x must not be a name of a type constructor.	
isFree :: Id -> Type -> Bool
isFree x (Instance y []) = x == y
isFree x (Instance y args) = any (isFree x) args
isFree x (MapType bv domains range) = x `notElem` bv && any (isFree x) (range:domains)
isFree x _ = False
	
-- | unifier fv xs ys : most general unifier of xs and ys with free variables fv 	
unifier :: [Id] -> [Type] -> [Type] -> Maybe (M.Map Id Type)
unifier _ [] [] = Just M.empty
unifier fv (IntType:xs) (IntType:ys) = unifier fv xs ys
unifier fv (BoolType:xs) (BoolType:ys) = unifier fv xs ys
unifier fv ((Instance id1 args1):xs) ((Instance id2 args2):ys) | id1 == id2 = unifier fv (args1 ++ xs) (args2 ++ ys)
unifier fv ((Instance id []):xs) (y:ys) | id `elem` fv = 
	if isFree id y then Nothing 
	else M.insert id y <$> unifier fv (update xs) (update ys)
		where update = map (substitution (M.singleton id y))
unifier fv (x:xs) ((Instance id []):ys) | id `elem` fv = 
	if isFree id x then Nothing 
	else M.insert id x <$> unifier fv (update xs) (update ys)
		where update = map (substitution (M.singleton id x))
unifier fv ((MapType bv1 domains1 range1):xs) ((MapType bv2 domains2 range2):ys) =
	if length bv1 /= length bv2 || length domains1 /= length domains2 then Nothing
	else case innerUnifier of 
		Nothing -> Nothing
		Just u -> if all isBV (M.elems (bound u)) && not (any hasBV (M.elems (free u)))
			then M.union (free u) <$> unifier fv (update u xs) (update u ys) 
			else Nothing
		where
			-- unifier for the components of map types m1 and m2, where bound variables of m1 are considered free, and those of m2 are considered constants and given fresh names 
			innerUnifier = unifier (fv ++ bv1) (range1:domains1) (map replacedBV (range2:domains2))
			-- substitution of bound variables of m2 with fresh names
			replacedBV = substitution (M.fromList (zip bv2 (map idType freshBVNames)))
			-- fresh names for bound variables of m2: with non-identifier chanarcter prepended 
			freshBVNames = map (nonIdChar:) bv2
			-- does a type correspond to one of the fresh bound variables of m2?
			isBV (Instance id []) = id `elem` freshBVNames
			isBV _ = False
			-- does type t contain any fresh bound variables of m2?
			hasBV t = any (flip isFree t) freshBVNames
			-- binding restricted to free variables
			free = deleteAll bv1
			-- binding restricted to bound variables
			bound = deleteAll (fv \\ bv1)
			-- type list updated with all free variables updated according to binding u
			update u = map (substitution (free u))
unifier _ _ _ = Nothing

-- | Equality of types
instance Eq Type where
	t1 == t2 = isJust (unifier [] [t1] [t2])
	
{- Expressions -}

{- requires all types in the context are valid and type synonims are resolved -}
checkExpression :: Context -> Expression -> Checked Type
checkExpression c e = case e of
	TT -> return BoolType
	FF -> return BoolType
	Numeral n -> return IntType
	Var id -> case M.lookup id (variables c) of
		Just t -> return t
		Nothing -> throwError ("Undeclared identifier " ++ id)
	Application id args -> throwError ("Todo")
	MapSelection id args -> throwError ("Todo")
	MapUpdate is args val -> throwError ("Todo")
	Old e1 -> checkExpression c e1 -- ToDo: only allowed in postconditions and implementation
	UnaryExpression op e1 -> checkUnaryExpression c op e1
	BinaryExpression op e1 e2 -> checkBinaryExpression c op e1 e2
	otherwise -> throwError ("Type error in expression") 
	
checkUnaryExpression :: Context -> UnOp -> Expression -> Checked Type
checkUnaryExpression c op e
	| op == Neg = checkType IntType IntType
	| op == Not = checkType BoolType BoolType
	where 
		checkType t ret = do { t' <- checkExpression c e;
			if t' == t then return ret else throwError (errorMsg t' op)
			}
		errorMsg t op = "Invalid argument type " ++ pretty t ++ " to unary operator" ++ pretty op
	
checkBinaryExpression :: Context -> BinOp -> Expression -> Expression -> Checked Type
checkBinaryExpression c op e1 e2
	| elem op [Plus, Minus, Times, Div, Mod] = checkTypes (\t1 t2 -> t1 == IntType && t2 == IntType) IntType
	| elem op [And, Or, Implies, Equiv] = checkTypes (\t1 t2 -> t1 == BoolType && t2 == BoolType) BoolType
	| elem op [Ls, Leq, Gt, Geq] = checkTypes (\t1 t2 -> t1 == IntType && t2 == IntType) BoolType
	| elem op [Eq, Neq] = checkTypes (\t1 t2 -> isJust (unifier (freeTypeVars c) [t1] [t2])) BoolType
	| op == Lc = checkTypes (==) BoolType
	where 
		checkTypes pred ret = do { t1 <- checkExpression c e1;
			t2 <- checkExpression c e2;
			if pred t1 t2 then return ret else throwError (errorMsg t1 t2 op)
			}	
		errorMsg t1 t2 op = "Invalid argument types " ++ pretty t1 ++ " and " ++ pretty t2 ++ " to binary operator" ++ pretty op

{- Statements -}

{- Declarations -}

checkProgram :: Program -> Checked Context
checkProgram p = foldM checkDecl emptyContext p

checkDecl :: Context -> Decl -> Checked Context
checkDecl c d = case d of
	VarDecl vars -> foldM checkIdType c (map noWhere vars)
	ConstantDecl _ ids t _ _ -> foldM checkIdType c (zip ids (repeat t))
	FunctionDecl name fv args ret body -> checkFunctionDecl c name fv args ret body
	otherwise -> return c
	
checkFunctionDecl :: Context -> Id -> [Id] -> [FArg] -> FArg -> (Maybe Expression) -> Checked Context
checkFunctionDecl c name fv args ret body = 
	do { 
		scoped <- foldM checkIdType (setFV emptyContext fv) (concat (map fArgToList (args ++ [ret])));
		case body of
			Nothing -> return c -- ToDo: update context
			Just e -> do { 
				t <- checkExpression (c `setFV` fv `setVariables` (removeRet (variables scoped))) e; 
				if t == snd ret 
					then return c 
					else throwError ("Function body type " ++ pretty t ++ " different from return type " ++ pretty (snd ret))
				}
		}
	where 
		fArgToList (name, t) = case name of
			Just id -> [(id, t)]
			Nothing -> []
		removeRet = M.delete (fromMaybe "" (fst ret))

-- ToDo: check that type constructors are valid and resolve type synonims, check that type variables are fresh, add constants to constants
checkIdType :: Context -> IdType -> Checked Context
checkIdType c (i, t) 	
	| M.member i (variables c) = throwError ("Multiple declarations of variable or constant " ++ i) 
	| otherwise = return (setVariables c (M.insert i t (variables c)))
	