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

-- | Function signature: argument types, return type
data FSig = FSig [Id] [Type] Type
	deriving Show

-- | Typechecking context: 
--	global variable-type binding, 
--	local variable-type binding, 
--	constant-type binding, 
--	function-signature binding,
--	type constructor arity,
--	type synonym to value binding,
--	free type variables
data Context = Context (M.Map Id Type) (M.Map Id Type) (M.Map Id Type) (M.Map Id FSig) (M.Map Id Int) (M.Map Id ([Id], Type)) [Id]
	deriving Show

-- | Global variable-type binding of a context
globals (Context g _ _ _ _ _ _) = g

-- | Local variable-type binding of a context
locals (Context _ l _ _ _ _ _) = l

-- | Constant-type binding of a context
constants (Context _ _ c _ _ _ _) = c

-- | Function-signature binding of a context
functions (Context _ _ _ f _ _ _) = f

-- | Type constructor arity
typeConstructors (Context _ _ _ _ tc _ _) = tc

-- | Type synonym to value binding
typeSynonyms (Context _ _ _ _ _ ts _) = ts

-- | Free type variables of a context
freeTypeVars (Context _ _ _ _ _ _ fv) = fv

-- | Empty context
emptyContext = Context M.empty M.empty M.empty M.empty M.empty M.empty []

-- | Change variable-type binding of a context to v
setGlobals (Context _ l c f tc ts fv) g = Context g l c f tc ts fv

-- | Change variable-type binding of a context to v
setLocals (Context g _ c f tc ts fv) l = Context g l c f tc ts fv

-- | Change constant-type binding of a context to c
setConstants (Context g l _ f tc ts fv) c = Context g l c f tc ts fv

-- | Change constant-type binding of a context to c
setFunctions (Context g l c _ tc ts fv) f = Context g l c f tc ts fv

-- | Change free type variables of a context to fv
setTypeConstructors (Context g l c f _ ts fv) tc = Context g l c f tc ts fv

-- | Change free type variables of a context to fv
setTypeSynonyms (Context g l c f tc _ fv) ts = Context g l c f tc ts fv

-- | Change free type variables of a context to fv
setFV (Context g l c f tc ts _) fv = Context g l c f tc ts fv

-- | Binding for global variables and constants
globConst c = M.union (globals c) (constants c)

-- | Binding for all variables and constants (local variables are chosen when conincide with global names)
varConst c = M.union (locals c) (globConst c)

-- | Names of type constructors and synonyms
typeNames c = M.keys (typeConstructors c) ++ M.keys (typeSynonyms c)

-- | insertIdType get set c i t : insert pair i-t into the (get c) binding of the context c, using setter set
insertIdType :: (Context -> M.Map Id Type) -> (Context -> M.Map Id Type -> Context) -> Context -> Id -> Type -> Context
insertIdType get set c i t = c `set` (M.insert i t (get c))

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

-- | checkType c t : check that t is a correct type in context c (all type names exist and have correct number of arguments)
checkType :: Context -> Type -> Checked Type
checkType c (MapType fv domains range) = do { domains' <- mapM (checkType c') domains;
		range' <- checkType c' range;
		return (MapType fv domains range)}
	where c' = c `setFV` (freeTypeVars c ++ fv)
checkType c (Instance name args)
	| name `elem` freeTypeVars c && null args = return (Instance name args)
	| M.member name (typeConstructors c) = if n == length args 
		then do { args' <- mapM (checkType c) args;
			return (Instance name args')}
		else throwError ("Wrong number of arguments " ++ show (length args) ++ " given to the type constructor " ++ name ++ " (expected " ++ show n ++ ")")
	| M.member name (typeSynonyms c) = if length formals == length args
		then do { args' <- mapM (checkType c) args;
			return (Instance name args')}
		else throwError ("Wrong number of arguments " ++ show (length args) ++ " given to the type synonym " ++ name ++ " (expected " ++ show (length formals) ++ ")")
	| otherwise = throwError ("Not in scope: type constructor or synonym " ++ name)
		where 
			n = (M.!) (typeConstructors c) name
			formals = fst ((M.!) (typeSynonyms c) name)
checkType _ t = return t

-- | resolve c t : type t with all type synonyms resolved according to binding in c			
resolve :: Context -> Type -> Type
resolve c (MapType fv domains range) = MapType fv (map (resolve c') domains) (resolve c' range)
	where c' = c `setFV` (freeTypeVars c ++ fv)
resolve c (Instance name args) 
	| name `elem` freeTypeVars c = (Instance name args)
	| otherwise = case M.lookup name (typeSynonyms c) of
		Nothing -> Instance name (map (resolve c) args)
		Just (formals, t) -> resolve c (substitution (M.fromList (zip formals args)) t) -- ToDo: check must be done before that synonym declarations are not cyclic
resolve _ t = t 	
	
{- Expressions -}

{- requires all types in the context are valid and type synonyms are resolved -}
checkExpression :: Context -> Expression -> Checked Type
checkExpression c e = case e of
	TT -> return BoolType
	FF -> return BoolType
	Numeral n -> return IntType
	Var id -> case M.lookup id (varConst c) of
		Nothing -> throwError ("Not in scope: variable or constant " ++ id)
		Just t -> return t
	Application id args -> checkApplication c id args
	MapSelection m args -> checkMapSelection c m args
	MapUpdate m args val -> checkMapUpdate c m args val
	Old e1 -> checkExpression c e1 -- ToDo: only allowed in postconditions and implementation
	UnaryExpression op e1 -> checkUnaryExpression c op e1
	BinaryExpression op e1 e2 -> checkBinaryExpression c op e1 e2
	Quantified qop fv vars e -> checkQuantified c qop fv vars e

checkApplication :: Context -> Id -> [Expression] -> Checked Type
checkApplication c id args = case M.lookup id (functions c) of
	Nothing -> throwError ("Not in scope: function " ++ id)
	Just (FSig fv argTypes retType) -> do {
		actualTypes <- mapM (checkExpression c) args;
		case unifier fv argTypes actualTypes of
			Nothing -> throwError ("Could not match formal argument types " ++ separated ", " (map pretty argTypes) ++
				" against actual argument types " ++ separated ", " (map pretty actualTypes) ++
				" in the call to " ++ id)
			Just u -> return (substitution u retType)
		}
		
checkMapSelection :: Context -> Expression -> [Expression] -> Checked Type
checkMapSelection c m args = do {
	mType <- checkExpression c m;
	case mType of
		MapType fv domainTypes rangeType -> do {
			actualTypes <- mapM (checkExpression c) args;
			case unifier fv domainTypes actualTypes of
				Nothing -> throwError ("Could not match map domain types " ++ separated ", " (map pretty domainTypes) ++
					" against map selection types " ++ separated ", " (map pretty actualTypes) ++
					" for the map " ++ pretty m)
				Just u -> return (substitution u rangeType)
			}
		t -> throwError ("Map selection applied to a non-map " ++ pretty m ++ " of type " ++ pretty t)
	}
	
checkMapUpdate :: Context -> Expression -> [Expression] -> Expression -> Checked Type
checkMapUpdate c m args val = do { 
	t <- checkMapSelection c m args;
	actualT <- checkExpression c val;
	if t == actualT 
		then checkExpression c m 
		else throwError ("Update value type " ++ pretty actualT ++ " different from map range type " ++ pretty t)
	}
	
	
checkUnaryExpression :: Context -> UnOp -> Expression -> Checked Type
checkUnaryExpression c op e
	| op == Neg = matchType IntType IntType
	| op == Not = matchType BoolType BoolType
	where 
		matchType t ret = do { t' <- checkExpression c e;
			if t' == t then return ret else throwError (errorMsg t' op)
			}
		errorMsg t op = "Invalid argument type " ++ pretty t ++ " to unary operator" ++ pretty op
	
checkBinaryExpression :: Context -> BinOp -> Expression -> Expression -> Checked Type
checkBinaryExpression c op e1 e2
	| elem op [Plus, Minus, Times, Div, Mod] = matchTypes (\t1 t2 -> t1 == IntType && t2 == IntType) IntType
	| elem op [And, Or, Implies, Equiv] = matchTypes (\t1 t2 -> t1 == BoolType && t2 == BoolType) BoolType
	| elem op [Ls, Leq, Gt, Geq] = matchTypes (\t1 t2 -> t1 == IntType && t2 == IntType) BoolType
	| elem op [Eq, Neq] = matchTypes (\t1 t2 -> isJust (unifier (freeTypeVars c) [t1] [t2])) BoolType
	| op == Lc = matchTypes (==) BoolType
	where 
		matchTypes pred ret = do { t1 <- checkExpression c e1;
			t2 <- checkExpression c e2;
			if pred t1 t2 then return ret else throwError (errorMsg t1 t2 op)
			}	
		errorMsg t1 t2 op = "Invalid argument types " ++ pretty t1 ++ " and " ++ pretty t2 ++ " to binary operator" ++ pretty op
		
checkQuantified :: Context -> QOp -> [Id] -> [IdType] -> Expression -> Checked Type
checkQuantified c _ fv vars e = if not (null duplicateFV) 
	then throwError ("Multiple declarations of type variable(s) " ++ separated ", " duplicateFV)
	else do {
		scoped <- foldM (checkIdType locals (insertIdType locals setLocals)) (c `setFV` (freeTypeVars c ++ fv)) vars;
		if not (null missingFV) 
		then throwError ("Type variable(s) must occur in the bound variables of the quantification: " ++ separated ", " missingFV) 
		else do {
			t <- checkExpression scoped e;
			case t of
				BoolType -> return BoolType;
				_ -> throwError ("Quantified expression type " ++ pretty t ++ " different from bool")
		}
	}
	where
		duplicateFV = intersect fv (freeTypeVars c)
		missingFV = filter (not . freeInVars) fv
		freeInVars v = any (isFree v) (map snd vars)
		
{- Statements -}

{- Declarations -}

checkProgram :: Program -> Checked Context
checkProgram p = foldM checkDecl emptyContext p

checkDecl :: Context -> Decl -> Checked Context
checkDecl c d = case d of
	TypeDecl finite name args value -> checkTypeDecl c finite name args value
	VarDecl vars -> foldM (checkIdType varConst (insertIdType globals setGlobals)) c (map noWhere vars)
	ConstantDecl _ ids t _ _ -> foldM (checkIdType varConst (insertIdType constants setConstants)) c (zip ids (repeat t))
	FunctionDecl name fv args ret body -> checkFunctionDecl c name fv args ret body
	otherwise -> return c	
	
checkTypeDecl :: Context -> Bool -> Id -> [Id] -> (Maybe Type) -> Checked Context 
checkTypeDecl c _ name formals value
	| name `elem` (typeNames c) = throwError ("Multiple declarations of type constructor or synonym " ++ name) 
	| not (null reservedFormals) = throwError ("Names already reserved for type constructors or synonyms: " ++ separated ", " reservedFormals)
	| otherwise = case value of
		Nothing -> return (c `setTypeConstructors` (M.insert name (length formals) (typeConstructors c)))
		Just t -> do { t' <- checkType (c `setFV` formals) t;
			return (c `setTypeSynonyms` (M.insert name (formals, t') (typeSynonyms c))) }
		where reservedFormals = intersect (typeNames c) formals			
	
checkFunctionDecl :: Context -> Id -> [Id] -> [FArg] -> FArg -> (Maybe Expression) -> Checked Context
checkFunctionDecl c name fv args ret body = 
	do { 
		mapM (checkType c) (map snd [fArg | fArg <- ret : args , isNothing (fst fArg)]); -- ToDo: types are checked in wrong order (first all without ids)
		scoped <- foldM (checkIdType locals (insertIdType locals setLocals)) (c `setFV` fv) (concat (map fArgToList (args ++ [ret])));
		if not (null missingFV) then throwError ("Type variable(s) must occur in function arguments: " ++ separated ", " missingFV) else
			case body of
				Nothing -> return (update c)
				Just e -> do { 
					t <- checkExpression (scoped `setGlobals` M.empty `setLocals` (removeRet (locals scoped))) e; 
					if t == snd ret 
						then return (update c) 
						else throwError ("Function body type " ++ pretty t ++ " different from return type " ++ pretty (snd ret))
					}
		}
	where 
		fArgToList (name, t) = case name of
			Just id -> [(id, t)]
			Nothing -> []
		removeRet = M.delete (fromMaybe "" (fst ret))
		missingFV = filter (not . freeInArgs) fv
		freeInArgs v = any (isFree v) (map snd args)
		update c = c `setFunctions` (M.insert name (FSig fv (map snd args) (snd ret)) (functions c))

-- ToDo: check that type constructors are valid and resolve type synonyms, check that type variables are fresh
checkIdType :: (Context -> M.Map Id Type) -> (Context -> Id -> Type -> Context) -> Context -> IdType -> Checked Context
checkIdType get set c (i, t) 	
	| M.member i (get c) = throwError ("Multiple declarations of variable or constant " ++ i)
	| otherwise = do { t' <- checkType c t;
		return (set c i (resolve c t)) }
	