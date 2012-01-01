module TypeChecker where

import AST
import Tokens
import Data.List
import qualified Data.Map as M
import Control.Monad.Identity
import Control.Monad.Error

-- | Result of type checking: either 'a' or an error with strings message
type Checked a = ErrorT String Identity a

{- Context -}

-- | Typechecking context: variable type binding, type variables
type Context = (M.Map Id Type, [Id])

-- | Variable type binding of context c
variables c = fst c

-- | Type arguments of context c
typeArgs c = snd c

-- | Add a new variable type binding to c
addVariable (vars, tArgs) i t = (M.insert i t vars, tArgs)

{- Types -}

-- | typeInstance bindings t returns type t with all free type variables instantiated according to bindings.
-- | All variables in the domain of bindings are considered free. 
typeInstance :: M.Map Id Type -> Type -> Type
typeInstance _ BoolType = BoolType
typeInstance _ IntType = IntType
typeInstance bindings (Instance id []) = case M.lookup id bindings of
	Just t -> t
	Nothing -> Instance id []
typeInstance bindings (Instance id args) = Instance id (map (typeInstance bindings) args)
typeInstance bindings (MapType args domains range) = MapType args (map (typeInstance removedBound) domains) (typeInstance removedBound range)
	where removedBound = foldr M.delete bindings args

-- | twoContextSame args1 ts1 args2 ts2 returns whether all ts1 are the same types as respective ts2 with free variable sets args1 and args2 respectively;	
-- | namely if they are equal for some permutation of type arguments, instantiated with the same actuals.
twoContextSame :: [Id] -> [Type] -> [Id] -> [Type] -> Bool
twoContextSame args1 ts1 args2 ts2 = length args1 == length args2 && or (map sameWithArgsOrder (permutations args2))
	where 	
		sameWithArgsOrder argsOrder = and (zipWith (==) ts1 (map (replacedArgs argsOrder) ts2))
		replacedArgs argsOrder = typeInstance (M.fromList (zip argsOrder (map idType args1)))

-- | Equality of types
instance Eq Type where
	BoolType == BoolType = True
	IntType == IntType = True
	Instance id1 args1 == Instance id2 args2 = id1 == id2 && and (zipWith (==) args1 args2)
	MapType args1 domains1 range1 == MapType args2 domains2 range2 = twoContextSame args1 (range1 : domains1) args2 (range2 : domains2)
	_ == _ = False

maybeSame :: Context -> Type -> Type -> Bool
maybeSame _ BoolType BoolType = True
maybeSame _ IntType IntType = True
maybeSame c (Instance id1 args1) (Instance id2 args2) = id1 == id2 && and (zipWith (maybeSame c) args1 args2)
maybeSame c (Instance id []) _ | elem id (typeArgs c) = True
maybeSame c _ (Instance id []) | elem id (typeArgs c) = True
-- ToDo: equality of map types? maybeSame for map types? do some standartization of type args names?


{- Expressions -}

{- requires all types in the context are valid and type synonims are resolved -}
checkExpression :: Context -> Expression -> Checked Type
checkExpression c e = case e of
	TT -> return BoolType
	FF -> return BoolType
	Numeral n -> return IntType
	Var id -> case M.lookup id (variables c) of
		Just t -> return t
		Nothing -> throwError ("Undeclared indentifier " ++ id) -- ToDo: if inside a function, cannot use global vars
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
		errorMsg t op = "Invalid argument type " ++ show t ++ " to unary operator" ++ unOpName op
	
checkBinaryExpression :: Context -> BinOp -> Expression -> Expression -> Checked Type
checkBinaryExpression c op e1 e2
	| elem op [Plus, Minus, Times, Div, Mod] = checkTypes (\t1 t2 -> t1 == IntType && t2 == IntType) IntType
	| elem op [And, Or, Implies, Equiv] = checkTypes (\t1 t2 -> t1 == BoolType && t2 == BoolType) BoolType
	| elem op [Ls, Leq, Gt, Geq] = checkTypes (\t1 t2 -> t1 == IntType && t2 == IntType) BoolType
	| elem op [Eq, Neq] = checkTypes (maybeSame c) BoolType
	| op == Lc = checkTypes (==) BoolType
	where 
		checkTypes pred ret = do { t1 <- checkExpression c e1;
			t2 <- checkExpression c e2;
			if pred t1 t2 then return ret else throwError (errorMsg t1 t2 op)
			}	
		errorMsg t1 t2 op = "Invalid argument types " ++ show t1 ++ " and " ++ show t2 ++ " to binary operator" ++ binOpName op

{- Statements -}

{- Declarations -}

checkProgram :: Program -> Checked Context
checkProgram p = foldM checkDecl (M.empty, []) p

checkDecl :: Context -> Decl -> Checked Context
checkDecl c d = case d of
	VarDecl vars -> foldM checkIdType c (map noWhere vars)
	ConstantDecl _ ids t _ _ -> foldM checkIdType c (zip ids (repeat t))
	FunctionDecl _ tArgs args ret body -> 
		do { scoped <- foldM checkIdType (M.empty, tArgs) (concat (map fArgToList (args ++ [ret])));
		-- ToDo: Check body
		return c }
		where fArgToList (name, t) = case name of
			Just id -> [(id, t)]
			Nothing -> []
	otherwise -> return c

-- ToDo: check that type constructors are valid and resolve type synonims, check that type variables are fresh
checkIdType :: Context -> IdType -> Checked Context
checkIdType c (i, t) 	
	| M.member i (variables c) = throwError ("Multiple declarations of variable or constant " ++ i) 
	| otherwise = return (addVariable c i t)
	