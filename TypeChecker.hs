{- Type checker for Boogie 2 -}
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

-- | Function signature: type variables, argument types, return type
data FSig = FSig [Id] [Type] Type
  deriving Show
  
-- | Procedure signature: type variables, argument types, return types
data PSig = PSig [Id] [Type] [Type]
  deriving Show

-- | Typechecking context: 
data Context = Context
  {
    ctxTypeConstructors :: M.Map Id Int,      --  type constructor arity,
    ctxTypeSynonyms :: M.Map Id ([Id], Type), --  type synonym to value binding,
    ctxGlobals :: M.Map Id Type,              --  global variable-type binding, 
    ctxConstants :: M.Map Id Type,            --  constant-type binding, 
    ctxFunctions :: M.Map Id FSig,            --  function-signature binding,
    ctxProcedures :: M.Map Id PSig,           --  procedure-signature binding,
    ctxTypeVars :: [Id],                      --  free type variables,
    ctxIns :: M.Map Id Type,                  --  input parameter-type binding,
    ctxLocals :: M.Map Id Type                --  local variable-type binding 
  } deriving Show

emptyContext = Context M.empty M.empty M.empty M.empty M.empty M.empty [] M.empty M.empty

setGlobals ctx g    = ctx { ctxGlobals = g }
setIns ctx i        = ctx { ctxIns = i }
setLocals ctx l     = ctx { ctxLocals = l }
setConstants ctx c  = ctx { ctxConstants = c }

-- | Type constructors and synonyms
typeNames c = M.keys (ctxTypeConstructors c) ++ M.keys (ctxTypeSynonyms c)
-- | Global variables and constants
globalScope c = M.union (ctxGlobals c) (ctxConstants c)
-- | Input parameters and local variables
localScope c = M.union (ctxIns c) (ctxLocals c)
-- | Global and local variables
mutableVars c = M.union (ctxGlobals c) (ctxLocals c)
-- | All variables and constants (local-scope preferred)
allVars c = M.union (localScope c) (globalScope c)

-- | Names of functions and procedures
funProcNames c = M.keys (ctxFunctions c) ++ M.keys (ctxProcedures c)

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

-- | Check that a type variable is fresh and add it to context  
checkTypeVar :: Context -> Id -> Checked Context
checkTypeVar c v
  | v `elem` typeNames c = throwError (v ++ " already used as a type constructor or synonym")
  | v `elem` ctxTypeVars c = throwError ("Multiple decalartions of type variable " ++ v)
  | otherwise = return c { ctxTypeVars = v : ctxTypeVars c }

-- | checkType c t : check that t is a correct type in context c (i.e. that all type names exist and have correct number of arguments)
checkType :: Context -> Type -> Checked ()
checkType c (MapType fv domains range) = do
  c' <- foldM checkTypeVar c fv
  mapM (checkType c') domains
  checkType c' range
checkType c (Instance name args)
  | name `elem` ctxTypeVars c && null args = return ()
  | M.member name (ctxTypeConstructors c) = if n == length args 
    then mapM_ (checkType c) args
    else throwError ("Wrong number of arguments " ++ show (length args) ++ " given to the type constructor " ++ name ++ " (expected " ++ show n ++ ")")
  | M.member name (ctxTypeSynonyms c) = if length formals == length args
    then mapM_ (checkType c) args
    else throwError ("Wrong number of arguments " ++ show (length args) ++ " given to the type synonym " ++ name ++ " (expected " ++ show (length formals) ++ ")")
  | otherwise = throwError ("Not in scope: type constructor or synonym " ++ name)
    where 
      n = (M.!) (ctxTypeConstructors c) name
      formals = fst ((M.!) (ctxTypeSynonyms c) name)
checkType _ t = return ()

-- | resolve c t : type t with all type synonyms resolved according to binding in c      
resolve :: Context -> Type -> Type
resolve c (MapType fv domains range) = MapType fv (map (resolve c') domains) (resolve c' range)
  where c' = c { ctxTypeVars = ctxTypeVars c ++ fv }
resolve c (Instance name args) 
  | name `elem` ctxTypeVars c = Instance name args
  | otherwise = case M.lookup name (ctxTypeSynonyms c) of
    Nothing -> Instance name (map (resolve c) args)
    Just (formals, t) -> resolve c (substitution (M.fromList (zip formals args)) t)
resolve _ t = t   
  
{- Expressions -}

-- | requires all types in the context be valid and type synonyms be resolved
checkExpression :: Context -> Expression -> Checked Type
checkExpression c e = case e of
  TT -> return BoolType
  FF -> return BoolType
  Numeral n -> return IntType
  Var id -> case M.lookup id (allVars c) of
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
checkApplication c id args = case M.lookup id (ctxFunctions c) of
  Nothing -> throwError ("Not in scope: function " ++ id)
  Just (FSig fv argTypes retType) -> do
    actualTypes <- mapM (checkExpression c) args
    case unifier fv argTypes actualTypes of
      Nothing -> throwError ("Could not match formal argument types " ++ separated ", " (map pretty argTypes) ++
        " against actual argument types " ++ separated ", " (map pretty actualTypes) ++
        " in the call to " ++ id)
      Just u -> return (substitution u retType)
    
checkMapSelection :: Context -> Expression -> [Expression] -> Checked Type
checkMapSelection c m args = do
  mType <- checkExpression c m
  case mType of
    MapType fv domainTypes rangeType -> do
      actualTypes <- mapM (checkExpression c) args
      case unifier fv domainTypes actualTypes of
        Nothing -> throwError ("Could not match map domain types " ++ separated ", " (map pretty domainTypes) ++
          " against map selection types " ++ separated ", " (map pretty actualTypes) ++
          " for the map " ++ pretty m)
        Just u -> return (substitution u rangeType)
    t -> throwError ("Map selection applied to a non-map " ++ pretty m ++ " of type " ++ pretty t)
  
checkMapUpdate :: Context -> Expression -> [Expression] -> Expression -> Checked Type
checkMapUpdate c m args val = do 
  t <- checkMapSelection c m args
  actualT <- checkExpression c val
  if t == actualT 
    then checkExpression c m 
    else throwError ("Update value type " ++ pretty actualT ++ " different from map range type " ++ pretty t)
    
checkUnaryExpression :: Context -> UnOp -> Expression -> Checked Type
checkUnaryExpression c op e
  | op == Neg = matchType IntType IntType
  | op == Not = matchType BoolType BoolType
  where 
    matchType t ret = do
      t' <- checkExpression c e
      if t' == t then return ret else throwError (errorMsg t' op)
    errorMsg t op = "Invalid argument type " ++ pretty t ++ " to unary operator" ++ pretty op
  
checkBinaryExpression :: Context -> BinOp -> Expression -> Expression -> Checked Type
checkBinaryExpression c op e1 e2
  | elem op [Plus, Minus, Times, Div, Mod] = matchTypes (\t1 t2 -> t1 == IntType && t2 == IntType) IntType
  | elem op [And, Or, Implies, Equiv] = matchTypes (\t1 t2 -> t1 == BoolType && t2 == BoolType) BoolType
  | elem op [Ls, Leq, Gt, Geq] = matchTypes (\t1 t2 -> t1 == IntType && t2 == IntType) BoolType
  | elem op [Eq, Neq] = matchTypes (\t1 t2 -> isJust (unifier (ctxTypeVars c) [t1] [t2])) BoolType
  | op == Lc = matchTypes (==) BoolType
  where 
    matchTypes pred ret = do
      t1 <- checkExpression c e1
      t2 <- checkExpression c e2
      if pred t1 t2 then return ret else throwError (errorMsg t1 t2 op)
    errorMsg t1 t2 op = "Invalid argument types " ++ pretty t1 ++ " and " ++ pretty t2 ++ " to binary operator" ++ pretty op
    
checkQuantified :: Context -> QOp -> [Id] -> [IdType] -> Expression -> Checked Type
checkQuantified c _ fv vars e = do
  c' <- foldM checkTypeVar c fv
  quantifiedScope <- foldM (checkIdType localScope ctxIns setIns) c' vars
  if not (null missingFV)
    then throwError ("Type variable(s) must occur in the bound variables of the quantification: " ++ separated ", " missingFV) 
    else do
      t <- checkExpression quantifiedScope e
      case t of
        BoolType -> return BoolType
        _ -> throwError ("Quantified expression type " ++ pretty t ++ " different from " ++ pretty BoolType)
  where
    missingFV = filter (not . freeInVars) fv
    freeInVars v = any (isFree v) (map snd vars)
    
{- Statements -}

checkStatement :: Context -> Statement -> Checked ()
checkStatement c (Assert e) = compareType c "assertion" BoolType e
checkStatement c (Assume e) = compareType c "assumption" BoolType e
checkStatement c (Havoc vars) = checkHavoc c vars
checkStatement c (Assign lhss rhss) = checkAssign c lhss rhss
checkStatement c (Call lhss name args) = checkCall c lhss name args
checkStatement c (CallForall name args) = checkCallForall c name args
checkStatement c (If cond thenBlock elseBlock) = checkIf c cond thenBlock elseBlock
checkStatement c (While cond invs b) = checkWhile c cond invs b
checkStatement _ _ = return ()

checkHavoc :: Context -> [Id] -> Checked ()
checkHavoc c vars = if not (null immutableLhss)
  then throwError ("Havoc of immutable variable(s): " ++ separated ", " immutableLhss)
  else return ()
  where immutableLhss = vars \\ M.keys (mutableVars c)
  
checkAssign :: Context -> [(Id , [[Expression]])] -> [Expression] -> Checked ()
checkAssign c lhss rhss = do
  checkLefts c (map fst lhss) (length rhss)
  rTypes <- mapM (checkExpression c) rhss
  zipWithM_ (compareType c "assignment left-hand side") rTypes (map selectExpr lhss) 
  where
    selectExpr (id, selects) = foldl MapSelection (Var id) selects
        
checkCall :: Context -> [Id] -> Id -> [Expression] -> Checked ()
checkCall c lhss name args = case M.lookup name (ctxProcedures c) of
  Nothing -> throwError ("Not in scope: procedure " ++ name)
  Just (PSig fv argTypes retTypes) -> do
    actualArgTypes <- mapM (checkExpression c) args
    case unifier fv argTypes actualArgTypes of
      Nothing -> throwError ("Could not match formal argument types " ++ separated ", " (map pretty argTypes) ++
        " against actual argument types " ++ separated ", " (map pretty actualArgTypes) ++
        " in the call to " ++ name)
      Just u -> do
        checkLefts c lhss (length retTypes)
        zipWithM_ (compareType c "call left-hand side") (map (substitution u) retTypes) (map Var lhss)
        
checkCallForall :: Context -> Id -> [WildcardExpression] -> Checked ()
checkCallForall c name args = case M.lookup name (ctxProcedures c) of
  Nothing -> throwError ("Not in scope: procedure " ++ name)
  Just (PSig fv argTypes _) -> do
    actualArgTypes <- mapM (checkExpression c) concreteArgs
    case unifier fv (concrete argTypes) actualArgTypes of
      Nothing -> throwError ("Could not match formal argument types " ++ separated ", " (map pretty (concrete argTypes)) ++
        " against actual argument types " ++ separated ", " (map pretty actualArgTypes) ++
        " in the call to " ++ name)
      Just u -> return ()
  where
    concreteArgs = [e | (Expr e) <- args]
    concrete at = [at !! i | i <- [0..length args - 1], isConcrete (args !! i)]
    isConcrete Wildcard = False
    isConcrete (Expr _) = True
    
checkIf :: Context -> WildcardExpression -> Block -> (Maybe Block) -> Checked ()
checkIf c cond thenBlock elseBlock = do
  case cond of
    Wildcard -> return ()
    Expr e -> compareType c "branching condition" BoolType e
  checkBlock c thenBlock
  case elseBlock of
    Nothing -> return ()
    Just b -> checkBlock c b
    
checkWhile :: Context -> WildcardExpression -> [(Bool, Expression)] -> Block -> Checked ()
checkWhile c cond invs body = do
  case cond of  
    Wildcard -> return ()
    Expr e -> compareType c "loop condition" BoolType e
  mapM_ (compareType c "loop invariant" BoolType) (map snd invs)
  checkBlock c body
    
{- Declarations -}

-- | Check program in five passes
checkProgram :: Program -> Checked Context
checkProgram p = do
  pass1 <- foldM collectTypes emptyContext p                  -- collect type names from type declarations
  mapM_ (checkTypeSynonyms pass1) p                           -- check values of type synonyms
  mapM_ (checkCycles pass1) (M.keys (ctxTypeSynonyms pass1))  -- check that type synonyms do not form a cycle 
  pass4 <- foldM checkSignatures pass1 p                      -- check variable, constant, function and procedure signatures
  mapM_ (checkBodies pass4) p                                 -- check axioms, function and procedure bodies
  return pass4

-- | Collect type names from type declarations
collectTypes :: Context -> Decl -> Checked Context
collectTypes c d = case d of
  TypeDecl finite name formals value -> checkTypeDecl c name formals value
  otherwise -> return c  

-- | Check uniqueness of type constructors and synonyms, and them in the context  
checkTypeDecl :: Context -> Id -> [Id] -> (Maybe Type) -> Checked Context 
checkTypeDecl c name formals value
  | name `elem` (typeNames c) = throwError ("Multiple declarations of type constructor or synonym " ++ name) 
  | otherwise = case value of
    Nothing -> return c { ctxTypeConstructors = M.insert name (length formals) (ctxTypeConstructors c) }
    Just t -> return c { ctxTypeSynonyms = M.insert name (formals, t) (ctxTypeSynonyms c) }

-- | Check that type arguments of type synonyms are fresh and values are valid types
checkTypeSynonyms :: Context -> Decl -> Checked ()
checkTypeSynonyms c d = case d of
  TypeDecl finite name formals (Just t) -> do
    c' <- foldM checkTypeVar c formals 
    checkType c' t
  otherwise -> return ()

-- | Check if type synonym declarations have cyclic dependences; do not modify context  
checkCycles :: Context -> Id -> Checked ()
checkCycles c id = checkCyclesWith c id (value id)
  where
    checkCyclesWith c id t = case t of
      Instance name args -> do
        if M.member name (ctxTypeSynonyms c)
          then if id == name 
            then throwError ("Cycle in the definition of type synonym " ++ id) 
            else checkCyclesWith c id (value name)
          else return ()
        mapM_ (checkCyclesWith c id) args
      MapType _ domains range -> mapM_ (checkCyclesWith c id) (range:domains)
      _ -> return ()
    value name = snd ((M.!) (ctxTypeSynonyms c) name)

-- | Check variable, constant, function and procedures and add them to context
checkSignatures :: Context -> Decl -> Checked Context
checkSignatures c d = case d of
  VarDecl vars -> foldM (checkIdType globalScope ctxGlobals setGlobals) c (map noWhere vars)
  ConstantDecl _ ids t _ _ -> foldM (checkIdType globalScope ctxConstants setConstants) c (zip ids (repeat t))
  FunctionDecl name fv args ret _ -> checkFunctionSignature c name fv args ret
  ProcedureDecl name fv args rets _ _ -> checkProcSignature c name fv args rets
  otherwise -> return c

-- | checkIdType scope get set c idType: check that declaration idType is fresh in scope, and if so add it to (get c) using (set c) 
checkIdType :: (Context -> M.Map Id Type) -> (Context -> M.Map Id Type) -> (Context -> M.Map Id Type -> Context) -> Context -> IdType -> Checked Context
checkIdType scope get set c (i, t)   
  | M.member i (scope c) = throwError ("Multiple declarations of variable or constant " ++ i)
  | otherwise = checkType c t >> return (c `set` M.insert i (resolve c t) (get c))

-- | Check uniqueness of function name, types of formals and add function to context
checkFunctionSignature :: Context -> Id -> [Id] -> [FArg] -> FArg -> Checked Context
checkFunctionSignature c name fv args ret
  | name `elem` funProcNames c = throwError ("Multiple declarations of function or procedure " ++ name)
  | otherwise = do
    c' <- foldM checkTypeVar c fv
    foldM checkFArg c' (args ++ [ret])
    if not (null missingFV) 
      then throwError ("Type variable(s) must occur in function arguments: " ++ separated ", " missingFV)
      else return c { ctxFunctions = M.insert name (FSig fv (map snd args) (snd ret)) (ctxFunctions c) }
    where 
      checkFArg c (Just id, t) = checkIdType ctxIns ctxIns setIns c (id, t)
      checkFArg c (Nothing, t) = checkType c t >> return c
      missingFV = filter (not . freeInArgs) fv
      freeInArgs v = any (isFree v) (map snd args)
      
checkProcSignature :: Context -> Id -> [Id] -> [IdTypeWhere] -> [IdTypeWhere] -> Checked Context
checkProcSignature c name fv args rets
  | name `elem` funProcNames c = throwError ("Multiple declarations of function or procedure " ++ name)
  | otherwise = do
    c' <- foldM checkTypeVar c fv
    foldM checkPArg c' (args ++ rets)
    if not (null missingFV) 
      then throwError ("Type variable(s) must occur in procedure arguments: " ++ separated ", " missingFV)
      else return c { ctxProcedures = M.insert name (PSig fv (map itwType args) (map itwType rets)) (ctxProcedures c) }
    where 
      checkPArg c arg = checkIdType ctxIns ctxIns setIns c (noWhere arg)
      missingFV = filter (not . freeInArgs) fv
      freeInArgs v = any (isFree v) (map itwType args)

-- | Check axioms, function and procedure bodies      
checkBodies :: Context -> Decl -> Checked ()
checkBodies c d = case d of
  VarDecl vars -> mapM_ (checkWhere c) vars
  FunctionDecl name fv args ret (Just body) -> checkFunctionBody c fv args ret body
  AxiomDecl e -> checkAxiom c e
  ProcedureDecl name fv args rets specs mb -> checkProcedureBody c fv args rets mb -- ToDo: check specs
  otherwise -> return ()    
  
-- | Check that "where" part is a valid boolean expression
checkWhere :: Context -> IdTypeWhere -> Checked ()
checkWhere c var = compareType c "where clause" BoolType (itwWhere var)
  
-- | Check that function body is a valid expression of the same type as the function return type
checkFunctionBody :: Context -> [Id] -> [FArg] -> FArg -> Expression -> Checked ()
checkFunctionBody c fv args ret body = do 
  functionScope <- foldM addFArg c { ctxTypeVars = fv } args
  compareType functionScope { ctxGlobals = M.empty } "function body" (snd ret) body
  where 
    addFArg c (Just id, t) = checkIdType ctxIns ctxIns setIns c (id, t)
    addFArg c  _ = return c
    
-- | Check "where" parts of procedure arguments and statements in its body
checkProcedureBody :: Context -> [Id] -> [IdTypeWhere] -> [IdTypeWhere] -> (Maybe Body) -> Checked ()
checkProcedureBody c fv args rets mb = do 
  c' <- foldM (checkIdType localScope ctxIns setIns) c { ctxTypeVars = fv } (map noWhere args)
  procScope <- foldM (checkIdType localScope ctxLocals setLocals) c' (map noWhere rets)
  mapM_ (checkWhere procScope) (args ++ rets)
  case mb of
    Nothing -> return ()
    Just body -> do
      procBodyScope <- foldM (checkIdType localScope ctxLocals setLocals) procScope (map noWhere (fst body))
      checkBlock procBodyScope (snd body)    

-- | Check that axiom is a valid boolean expression    
checkAxiom :: Context -> Expression -> Checked ()
checkAxiom c e = compareType c {ctxGlobals = M.empty } "axiom" BoolType e
    
{- Misc -}

-- | compareType c msg t e: check that e is a valid expression in context c and its type is t
compareType :: Context -> String -> Type -> Expression -> Checked ()
compareType c msg t e = do
  t' <- checkExpression c e
  if t == t' 
    then return ()
    else throwError ("Type of " ++ msg ++ " (" ++ pretty t' ++ ") is different from " ++ pretty t)
    
-- | checkLefts c ids n: check that there are n ids, all ids are unique and denote mutable variables
checkLefts :: Context -> [Id] -> Int -> Checked ()
checkLefts c vars n = if length vars /= n 
  then throwError ("Expected " ++ show n ++ " left-hand sides and got " ++ show (length vars))
  else if vars /= nub vars
    then throwError ("Variable occurs more than once among left-handes of a parallel assignment")
    else if not (null immutableLhss)
      then throwError ("Assignment to immutable variable(s): " ++ separated ", " immutableLhss)
      else return ()
  where 
    immutableLhss = vars \\ M.keys (mutableVars c)

checkBlock :: Context -> Block -> Checked ()    
checkBlock c block = mapM_ (checkStatement c) (map snd block) -- ToDo: keep track of labels    
  