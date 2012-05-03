{- Type checker for Boogie 2 -}
module TypeChecker where

import AST
import Position
import Tokens
import Message
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Control.Monad.Error
import Control.Applicative

{- Errors -}

-- | Result of type checking: either 'a' or an error with strings message
type Checked a = Either String a

-- | Throw a type error with a source position and a message
typeError pos msg = throwError ("Type error in " ++ show pos ++ ":\n" ++ msg ++ "\n")

-- | Error accumulator: used to store intermediate type checking results, when errors should be accumulated rather than reported immediately
data ErrorAccum a = ErrorAccum [String] a

instance Monad ErrorAccum where
  return x                = ErrorAccum [] x
  ErrorAccum errs x >>= f = case (f x) of
    ErrorAccum es v -> ErrorAccum (errs ++ es) v

-- | Transform a type checking result and default value into an error accumlator
accum :: Checked a -> a -> ErrorAccum a
accum cx y = case cx of
  Left e -> ErrorAccum [e] y
  Right x -> ErrorAccum [] x    
  
-- | Trnasform an error accumulator back into a rgeular type checking result  
report :: ErrorAccum a -> Checked a
report (ErrorAccum [] x) = Right x
report (ErrorAccum es _) = Left (concat (intersperse "\n" es))  

-- | Apply type checking f to all nodes in the initial context c,
-- | accumulating errors from all nodes and reporting them at the end;
-- | in case of success the modified context is passed on and in case of failure the context is unchanged
foldAccum :: (a -> b -> Checked a) -> a -> [b] -> Checked a
foldAccum f c nodes = report $ foldM (acc f) c nodes
  where
    acc f x y = accum (f x y) x
    
-- | Apply type checking f to all nodes,
-- | accumulating errors from all nodes and reporting them at the end
mapAccum :: (b -> Checked c) -> c -> [b] -> Checked [c]
mapAccum f def nodes = report $ mapM (acc f) nodes  
  where
    acc f x  = accum (f x) def
   
-- | Apply type checking f to all nodes throring away the result,
-- | accumulating errors from all nodes
mapAccumA_ :: (a -> Checked ()) -> [a] -> ErrorAccum ()
mapAccumA_ f nodes = mapM_ (acc f) nodes  
  where
    acc f x  = accum (f x) ()
    
-- | Same as mapAccumA_, but reporting the error at the end
mapAccum_ :: (a -> Checked ()) -> [a] -> Checked ()
mapAccum_ f nodes = report $ mapAccumA_ f nodes  

-- | Apply type checking f to all xs and ys throring away the result,
-- | accumulating errors from all nodes and reporting them at the end
zipWithAccum_ :: (a -> b -> Checked ()) -> [a] -> [b] -> Checked ()
zipWithAccum_ f xs ys = report $ zipWithM_ (acc f) xs ys  
  where
    acc f x y  = accum (f x y) ()
  
{- Context -}

-- | Typechecking context: 
data Context = Context
  {
    ctxPos :: SourcePos,
    ctxTypeConstructors :: M.Map Id Int,      -- type constructor arity
    ctxTypeSynonyms :: M.Map Id ([Id], Type), -- type synonym values
    ctxGlobals :: M.Map Id Type,              -- global variable types
    ctxConstants :: M.Map Id Type,            -- constant types
    ctxFunctions :: M.Map Id FSig,            -- function signatures
    ctxProcedures :: M.Map Id (PSig, [Id]),   -- procedure signatures and modifies-lists
    ctxTypeVars :: [Id],                      -- free type variables
    ctxIns :: M.Map Id Type,                  -- input parameter types
    ctxLocals :: M.Map Id Type,               -- local variable types
    ctxModifies :: [Id],                      -- variables in the modifies clause of the enclosing procedure
    ctxLabels :: [Id],                        -- all labels of the enclosing procedure body
    ctxEncLabels :: [Id],                     -- labels of all enclosing statements
    ctxTwoState :: Bool,                      -- is the context two-state? (procedure body or postcondition)
    ctxInLoop :: Bool                         -- is context inside a loop body?
  } deriving Show

emptyContext = Context {
    ctxPos              = noPos,
    ctxTypeConstructors = M.empty,
    ctxTypeSynonyms     = M.empty,
    ctxGlobals          = M.empty,
    ctxConstants        = M.empty,
    ctxFunctions        = M.empty,
    ctxProcedures       = M.empty,
    ctxTypeVars         = [],
    ctxIns              = M.empty,
    ctxLocals           = M.empty,
    ctxModifies         = [],
    ctxLabels           = [],
    ctxEncLabels        = [],
    ctxTwoState         = False,
    ctxInLoop           = False
  }

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
  
-- | unifier fv xs ys : most general unifier of xs and ys with free type variables fv   
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
  case boundUnifier fv bv1 (range1:domains1) bv2 (range2:domains2) of
    Nothing -> Nothing
    Just u -> M.union u <$> (unifier fv (update u xs) (update u ys))
  where
    update u = map (substitution u)
unifier _ _ _ = Nothing

-- | boundUnifier fv bv1 xs bv2 ys: most geenral unifier of xs and ys,
-- | where bv1 are bound type varuables in xs and bv2 are bound type variables in ys,
-- | and fv are free type variables of the enclosing context
boundUnifier fv bv1 xs bv2 ys = if length bv1 /= length bv2 || length xs /= length ys 
  then Nothing
  else case unifier (fv ++ bv1) xs (map replacedBV ys) of
    Nothing -> Nothing
    Just u -> if all isFreshBV (M.elems (bound u)) && not (any hasFreshBV (M.elems (free u)))
      then Just (free u)
      else Nothing
    where
      -- substitution of bound variables of m2 with fresh names
      replacedBV = substitution (M.fromList (zip bv2 (map idType freshBVNames)))
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

-- | Check that a type variable is fresh and add it to context  
checkTypeVar :: Context -> Id -> Checked Context
checkTypeVar c v
  | v `elem` typeNames c = typeError (ctxPos c) (v ++ " already used as a type constructor or synonym")
  | v `elem` ctxTypeVars c = typeError (ctxPos c) ("Multiple decalartions of type variable " ++ v)
  | otherwise = return c { ctxTypeVars = v : ctxTypeVars c }

-- | checkType c t : check that t is a correct type in context c (i.e. that all type names exist and have correct number of arguments)
checkType :: Context -> Type -> Checked ()
checkType c (MapType fv domains range) = do
  c' <- foldAccum checkTypeVar c fv
  mapAccum_ (checkType c') (domains ++ [range])
checkType c (Instance name args)
  | name `elem` ctxTypeVars c && null args = return ()
  | M.member name (ctxTypeConstructors c) = if n == length args 
    then mapAccum_ (checkType c) args
    else typeError (ctxPos c) ("Wrong number of arguments " ++ show (length args) ++ " given to the type constructor " ++ name ++ " (expected " ++ show n ++ ")")
  | M.member name (ctxTypeSynonyms c) = if length formals == length args
    then mapAccum_ (checkType c) args
    else typeError (ctxPos c) ("Wrong number of arguments " ++ show (length args) ++ " given to the type synonym " ++ name ++ " (expected " ++ show (length formals) ++ ")")
  | otherwise = typeError (ctxPos c) ("Not in scope: type constructor or synonym " ++ name)
    where 
      n = (M.!) (ctxTypeConstructors c) name
      formals = fst ((M.!) (ctxTypeSynonyms c) name)
checkType _ _ = return ()

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
checkExpression c (Pos pos e) = case e of
  TT -> return BoolType
  FF -> return BoolType
  Numeral n -> return IntType
  Var id -> case M.lookup id (allVars c) of
    Nothing -> typeError pos ("Not in scope: variable or constant " ++ id)
    Just t -> return t
  Application id args -> checkApplication cPos id args
  MapSelection m args -> checkMapSelection cPos m args
  MapUpdate m args val -> checkMapUpdate cPos m args val
  Old e1 -> if ctxTwoState c
    then checkExpression c e1
    else typeError pos ("Old expression in a single state context")
  UnaryExpression op e1 -> checkUnaryExpression cPos op e1
  BinaryExpression op e1 e2 -> checkBinaryExpression cPos op e1 e2
  Quantified qop fv vars e -> checkQuantified cPos qop fv vars e
  where
    cPos = c { ctxPos = pos }

checkApplication :: Context -> Id -> [Expression] -> Checked Type
checkApplication c id args = case M.lookup id (ctxFunctions c) of
  Nothing -> typeError (ctxPos c) ("Not in scope: function " ++ id)
  Just (FSig fv argTypes retType) -> do
    actualTypes <- mapAccum (checkExpression c) noType args
    case unifier fv argTypes actualTypes of
      Nothing -> typeError (ctxPos c) ("Could not match formal argument types " ++ commaSep (map show argTypes) ++
        " against actual argument types " ++ commaSep (map show actualTypes) ++
        " in the call to " ++ id)
      Just u -> return (substitution u retType)
    
checkMapSelection :: Context -> Expression -> [Expression] -> Checked Type
checkMapSelection c m args = do
  mType <- checkExpression c m
  case mType of
    MapType fv domainTypes rangeType -> do
      actualTypes <- mapAccum (checkExpression c) noType args
      case unifier fv domainTypes actualTypes of
        Nothing -> typeError (ctxPos c) ("Could not match map domain types " ++ commaSep (map show domainTypes) ++
          " against map selection types " ++ commaSep (map show actualTypes) ++
          " for the map " ++ show m)
        Just u -> return (substitution u rangeType)
    t -> typeError (ctxPos c) ("Map selection applied to a non-map " ++ show m ++ " of type " ++ show t)
  
checkMapUpdate :: Context -> Expression -> [Expression] -> Expression -> Checked Type
checkMapUpdate c m args val = do 
  t <- checkMapSelection c m args
  actualT <- checkExpression c val
  if t == actualT 
    then checkExpression c m 
    else typeError (ctxPos c) ("Update value type " ++ show actualT ++ " different from map range type " ++ show t)
    
checkUnaryExpression :: Context -> UnOp -> Expression -> Checked Type
checkUnaryExpression c op e
  | op == Neg = matchType IntType IntType
  | op == Not = matchType BoolType BoolType
  where 
    matchType t ret = do
      t' <- checkExpression c e
      if t' == t then return ret else typeError (ctxPos c) (errorMsg t' op)
    errorMsg t op = "Invalid argument type " ++ show t ++ " to unary operator" ++ show op
  
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
      if pred t1 t2 then return ret else typeError (ctxPos c) (errorMsg t1 t2 op)
    errorMsg t1 t2 op = "Invalid argument types " ++ show t1 ++ " and " ++ show t2 ++ " to binary operator" ++ show op
    
checkQuantified :: Context -> QOp -> [Id] -> [IdType] -> Expression -> Checked Type
checkQuantified c _ fv vars e = do
  c' <- foldAccum checkTypeVar c fv
  quantifiedScope <- foldAccum (checkIdType localScope ctxIns setIns) c' vars
  if not (null missingFV)
    then typeError (ctxPos c) ("Type variable(s) must occur in the bound variables of the quantification: " ++ commaSep missingFV) 
    else do
      t <- checkExpression quantifiedScope e
      case t of
        BoolType -> return BoolType
        _ -> typeError (ctxPos c) ("Quantified expression type " ++ show t ++ " different from " ++ show BoolType)
  where
    missingFV = filter (not . freeInVars) fv
    freeInVars v = any (isFree v) (map snd vars)
    
{- Statements -}

checkStatement :: Context -> Statement -> Checked ()
checkStatement c (Pos pos s) = case s of
  Assert e -> compareType cPos "assertion" BoolType e
  Assume e -> compareType cPos "assumption" BoolType e
  Havoc vars -> checkLefts cPos (nub vars) (length (nub vars))
  Assign lhss rhss -> checkAssign cPos lhss rhss
  Call lhss name args -> checkCall cPos lhss name args
  CallForall name args -> checkCallForall cPos name args
  If cond thenBlock elseBlock -> checkIf cPos cond thenBlock elseBlock
  While cond invs b -> checkWhile cPos cond invs b
  Goto ids -> checkGoto cPos ids
  Break Nothing -> checkSimpleBreak cPos
  Break (Just l) -> checkLabelBreak cPos l
  _ -> return ()
  where
    cPos = c { ctxPos = pos }

checkAssign :: Context -> [(Id , [[Expression]])] -> [Expression] -> Checked ()
checkAssign c lhss rhss = do
  checkLefts c (map fst lhss) (length rhss)
  rTypes <- mapAccum (checkExpression c) noType rhss
  zipWithAccum_ (compareType c "assignment left-hand side") rTypes (map selectExpr lhss) 
  where
    selectExpr (id, selects) = foldl mapSelectExpr (attachPos (ctxPos c) (Var id)) selects
        
checkCall :: Context -> [Id] -> Id -> [Expression] -> Checked ()
checkCall c lhss name args = case M.lookup name (ctxProcedures c) of
  Nothing -> typeError (ctxPos c) ("Not in scope: procedure " ++ name)
  Just (PSig fv argTypes retTypes, mods) -> if not (null (mods \\ ctxModifies c)) 
    then typeError (ctxPos c) ("Call modifies a global variable that is not in the enclosing procedure's modifies clause: " ++ commaSep (mods \\ ctxModifies c))
    else do
      actualArgTypes <- mapAccum (checkExpression c) noType args
      case unifier fv argTypes actualArgTypes of
        Nothing -> typeError (ctxPos c) ("Could not match formal argument types " ++ commaSep (map show argTypes) ++
          " against actual argument types " ++ commaSep (map show actualArgTypes) ++
          " in the call to " ++ name)
        Just u -> do
          checkLefts c lhss (length retTypes)
          zipWithAccum_ (compareType c "call left-hand side") (map (substitution u) retTypes) (map (attachPos (ctxPos c) . Var) lhss)
        
checkCallForall :: Context -> Id -> [WildcardExpression] -> Checked ()
checkCallForall c name args = case M.lookup name (ctxProcedures c) of
  Nothing -> typeError (ctxPos c) ("Not in scope: procedure " ++ name)
  Just (PSig fv argTypes _, mods) -> if not (null mods) 
    then typeError (ctxPos c) "Call forall to a procedure with a non-empty modifies clause"
    else do
      actualArgTypes <- mapAccum (checkExpression c) noType concreteArgs
      case unifier fv (concrete argTypes) actualArgTypes of
        Nothing -> typeError (ctxPos c) ("Could not match formal argument types " ++ commaSep (map show (concrete argTypes)) ++
          " against actual argument types " ++ commaSep (map show actualArgTypes) ++
          " in the call to " ++ name)
        Just u -> return ()
  where
    concreteArgs = [e | (Expr e) <- args]
    concrete at = [at !! i | i <- [0..length args - 1], isConcrete (args !! i)]
    isConcrete Wildcard = False
    isConcrete (Expr _) = True
    
checkIf :: Context -> WildcardExpression -> Block -> (Maybe Block) -> Checked ()
checkIf c cond thenBlock elseBlock = report $ do
  case cond of
    Wildcard -> return ()
    Expr e -> accum (compareType c "branching condition" BoolType e) ()
  accum (checkBlock c thenBlock) ()
  case elseBlock of
    Nothing -> return ()
    Just b -> accum (checkBlock c b) ()
    
checkWhile :: Context -> WildcardExpression -> [(Bool, Expression)] -> Block -> Checked ()
checkWhile c cond invs body = report $ do
  case cond of  
    Wildcard -> return ()
    Expr e -> accum (compareType c "loop condition" BoolType e) ()
  mapAccumA_ (compareType c "loop invariant" BoolType) (map snd invs)
  accum (checkBlock c {ctxInLoop = True} body) ()

checkGoto :: Context -> [Id] -> Checked ()  
checkGoto c ids = if not (null unknownLabels)
  then typeError (ctxPos c) ("Not in scope: label(s) " ++ separated "," unknownLabels)
  else return ()
  where
    unknownLabels = ids \\ ctxLabels c 
    
checkSimpleBreak :: Context -> Checked ()
checkSimpleBreak c = if not (ctxInLoop c)
  then typeError (ctxPos c) ("Break statement outside a loop")
  else return ()
  
checkLabelBreak :: Context -> Id -> Checked ()
checkLabelBreak c l = if not (l `elem` ctxEncLabels c)
  then typeError (ctxPos c) ("Break label " ++ l ++ " does not label an enclosing statement")
  else return ()
  
{- Blocks -}

-- | collectLabels c block: check that all labels in block and nested blocks are unique and add then to the context
collectLabels :: Context -> Block -> Checked Context
collectLabels c block = foldAccum checkLStatement c block
  where
    checkLStatement c (Pos pos (ls, (Pos _ st))) = do
      c' <- foldM (addLabel pos) c ls
      case st of
        If _ thenBlock mElseBlock -> do 
          c'' <- collectLabels c' thenBlock
          case mElseBlock of
            Nothing -> return c''
            Just elseBlock -> collectLabels c'' elseBlock
        While _ _ bodyBlock -> collectLabels c' bodyBlock
        _ -> return c'
    addLabel pos c l = if l `elem` ctxLabels c 
      then typeError pos ("Multiple occurrences of label " ++ l ++ " in a procedure body")
      else return c {ctxLabels = l : ctxLabels c}

-- | check every statement in the block
checkBlock :: Context -> Block -> Checked ()    
checkBlock c block = mapAccum_ (checkLStatement c) block
  where
    checkLStatement c (Pos _ (ls, st)) = checkStatement c { ctxEncLabels = ctxEncLabels c ++ ls} st
    
{- Declarations -}

-- | Check program in five passes
checkProgram :: Program -> Checked Context
checkProgram p = do
  pass1   <- foldAccum collectTypes emptyContext p                            -- collect type names from type declarations
  _pass2  <- mapAccum_ (checkTypeSynonyms pass1) p                            -- check values of type synonyms
  _pass3  <- mapAccum_ (checkCycles pass1 p) (M.keys (ctxTypeSynonyms pass1)) -- check that type synonyms do not form a cycle 
  pass4   <- foldAccum checkSignatures pass1 p                                -- check variable, constant, function and procedure signatures
  _pass5  <- mapAccum_ (checkBodies pass4) p                                  -- check axioms, function and procedure bodies, constant parent info
  return pass4

-- | Collect type names from type declarations
collectTypes :: Context -> Decl -> Checked Context
collectTypes c (Pos pos d) = case d of
  TypeDecl ts -> foldM checkTypeDecl c { ctxPos = pos } ts
  otherwise -> return c  

-- | Check uniqueness of type constructors and synonyms, and them in the context  
checkTypeDecl :: Context -> NewType -> Checked Context 
checkTypeDecl c (NewType name formals value)
  | name `elem` (typeNames c) = typeError (ctxPos c) ("Multiple declarations of type constructor or synonym " ++ name) 
  | otherwise = case value of
    Nothing -> return c { ctxTypeConstructors = M.insert name (length formals) (ctxTypeConstructors c) }
    Just t -> return c { ctxTypeSynonyms = M.insert name (formals, t) (ctxTypeSynonyms c) }

-- | Check that type arguments of type synonyms are fresh and values are valid types
checkTypeSynonyms :: Context -> Decl -> Checked ()
checkTypeSynonyms c (Pos pos d) = case d of
  TypeDecl ts -> mapAccum_ (checkNewType c { ctxPos = pos }) ts
  otherwise -> return ()
  where
    checkNewType c (NewType name formals (Just t)) = do
      c' <- foldAccum checkTypeVar c formals 
      checkType c' t
    checkNewType _ _ = return ()

-- | Check if type synonym declarations have cyclic dependences (program is passed for the purpose of error reporting)
checkCycles :: Context -> [Decl] -> Id -> Checked ()
checkCycles c decls id = checkCyclesWith c id (value id)
  where
    checkCyclesWith c id t = case t of
      Instance name args -> do
        if M.member name (ctxTypeSynonyms c)
          then if id == name 
            then typeError firstPos ("Cycle in the definition of type synonym " ++ id) 
            else checkCyclesWith c id (value name)
          else return ()
        mapAccum_ (checkCyclesWith c id) args
      MapType _ domains range -> mapAccum_ (checkCyclesWith c id) (range:domains)
      _ -> return ()
    value name = snd ((M.!) (ctxTypeSynonyms c) name)
    firstPos = head [pos | Pos pos (TypeDecl ts) <- decls, id `elem` map tId ts]

-- | Check variable, constant, function and procedures and add them to context
checkSignatures :: Context -> Decl -> Checked Context
checkSignatures c (Pos pos d) = case d of
  VarDecl vars -> foldAccum (checkIdType globalScope ctxGlobals setGlobals) cPos (map noWhere vars)
  ConstantDecl _ ids t _ _ -> foldAccum (checkIdType globalScope ctxConstants setConstants) cPos (zip ids (repeat t))
  FunctionDecl name fv args ret _ -> checkFunctionSignature cPos name fv args ret
  ProcedureDecl name fv args rets specs _ -> checkProcSignature cPos name fv args rets specs
  otherwise -> return c
  where
    cPos = c { ctxPos = pos }

-- | checkIdType scope get set c idType: check that declaration idType is fresh in scope, and if so add it to (get c) using (set c) 
checkIdType :: (Context -> M.Map Id Type) -> (Context -> M.Map Id Type) -> (Context -> M.Map Id Type -> Context) -> Context -> IdType -> Checked Context
checkIdType scope get set c (i, t)   
  | M.member i (scope c) = typeError (ctxPos c) ("Multiple declarations of variable or constant " ++ i)
  | otherwise = checkType c t >> return (c `set` M.insert i (resolve c t) (get c))

-- | Check uniqueness of function name, types of formals and add function to context
checkFunctionSignature :: Context -> Id -> [Id] -> [FArg] -> FArg -> Checked Context
checkFunctionSignature c name fv args ret
  | name `elem` funProcNames c = typeError (ctxPos c) ("Multiple declarations of function or procedure " ++ name)
  | otherwise = do
    c' <- foldAccum checkTypeVar c fv
    foldAccum checkFArg c' (args ++ [ret])
    if not (null missingFV) 
      then typeError (ctxPos c) ("Type variable(s) must occur in function arguments: " ++ commaSep missingFV)
      else return c { ctxFunctions = M.insert name (FSig fv (map snd args) (snd ret)) (ctxFunctions c) }
    where 
      checkFArg c (Just id, t) = checkIdType ctxIns ctxIns setIns c (id, t)
      checkFArg c (Nothing, t) = checkType c t >> return c
      missingFV = filter (not . freeInArgs) fv
      freeInArgs v = any (isFree v) (map snd args)
      
checkProcSignature :: Context -> Id -> [Id] -> [IdTypeWhere] -> [IdTypeWhere] -> [Spec] -> Checked Context
checkProcSignature c name fv args rets specs
  | name `elem` funProcNames c = typeError (ctxPos c) ("Multiple declarations of function or procedure " ++ name)
  | otherwise = do
    c' <- foldAccum checkTypeVar c fv
    foldAccum checkPArg c' (args ++ rets)
    if not (null missingFV) 
      then typeError (ctxPos c) ("Type variable(s) must occur in procedure arguments: " ++ commaSep missingFV)
      else return c { ctxProcedures = M.insert name (PSig fv (map itwType args) (map itwType rets), modifies specs) (ctxProcedures c) }
    where 
      checkPArg c arg = checkIdType ctxIns ctxIns setIns c (noWhere arg)
      missingFV = filter (not . freeInArgs) fv
      freeInArgs v = any (isFree v) (map itwType args)

-- | Check axioms, function and procedure bodies      
checkBodies :: Context -> Decl -> Checked ()
checkBodies c (Pos pos d) = case d of
  VarDecl vars -> mapAccum_ (checkWhere cPos) vars
  ConstantDecl _ ids t (Just edges) _ -> checkParentInfo cPos ids t (map snd edges)
  FunctionDecl name fv args ret (Just body) -> checkFunction cPos fv args ret body
  AxiomDecl e -> checkAxiom cPos e
  ProcedureDecl name fv args rets specs mb -> checkProcedure cPos fv args rets specs mb
  ImplementationDecl name fv args rets bodies -> checkImplementation cPos name fv args rets bodies	
  otherwise -> return ()
  where
    cPos = c { ctxPos = pos }  
  
-- | Check that "where" part is a valid boolean expression
checkWhere :: Context -> IdTypeWhere -> Checked ()
checkWhere c var = compareType c "where clause" BoolType (itwWhere var)

-- | Check that identifiers in parents are distinct constants of a proper type and do not occur among ids
checkParentInfo :: Context -> [Id] -> Type -> [Id] -> Checked ()
checkParentInfo c ids t parents = if length parents /= length (nub parents)
  then typeError (ctxPos c) ("Parent list contains duplicates: " ++ commaSep parents)
  else mapAccum_ checkParent parents
  where
    checkParent p = case M.lookup p (ctxConstants c) of
      Nothing -> typeError (ctxPos c) ("Not in scope: constant " ++ p)
      Just t' -> if t /= t'
        then typeError (ctxPos c) ("Parent type " ++ show t' ++ " is different from constant type " ++ show t)
        else if p `elem` ids
          then typeError (ctxPos c) ("Constant " ++ p ++ " is decalred to be its own parent")
          else return ()

-- | Check that axiom is a valid boolean expression    
checkAxiom :: Context -> Expression -> Checked ()
checkAxiom c e = compareType c {ctxGlobals = M.empty } "axiom" BoolType e
  
-- | Check that function body is a valid expression of the same type as the function return type
checkFunction :: Context -> [Id] -> [FArg] -> FArg -> Expression -> Checked ()
checkFunction c fv args ret body = do 
  functionScope <- foldAccum addFArg c { ctxTypeVars = fv } args
  compareType functionScope { ctxGlobals = M.empty } "function body" (snd ret) body
  where 
    addFArg c (Just id, t) = checkIdType ctxIns ctxIns setIns c (id, t)
    addFArg c  _ = return c
    
-- | Check "where" parts of procedure arguments and statements in its body
checkProcedure :: Context -> [Id] -> [IdTypeWhere] -> [IdTypeWhere] -> [Spec] -> (Maybe Body) -> Checked ()
checkProcedure c fv args rets specs mb = do 
  cArgs <- foldAccum (checkIdType localScope ctxIns setIns) c { ctxTypeVars = fv } (map noWhere args)
  mapAccum_ (checkWhere cArgs) args
  mapAccum_ (compareType cArgs "precondition" BoolType) (preconditions specs)
  cRets <- foldAccum (checkIdType localScope ctxLocals setLocals) cArgs (map noWhere rets)
  mapAccum_ (checkWhere cRets) rets
  mapAccum_ (compareType cRets {ctxTwoState = True} "postcondition" BoolType) (postconditions specs)
  if not (null invalidModifies)
    then typeError (ctxPos c) ("Identifier in a modifies clause does not denote a global variable: " ++ commaSep invalidModifies)
    else case mb of
      Nothing -> return ()
      Just body -> checkBody cRets { ctxModifies = modifies specs, ctxTwoState = True } body
  where invalidModifies = modifies specs \\ M.keys (ctxGlobals c)
  
-- | Check procedure body in context c  
checkBody :: Context -> Body -> Checked ()
checkBody c body = do
  bodyScope <- foldAccum (checkIdType localScope ctxLocals setLocals) c (map noWhere (concat (fst body)))
  mapAccum_ (checkWhere bodyScope) (concat (fst body))
  bodyScope' <- collectLabels bodyScope (snd body)
  checkBlock bodyScope' (snd body)

-- | Check that implementation corresponds to a known procedure and matches its signature, then checkk all bodies
checkImplementation :: Context -> Id -> [Id] -> [IdType] -> [IdType] -> [Body] -> Checked ()  
checkImplementation c name fv args rets bodies = case M.lookup name (ctxProcedures c) of
    Nothing -> typeError (ctxPos c) ("Not in scope: procedure " ++ name)
    Just (PSig fv' argTypes' retTypes', mods) -> case boundUnifier [] fv' (argTypes' ++ retTypes') fv (map snd (args ++ rets)) of
      Nothing -> typeError (ctxPos c) ("Could not match procedure signature " ++ show (PSig fv' argTypes' retTypes') ++
        " against implementation signature " ++ show (PSig fv (map snd args) (map snd rets)) ++
        " in the implementation of " ++ name)
      Just _ -> do
        cArgs <- foldAccum (checkIdType localScope ctxIns setIns) c { ctxTypeVars = fv } args
        cRets <- foldAccum (checkIdType localScope ctxLocals setLocals) cArgs rets
        mapAccum_ (checkBody cRets { ctxModifies = mods, ctxTwoState = True }) bodies
    
{- Misc -}

-- | compareType c msg t e: check that e is a valid expression in context c and its type is t
compareType :: Context -> String -> Type -> Expression -> Checked ()
compareType c msg t e = do
  t' <- checkExpression c e
  if t == t' 
    then return ()
    else typeError (ctxPos c) ("Type of " ++ msg ++ " (" ++ show t' ++ ") is different from " ++ show t)
    
-- | checkLefts c ids n: check that there are n ids, all ids are unique and denote mutable variables
checkLefts :: Context -> [Id] -> Int -> Checked ()
checkLefts c vars n = if length vars /= n 
  then typeError (ctxPos c) ("Expected " ++ show n ++ " left-hand sides and got " ++ show (length vars))
  else if vars /= nub vars
    then typeError (ctxPos c) ("Variable occurs more than once among left-handes of a parallel assignment")
    else if not (null immutableLhss)
      then typeError (ctxPos c) ("Assignment to immutable variable(s): " ++ commaSep immutableLhss)
      else if not (null invalidGlobals)
        then typeError (ctxPos c) ("Assignment to a global variable that is not in the enclosing procedure's modifies clause: " ++ commaSep invalidGlobals)
        else return ()      
  where 
    immutableLhss = vars \\ M.keys (mutableVars c)
    invalidGlobals = (vars \\ M.keys (ctxLocals c)) \\ ctxModifies c
  