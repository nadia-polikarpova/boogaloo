{- Type checker for Boogie 2 -}
module Language.Boogie.TypeChecker where

import Language.Boogie.AST
import Language.Boogie.Util
import Language.Boogie.Position
import Language.Boogie.PrettyPrinter
import Data.List
import Data.Maybe
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Error
import Control.Monad.Trans.Error hiding (throwError)
import Control.Applicative
import Text.PrettyPrint

{- Interface -}

-- | checkProgram p: check program p and return the type information in the global part of the context
checkProgram :: Program -> Checked Context
checkProgram (Program decls) = do
  pass1  <- foldAccum collectTypes emptyContext decls                            -- collect type names from type declarations
  _pass2 <- mapAccum_ (checkTypeSynonyms pass1) decls                            -- check values of type synonyms
  _pass3 <- mapAccum_ (checkCycles pass1 decls) (M.keys (ctxTypeSynonyms pass1)) -- check that type synonyms do not form a cycle 
  pass4  <- foldAccum checkSignatures pass1 decls                                -- check variable, constant, function and procedure signatures
  pass5  <- foldAccum checkBodies pass4 decls                                    -- check axioms, function and procedure bodies, constant parent info
  return pass5
  
-- | Type of expr in context c;
-- | fails if expr contains type errors.    
exprType :: Context -> Expression -> Type
exprType c expr = case checkExpression c expr of
  Left _ -> (error . show) (text "encountered ill-typed expression during execution:" <+> exprDoc expr)
  Right t -> t
  
-- | Local context of function sig with formal arguments formals and actual arguments actuals
-- | in a context where the return type is exprected to be mRetType (if known)
enterFunction :: FSig -> [Id] -> [Expression] -> Maybe Type -> Context -> Context 
enterFunction sig formals actuals mRetType c = c 
  {
    ctxTypeVars = [],
    ctxIns = M.fromList (zip formals argTypes),
    ctxLocals = M.empty,
    ctxModifies = [],
    ctxTwoState = False,
    ctxInLoop = False
  }
  where 
    inst = case fInstance c sig actuals mRetType of
      Left _ -> (error . show) (text "encountered ill-typed function application during execution:" <+> 
        text (fsigName sig) <+> parens (commaSep (map text formals)) <+>
        text "to actual arguments" <+> parens (commaSep (map exprDoc actuals)))
      Right u -> typeSubst u
    argTypes = map inst (fsigArgTypes sig)

-- | Local context of procedure sig with definition def and actual arguments actuals 
-- | in a call with left-hand sides lhss
enterProcedure :: PSig -> PDef -> [Expression] -> [Expression] -> Context -> Context 
enterProcedure sig def actuals lhss c = c 
  {
    ctxTypeVars = [],
    ctxIns = M.fromList $ zip ins inTypes,
    ctxLocals = M.union (M.fromList $ zip localNames localTypes) (M.fromList $ zip outs outTypes),
    ctxWhere = foldl addWhere (ctxWhere c) (zip (ins ++ outs ++ localNames) (paramWhere ++ localWhere)), 
    ctxModifies = psigModifies sig,
    ctxTwoState = True,
    ctxInLoop = False
  }
  where
    ins = pdefIns def
    outs = pdefOuts def
    locals = fst (pdefBody def)
    inst = case pInstance c sig actuals lhss of
      Left _ -> (error . show) (text "encountered ill-typed procedure call during execution:" <+> 
        text (psigName sig) <+> text "with actual arguments" <+> parens (commaSep (map exprDoc actuals)) <+>
        text "and left-hand sides" <+> parens (commaSep (map exprDoc lhss)))
      Right u -> typeSubst u
    inTypes = map inst (psigArgTypes sig)
    outTypes = map inst (psigRetTypes sig)
    localTypes = map (inst . itwType) locals
    localNames = map itwId locals
    addWhere m (id, w) = M.insert id w m
    localWhere = map itwWhere locals
    paramWhere = map (paramSubst sig def . itwWhere) (psigArgs sig ++ psigRets sig)
   
-- | Local context of a quantified expression   
enterQuantified :: [Id] -> [IdType] -> Context -> Context 
enterQuantified tv vars c = c' 
  {
    ctxIns = foldl addIn (ctxIns c) vars
  }
  where
    c' = c { ctxTypeVars = tv }
    addIn ins (id, t) = M.insert id (resolve c' t) ins

{- Errors -}

-- | Type error with a source position and a pretty-printed message
data TypeError = TypeError SourcePos Doc

instance ErrorList TypeError where
  listMsg s = [TypeError noPos (text s)]

-- | Pretty-printed type error  
typeErrorDoc (TypeError pos msgDoc) = text "Type error in" <+> text (show pos) $+$ msgDoc  
  
-- | Pretty-printed list of type errors
typeErrorsDoc errs = (vsep . punctuate newline . map typeErrorDoc) errs
  
-- | Result of type checking: either 'a' or a type error
type Checked a = Either [TypeError] a

-- | Throw a single type error
throwTypeError pos msgDoc = throwError [TypeError pos msgDoc]

-- | Error accumulator: used to store intermediate type checking results, when errors should be accumulated rather than reported immediately
data ErrorAccum a = ErrorAccum [TypeError] a

instance Monad ErrorAccum where
  return x                = ErrorAccum [] x
  ErrorAccum errs x >>= f = case (f x) of
    ErrorAccum es v -> ErrorAccum (errs ++ es) v

-- | Transform a type checking result and default value into an error accumlator
accum :: Checked a -> a -> ErrorAccum a
accum cx y = case cx of
  Left e -> ErrorAccum e y
  Right x -> ErrorAccum [] x    
  
-- | Transform an error accumulator back into a rgeular type checking result  
report :: ErrorAccum a -> Checked a
report (ErrorAccum [] x) = Right x
report (ErrorAccum es _) = Left es  

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
   
-- | Apply type checking f to all nodes throwing away the result,
-- | accumulating errors from all nodes
mapAccumA_ :: (a -> Checked ()) -> [a] -> ErrorAccum ()
mapAccumA_ f nodes = mapM_ (acc f) nodes  
  where
    acc f x  = accum (f x) ()
    
-- | Same as mapAccumA_, but reporting the error at the end
mapAccum_ :: (a -> Checked ()) -> [a] -> Checked ()
mapAccum_ f nodes = report $ mapAccumA_ f nodes  

-- | Apply type checking f to all xs and ys throwing away the result,
-- | accumulating errors from all nodes and reporting them at the end
zipWithAccum_ :: (a -> b -> Checked ()) -> [a] -> [b] -> Checked ()
zipWithAccum_ f xs ys = report $ zipWithM_ (acc f) xs ys  
  where
    acc f x y  = accum (f x y) ()
  
{- Context -}

-- | Typechecking context
data Context = Context
  {
    -- Global context:
    ctxTypeConstructors :: Map Id Int,      -- type constructor arity
    ctxTypeSynonyms :: Map Id ([Id], Type), -- type synonym values
    ctxGlobals :: Map Id Type,              -- global variable types (type synonyms resolved)
    ctxConstants :: Map Id Type,            -- constant types (type synonyms resolved)
    ctxFunctions :: Map Id FSig,            -- function signatures (type synonyms resolved)
    ctxProcedures :: Map Id PSig,           -- procedure signatures (type synonyms resolved)
    ctxWhere :: Map Id Expression,          -- where clauses of variables (global and local)
    -- Local context:
    ctxTypeVars :: [Id],                    -- free type variables
    ctxIns :: Map Id Type,                  -- input parameter types
    ctxLocals :: Map Id Type,               -- local variable types
    ctxModifies :: [Id],                    -- variables in the modifies clause of the enclosing procedure
    ctxLabels :: [Id],                      -- all labels of the enclosing procedure body
    ctxEncLabels :: [Id],                   -- labels of all enclosing statements
    ctxTwoState :: Bool,                    -- is the context two-state? (procedure body or postcondition)
    ctxInLoop :: Bool,                      -- is context inside a loop body?
    ctxPos :: SourcePos                     -- position in the source code
  }

emptyContext = Context {
    ctxTypeConstructors = M.empty,
    ctxTypeSynonyms     = M.empty,
    ctxGlobals          = M.empty,
    ctxConstants        = M.empty,
    ctxFunctions        = M.empty,
    ctxProcedures       = M.empty,
    ctxWhere            = M.empty,
    ctxTypeVars         = [],
    ctxIns              = M.empty,
    ctxLocals           = M.empty,
    ctxModifies         = [],
    ctxLabels           = [],
    ctxEncLabels        = [],
    ctxTwoState         = False,
    ctxInLoop           = False,
    ctxPos              = noPos
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
-- | All variables that can be assigned to (local variables and global variables)
mutableVars c = M.union (ctxGlobals c) (ctxLocals c)
-- | All variables that can have where clauses (everything except constants)
allVars c = M.union (localScope c) (ctxGlobals c)
-- | All variables and constants (local-scope preferred)
allNames c = M.union (localScope c) (globalScope c)
-- | Names of functions and procedures
funProcNames c = M.keys (ctxFunctions c) ++ M.keys (ctxProcedures c)
-- | Signature of funtion name
funSig name c = ctxFunctions c ! name
-- | Signature of procedure name
procSig name c = ctxProcedures c ! name    
  
{- Types -}
  
-- | Check that a type variable is fresh and add it to context  
checkTypeVar :: Context -> Id -> Checked Context
checkTypeVar c v
  | v `elem` typeNames c = throwTypeError (ctxPos c) (text v <+> text "already used as a type constructor or synonym")
  | v `elem` ctxTypeVars c = throwTypeError (ctxPos c) (text "Multiple decalartions of type variable" <+> text v)
  | otherwise = return c { ctxTypeVars = v : ctxTypeVars c }

-- | checkType c t : check that t is a correct type in context c (i.e. that all type names exist and have correct number of arguments)
checkType :: Context -> Type -> Checked ()
checkType c (MapType tv domains range) = do
  c' <- foldAccum checkTypeVar c tv
  mapAccum_ (checkType c') (domains ++ [range])
checkType c (Instance name args)
  | name `elem` ctxTypeVars c && null args = return ()
  | M.member name (ctxTypeConstructors c) = if n == length args 
    then mapAccum_ (checkType c) args
    else throwTypeError (ctxPos c) (text "Wrong number of arguments" <+> int (length args) <+> text "given to the type constructor" <+> text name <+> 
      parens (text "expected" <+> int n))
  | M.member name (ctxTypeSynonyms c) = if length formals == length args
    then mapAccum_ (checkType c) args
    else throwTypeError (ctxPos c) (text "Wrong number of arguments " <+> int (length args) <+> text "given to the type synonym" <+> text name <+> 
      parens (text "expected" <+> int (length formals)))
  | otherwise = throwTypeError (ctxPos c) (text "Not in scope: type constructor or synonym" <+> text name)
    where 
      n = ctxTypeConstructors c ! name
      formals = fst (ctxTypeSynonyms c ! name)
checkType _ _ = return ()

-- | resolve c t : type t with all type synonyms resolved according to binding in c      
resolve :: Context -> Type -> Type
resolve c (MapType tv domains range) = MapType tv (map (resolve c') domains) (resolve c' range)
  where c' = c { ctxTypeVars = ctxTypeVars c ++ tv }
resolve c (Instance name args) 
  | name `elem` ctxTypeVars c = Instance name args
  | otherwise = case M.lookup name (ctxTypeSynonyms c) of
    Nothing -> Instance name (map (resolve c) args)
    Just (formals, t) -> resolve c (typeSubst (M.fromList (zip formals args)) t)
resolve _ t = t

-- | Instantiation of type variables in a function signature sig given the actual arguments actuals in a context c 
-- | and possibly a return type mRetType (if known from the context)
fInstance :: Context -> FSig -> [Expression] -> Maybe Type -> Checked TypeBinding
fInstance c sig actuals mRetType = case mRetType of
    Nothing -> if not (null retOnlyTVs) 
      then throwTypeError (ctxPos c) (text "Cannot infer type arguments from the context:" <+> commaSep (map text retOnlyTVs) <+> text "(insert a coercion)")
      else do
        actualTypes <- mapAccum (checkExpression c) noType actuals
        case oneSidedUnifier (fsigTypeVars sig) (fsigArgTypes sig) (ctxTypeVars c) actualTypes of
          Nothing -> throwTypeError (ctxPos c) (text "Could not match formal argument types" <+> 
            doubleQuotes (commaSep (map typeDoc (fsigArgTypes sig))) <+>
            text "against actual argument types" <+> 
            doubleQuotes (commaSep (map typeDoc actualTypes)) <+>
            text "in the call to" <+> text (fsigName sig))
          Just u -> return u
    Just retType -> do
      actualTypes <- mapAccum (checkExpression c) noType actuals
      case oneSidedUnifier (fsigTypeVars sig) (fsigRetType sig : fsigArgTypes sig) (ctxTypeVars c) (retType : actualTypes) of
        Nothing -> throwTypeError (ctxPos c) (text "Could not match function signature" <+> 
          doubleQuotes (sigDoc (fsigArgTypes sig) [fsigRetType sig]) <+>
          text "against actual types" <+> 
          doubleQuotes (sigDoc actualTypes [retType]) <+>
          text "in the call to" <+> text (fsigName sig))
        Just u -> return u
  where
    tvs = fsigTypeVars sig
    retOnlyTVs = filter (not . freeInArgs) tvs
    freeInArgs tv = any (tv `isFreeIn`) (fsigArgTypes sig)
      
-- | Instantiation of type variables in a procedure signature sig given the actual arguments actuals and call left-hand sides lhss, in a context c 
pInstance :: Context -> PSig -> [Expression] -> [Expression] -> Checked TypeBinding
pInstance c sig actuals lhss = do
  actualTypes <- mapAccum (checkExpression c) noType actuals
  lhssTypes <- mapAccum (checkExpression c) noType lhss
  case oneSidedUnifier (psigTypeVars sig) (psigArgTypes sig ++ psigRetTypes sig) (ctxTypeVars c) (actualTypes ++ lhssTypes) of
    Nothing -> throwTypeError (ctxPos c) (text "Could not match procedure signature" <+> 
      doubleQuotes (sigDoc (psigArgTypes sig) (psigRetTypes sig)) <+>
      text "against actual types" <+> 
      doubleQuotes (sigDoc actualTypes lhssTypes) <+>
      text "in the call to" <+> text (psigName sig))
    Just u -> return u    
  
{- Expressions -}

-- | requires all types in the context be valid and type synonyms be resolved
checkExpression :: Context -> Expression -> Checked Type
checkExpression c (Pos pos e) = case e of
  TT -> return BoolType
  FF -> return BoolType
  Numeral n -> return IntType
  Var id -> case M.lookup id (allNames c) of
    Nothing -> throwTypeError pos (text "Not in scope: variable or constant" <+> text id)
    Just t -> return t
  Application id args -> checkApplication cPos id args Nothing
  MapSelection m args -> checkMapSelection cPos m args
  MapUpdate m args val -> checkMapUpdate cPos m args val
  Old e1 -> if ctxTwoState c
    then checkExpression c { ctxLocals = M.empty } e1
    else throwTypeError pos (text "Old expression in a single state context")
  IfExpr cond e1 e2 -> checkIfExpression cPos cond e1 e2
  Coercion e t -> checkCoercion cPos e t
  UnaryExpression op e1 -> checkUnaryExpression cPos op e1
  BinaryExpression op e1 e2 -> checkBinaryExpression cPos op e1 e2
  Quantified qop tv vars e -> checkQuantified cPos qop tv vars e
  where
    cPos = c { ctxPos = pos }

-- | mRetType stored function return type if known from the context (currently: if used inside a coercion);
-- | it is a temporary workaround for generic return types of functions    
checkApplication :: Context -> Id -> [Expression] -> Maybe Type -> Checked Type
checkApplication c id args mRetType = case M.lookup id (ctxFunctions c) of
  Nothing -> throwTypeError (ctxPos c) (text "Not in scope: function" <+> text id)
  Just sig -> do
    u <- fInstance c sig args mRetType
    return $ typeSubst u (fsigRetType sig)
    
checkMapSelection :: Context -> Expression -> [Expression] -> Checked Type
checkMapSelection c m args = do
  mType <- checkExpression c m
  case mType of
    MapType tv domainTypes rangeType -> do
      actualTypes <- mapAccum (checkExpression c) noType args
      case oneSidedUnifier tv domainTypes (ctxTypeVars c) actualTypes of
        Nothing -> throwTypeError (ctxPos c) (text "Could not match map domain types" <+> commaSep (map typeDoc domainTypes) <+>
          text "against map selection types" <+> commaSep (map typeDoc actualTypes) <+>
          text "for the map" <+> exprDoc m)
        Just u -> return (typeSubst u rangeType)
    t -> throwTypeError (ctxPos c) (text "Map selection applied to a non-map" <+> exprDoc m <+> text "of type" <+> typeDoc t)
  
checkMapUpdate :: Context -> Expression -> [Expression] -> Expression -> Checked Type
checkMapUpdate c m args val = do 
  t <- checkMapSelection c m args
  actualT <- checkExpression c val
  if t <==> actualT 
    then checkExpression c m 
    else throwTypeError (ctxPos c) (text "Update value type" <+> typeDoc actualT <+> text "different from map range type" <+> typeDoc t)
    
checkIfExpression :: Context -> Expression -> Expression -> Expression -> Checked Type    
checkIfExpression c cond e1 e2 = do
  compareType c "if-expression condition" BoolType cond
  t <- checkExpression c e1
  compareType c "else-part of the if-expression" t e2
  return t
  
checkCoercion :: Context -> Expression -> Type -> Checked Type
checkCoercion c e t = do
  checkType c t
  let t' = resolve c t
  case contents e of
    Application id args -> checkApplication cPos id args (Just t')
    _ -> compareType c "coerced expression" t' e >> return t'
  where cPos = c { ctxPos = position e }
    
checkUnaryExpression :: Context -> UnOp -> Expression -> Checked Type
checkUnaryExpression c op e
  | op == Neg = matchType IntType IntType
  | op == Not = matchType BoolType BoolType
  where 
    matchType t ret = do
      t' <- checkExpression c e
      if t' <==> t then return ret else throwTypeError (ctxPos c) (errorMsg t' op)
    errorMsg t op = text "Invalid argument type" <+> typeDoc t <+> text "to unary operator" <+> unOpDoc op
  
checkBinaryExpression :: Context -> BinOp -> Expression -> Expression -> Checked Type
checkBinaryExpression c op e1 e2
  | elem op [Plus, Minus, Times, Div, Mod] = matchTypes (\t1 t2 -> t1 <==> IntType && t2 <==> IntType) IntType
  | elem op [And, Or, Implies, Explies, Equiv] = matchTypes (\t1 t2 -> t1 <==> BoolType && t2 <==> BoolType) BoolType
  | elem op [Ls, Leq, Gt, Geq] = matchTypes (\t1 t2 -> t1 <==> IntType && t2 <==> IntType) BoolType
  | elem op [Eq, Neq] = matchTypes (\t1 t2 -> isJust (unifier (ctxTypeVars c) [t1] [t2])) BoolType
  | op == Lc = matchTypes (<==>) BoolType
  where 
    matchTypes pred ret = do
      t1 <- checkExpression c e1
      t2 <- checkExpression c e2
      if pred t1 t2 then return ret else throwTypeError (ctxPos c) (errorMsg t1 t2 op)
    errorMsg t1 t2 op = text "Invalid argument types" <+> typeDoc t1 <+> text "and" <+> typeDoc t2 <+> text "to binary operator" <+> binOpDoc op
    
checkQuantified :: Context -> QOp -> [Id] -> [IdType] -> Expression -> Checked Type
checkQuantified c Lambda tv vars e = do
  c' <- foldAccum checkTypeVar c tv
  quantifiedScope <- foldAccum (checkIdType localScope ctxIns setIns) c' vars
  if not (null missingTV)
    then throwTypeError (ctxPos c) (text "Type variable(s) must occur among the types of lambda parameters:" <+> commaSep (map text missingTV)) 
    else do
      rangeType <- checkExpression quantifiedScope e
      return $ MapType tv varTypes rangeType
  where
    varTypes = map snd vars
    missingTV = filter (not . freeInVars) tv    
    freeInVars v = any (v `isFreeIn`) varTypes      
checkQuantified c qop tv vars e = do
  c' <- foldAccum checkTypeVar c tv
  quantifiedScope <- foldAccum (checkIdType localScope ctxIns setIns) c' vars
  compareType quantifiedScope "quantified expression" BoolType e
  return BoolType
    
{- Statements -}

checkStatement :: Context -> Statement -> Checked ()
checkStatement c (Pos pos s) = case s of
  Predicate (SpecClause _ _ e) -> compareType cPos "predicate" BoolType e
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
  Nothing -> throwTypeError (ctxPos c) (text "Not in scope: procedure" <+> text name)
  Just sig -> let illegalModifies = psigModifies sig \\ ctxModifies c in
    if not (null illegalModifies) 
    then throwTypeError (ctxPos c) (text "Call modifies a global variable that is not in the enclosing procedure's modifies clause:" <+> commaSep (map text illegalModifies))
    else do
      checkLefts c lhss (length $ psigRetTypes sig)
      let lhssExpr = map (attachPos (ctxPos c) . Var) lhss
      pInstance c sig args lhssExpr >> return ()      
        
checkCallForall :: Context -> Id -> [WildcardExpression] -> Checked ()
checkCallForall c name args = case M.lookup name (ctxProcedures c) of
  Nothing -> throwTypeError (ctxPos c) (text "Not in scope: procedure" <+> text name)
  Just sig -> if not (null (psigModifies sig)) 
    then throwTypeError (ctxPos c) (text "Call forall to a procedure with a non-empty modifies clause")
    else pInstance c sig { psigArgs = concrete (psigArgs sig) } concreteArgs [] >> return ()
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
    
checkWhile :: Context -> WildcardExpression -> [SpecClause] -> Block -> Checked ()
checkWhile c cond invs body = report $ do
  case cond of  
    Wildcard -> return ()
    Expr e -> accum (compareType c "loop condition" BoolType e) ()
  mapAccumA_ (compareType c "loop invariant" BoolType) (map specExpr invs)
  accum (checkBlock c {ctxInLoop = True} body) ()

checkGoto :: Context -> [Id] -> Checked ()  
checkGoto c ids = if not (null unknownLabels)
  then throwTypeError (ctxPos c) (text "Not in scope: label(s)" <+> commaSep (map text unknownLabels))
  else return ()
  where
    unknownLabels = ids \\ ctxLabels c 
    
checkSimpleBreak :: Context -> Checked ()
checkSimpleBreak c = if not (ctxInLoop c)
  then throwTypeError (ctxPos c) (text "Break statement outside a loop")
  else return ()
  
checkLabelBreak :: Context -> Id -> Checked ()
checkLabelBreak c l = if not (l `elem` ctxEncLabels c)
  then throwTypeError (ctxPos c) (text "Break label" <+> text l <+> text "does not label an enclosing statement")
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
      then throwTypeError pos (text "Multiple occurrences of label" <+> text l <+> text "in a procedure body")
      else return c {ctxLabels = l : ctxLabels c}

-- | check every statement in the block
checkBlock :: Context -> Block -> Checked ()    
checkBlock c block = mapAccum_ (checkLStatement c) block
  where
    checkLStatement c (Pos _ (ls, st)) = checkStatement c { ctxEncLabels = ctxEncLabels c ++ ls} st
    
{- Declarations -}

-- | Collect type names from type declarations
collectTypes :: Context -> Decl -> Checked Context
collectTypes c (Pos pos d) = case d of
  TypeDecl ts -> foldM checkTypeDecl c { ctxPos = pos } ts
  otherwise -> return c  

-- | Check uniqueness of type constructors and synonyms, and them in the context  
checkTypeDecl :: Context -> NewType -> Checked Context 
checkTypeDecl c (NewType name formals value)
  | name `elem` (typeNames c) = throwTypeError (ctxPos c) (text "Multiple declarations of type constructor or synonym" <+> text name) 
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
            then throwTypeError firstPos (text "Cycle in the definition of type synonym" <+> text id) 
            else checkCyclesWith c id (value name)
          else return ()
        mapAccum_ (checkCyclesWith c id) args
      MapType _ domains range -> mapAccum_ (checkCyclesWith c id) (range:domains)
      _ -> return ()
    value name = snd (ctxTypeSynonyms c ! name)
    firstPos = head [pos | Pos pos (TypeDecl ts) <- decls, id `elem` map tId ts]

-- | Check variable, constant, function and procedures and add them to context
checkSignatures :: Context -> Decl -> Checked Context
checkSignatures c (Pos pos d) = case d of
  VarDecl vars -> foldAccum (checkIdType globalScope ctxGlobals setGlobals) cPos (map noWhere vars)
  ConstantDecl _ ids t _ _ -> foldAccum (checkIdType globalScope ctxConstants setConstants) cPos (zip ids (repeat t))
  FunctionDecl name tv args ret _ -> checkFunctionSignature cPos name tv args ret
  ProcedureDecl name tv args rets specs _ -> checkProcSignature cPos name tv args rets specs
  otherwise -> return c
  where
    cPos = c { ctxPos = pos }

-- | checkIdType scope get set c idType: check that declaration idType is fresh in scope, and if so add it to (get c) using (set c) 
checkIdType :: (Context -> Map Id Type) -> (Context -> Map Id Type) -> (Context -> Map Id Type -> Context) -> Context -> IdType -> Checked Context
checkIdType scope get set c (i, t)   
  | M.member i (scope c) = throwTypeError (ctxPos c) (text "Multiple declarations of variable or constant" <+> text i)
  | otherwise = checkType c t >> return (c `set` M.insert i (resolve c t) (get c))

-- | Check uniqueness of function name, types of formals and add function to context
checkFunctionSignature :: Context -> Id -> [Id] -> [FArg] -> FArg -> Checked Context
checkFunctionSignature c name tv args ret
  | name `elem` funProcNames c = throwTypeError (ctxPos c) (text "Multiple declarations of function or procedure" <+> text name)
  | otherwise = do
    c' <- foldAccum checkTypeVar c tv
    foldAccum checkFArg c' params
    if not (null missingTV) 
      then throwTypeError (ctxPos c) (text "Type variable(s) must occur in function arguments or return type:" <+> commaSep (map text missingTV))
      else return $ addFSig c name (FSig name tv argTypes retType) 
    where
      params = args ++ [ret]
      checkFArg c (Just id, t) = checkIdType ctxIns ctxIns setIns c (id, t)
      checkFArg c (Nothing, t) = checkType c t >> return c
      missingTV = filter (not . freeInParams) tv
      freeInParams v = any (v `isFreeIn`) (map snd params)
      addFSig c name sig = c { ctxFunctions = M.insert name sig (ctxFunctions c) }
      argTypes = map (resolve c . snd) args
      retType = (resolve c . snd) ret
      
checkProcSignature :: Context -> Id -> [Id] -> [IdTypeWhere] -> [IdTypeWhere] -> [Contract] -> Checked Context
checkProcSignature c name tv args rets specs
  | name `elem` funProcNames c = throwTypeError (ctxPos c) (text "Multiple declarations of function or procedure" <+> text name)
  | otherwise = do
    c' <- foldAccum checkTypeVar c tv
    foldAccum checkPArg c' params
    if not (null missingTV) 
      then throwTypeError (ctxPos c) (text "Type variable(s) must occur in procedure in- our out-parameters:" <+> commaSep (map text missingTV))
      else return $ addPSig c name (PSig name tv (map resolveType args) (map resolveType rets) specs)
    where
      params = args ++ rets
      checkPArg c arg = checkIdType ctxIns ctxIns setIns c (noWhere arg)
      missingTV = filter (not . freeInParams) tv
      freeInParams v = any (v `isFreeIn`) (map itwType params)
      addPSig c name sig = c { ctxProcedures = M.insert name sig (ctxProcedures c) }
      resolveType (IdTypeWhere id t w) = IdTypeWhere id (resolve c t) w

-- | Check axioms, function and procedure bodies      
checkBodies :: Context -> Decl -> Checked Context
checkBodies c (Pos pos d) = case d of
  VarDecl vars -> foldAccum checkWhere cPos vars
  ConstantDecl _ ids t (Just edges) _ -> checkParentInfo cPos ids t (map snd edges) >> return c
  FunctionDecl name tv args ret (Just body) -> checkFunction cPos name tv args body >> return c
  AxiomDecl e -> checkAxiom cPos e >> return c
  ProcedureDecl name tv args rets specs mb -> checkProcedure cPos tv args rets specs mb >> return c
  ImplementationDecl name tv args rets bodies -> checkImplementation cPos name tv args rets bodies >> return c
  otherwise -> return c
  where
    cPos = c { ctxPos = pos }  
  
-- | Check that "where" part is a valid boolean expression
checkWhere :: Context -> IdTypeWhere -> Checked Context
checkWhere c var = do
  compareType c "where clause" BoolType (itwWhere var)
  return c { ctxWhere = M.insert (itwId var) (itwWhere var) (ctxWhere c) }

-- | Check that identifiers in parents are distinct constants of a proper type and do not occur among ids
checkParentInfo :: Context -> [Id] -> Type -> [Id] -> Checked ()
checkParentInfo c ids t parents = if length parents /= length (nub parents)
  then throwTypeError (ctxPos c) (text "Parent list contains duplicates:" <+> commaSep (map text parents))
  else mapAccum_ checkParent parents
  where
    checkParent p = case M.lookup p (ctxConstants c) of
      Nothing -> throwTypeError (ctxPos c) (text "Not in scope: constant" <+> text p)
      Just t' -> if not (t <==> t')
        then throwTypeError (ctxPos c) (text "Parent type" <+> typeDoc t' <+> text "is different from constant type" <+> typeDoc t)
        else if p `elem` ids
          then throwTypeError (ctxPos c) (text "Constant" <+> text p <+> text "is decalred to be its own parent")
          else return ()    

-- | Check that axiom is a valid boolean expression    
checkAxiom :: Context -> Expression -> Checked ()
checkAxiom c e = compareType c {ctxGlobals = M.empty } "axiom" BoolType e
  
-- | Check that function body is a valid expression of the same type as the function return type
checkFunction :: Context -> Id -> [Id] -> [FArg] -> Expression -> Checked ()
checkFunction c name tv args body = do 
  functionScope <- foldAccum addFArg c { ctxTypeVars = tv } args
  compareType functionScope { ctxGlobals = M.empty } "function body" retType body
  where 
    addFArg c (Just id, t) = checkIdType ctxIns ctxIns setIns c (id, t)
    addFArg c  _ = return c
    sig = funSig name c
    retType = fsigRetType sig
        
-- | Check "where" parts of procedure arguments and statements in its body
checkProcedure :: Context -> [Id] -> [IdTypeWhere] -> [IdTypeWhere] -> [Contract] -> (Maybe Body) -> Checked ()
checkProcedure c tv args rets specs mb = do 
  cArgs <- foldAccum (checkIdType localScope ctxIns setIns) c { ctxTypeVars = tv } (map noWhere args)
  _ <- foldAccum checkWhere cArgs args
  mapAccum_ (compareType cArgs "precondition" BoolType . specExpr) (preconditions specs)
  cRets <- foldAccum (checkIdType localScope ctxLocals setLocals) cArgs (map noWhere rets)
  _ <- foldAccum checkWhere cRets rets
  mapAccum_ (compareType cRets {ctxTwoState = True} "postcondition" BoolType . specExpr) (postconditions specs)
  if not (null invalidModifies)
    then throwTypeError (ctxPos c) (text "Identifier in a modifies clause does not denote a global variable:" <+> commaSep (map text invalidModifies))
    else case mb of
      Nothing -> return ()
      Just body -> checkBody cRets { ctxModifies = modifies specs, ctxTwoState = True } body
  where invalidModifies = modifies specs \\ M.keys (ctxGlobals c)
  
-- | Check procedure body in context c  
checkBody :: Context -> Body -> Checked ()
checkBody c body = do
  bodyScope <- foldAccum (checkIdType localScope ctxLocals setLocals) c (map noWhere (concat (fst body)))
  _ <- foldAccum checkWhere bodyScope (concat (fst body))
  bodyScope' <- collectLabels bodyScope (snd body)
  checkBlock bodyScope' (snd body)

-- | Check that implementation corresponds to a known procedure and matches its signature, then check all bodies
checkImplementation :: Context -> Id -> [Id] -> [IdType] -> [IdType] -> [Body] -> Checked ()  
checkImplementation c name tv args rets bodies = case M.lookup name (ctxProcedures c) of
    Nothing -> throwTypeError (ctxPos c) (text "Not in scope: procedure" <+> text name)
    Just sig -> case boundUnifier [] (psigTypeVars sig) (psigArgTypes sig ++ psigRetTypes sig) tv (argTypes ++ retTypes) of
      Nothing -> throwTypeError (ctxPos c) (text "Could not match procedure signature" <+> 
        doubleQuotes (sigDoc (psigArgTypes sig) (psigRetTypes sig)) <+>
        text "against implementation signature" <+>
        doubleQuotes (sigDoc argTypes retTypes) <+>
        text "in the implementation of" <+> text name)
      Just _ -> do
        cArgs <- foldAccum (checkIdType localScope ctxIns setIns) c { ctxTypeVars = tv } args
        cRets <- foldAccum (checkIdType localScope ctxLocals setLocals) cArgs rets
        mapAccum_ (checkBody cRets { ctxModifies = (psigModifies sig), ctxTwoState = True }) bodies
  where
    argTypes = map (resolve c . snd) args
    retTypes = map (resolve c . snd) rets        
    
{- Misc -}

-- | compareType c msg t e: check that e is a valid expression in context c and its type is t
-- | (requires type synonyms in t be resolved)
compareType :: Context -> String -> Type -> Expression -> Checked ()
compareType c msg t e = do
  t' <- checkExpression c e
  if t <==> t' 
    then return ()
    else throwTypeError (ctxPos c) (text "Type of" <+> text msg <+> doubleQuotes (typeDoc t') <+> text "is different from" <+> doubleQuotes (typeDoc t))
    
-- | checkLefts c ids n: check that there are n ids, all ids are unique and denote mutable variables
checkLefts :: Context -> [Id] -> Int -> Checked ()
checkLefts c vars n = if length vars /= n 
  then throwTypeError (ctxPos c) (text "Expected" <+> int n <+> text "left-hand sides and got" <+> int (length vars))
  else if vars /= nub vars
    then throwTypeError (ctxPos c) (text "Variable occurs more than once among left-handes of a parallel assignment")
    else if not (null immutableLhss)
      then throwTypeError (ctxPos c) (text "Assignment to immutable variable(s):" <+> commaSep (map text immutableLhss))
      else if not (null invalidGlobals)
        then throwTypeError (ctxPos c) (text "Assignment to a global variable that is not in the enclosing procedure's modifies clause:" <+> commaSep (map text invalidGlobals))
        else return ()      
  where 
    immutableLhss = vars \\ M.keys (mutableVars c)
    invalidGlobals = (vars \\ M.keys (ctxLocals c)) \\ ctxModifies c
  