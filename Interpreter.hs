{- Interpreter for Boogie 2 -}
module Interpreter where

import AST
import Util
import Position
import PrettyPrinter
import qualified TypeChecker as TC
import BasicBlocks
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Error
import Control.Applicative hiding (empty)
import Control.Monad.State
import Text.PrettyPrint

{- Interface -}

-- | Execute program p with type context tc (produced by the type checker) and entry point main, 
-- | and return the values of global variables;
-- | main must have no arguments
executeProgram :: Program -> TypeContext -> Id -> Either RuntimeError (Map Id Value)
executeProgram p tc main = envGlobals <$> finalEnvironment
  where
    initEnvironment = emptyEnv { envTypeContext = tc }
    finalEnvironment = case runState (runErrorT programState) initEnvironment of
      (Left err, _) -> Left err
      (_, env)      -> Right env            
    programState = do
      collectDefinitions p
      procedures <- gets envProcedures
      case M.lookup main procedures of
        Nothing -> throwRuntimeError (NoEntryPoint main) noPos
        Just (def : defs) -> do
          execProcedure main def [] >> return ()
      
{- State -}

data Value = IntValue Integer |   -- Integer value
  BoolValue Bool |                -- Boolean value
  MapValue (Map [Value] Value) |  -- Value of a map type
  CustomValue Integer             -- Value of a user-defined type (values with the same code are considered equal)
  deriving (Eq, Ord)
  
-- | Default value of a type (used to initialize variables)  
defaultValue :: Type -> Value
defaultValue BoolType         = BoolValue False  
defaultValue IntType          = IntValue 0
defaultValue (MapType _ _ _)  = MapValue M.empty
defaultValue (Instance _ _)   = CustomValue 0  

-- | Pretty-printed value
valueDoc :: Value -> Doc
valueDoc (IntValue n) = integer n
valueDoc (BoolValue False) = text "false"
valueDoc (BoolValue True) = text "true"
valueDoc (MapValue m) = brackets (commaSep (map itemDoc (M.toList m)))
  where itemDoc (keys, v) = commaSep (map valueDoc keys) <+> text "->" <+>  valueDoc v
valueDoc (CustomValue n) = text "custom_" <> integer n
  
type TypeContext = TC.Context

data Environment = Environment
  {
    envLocals :: Map Id Value,          -- Local variable names to values
    envGlobals :: Map Id Value,         -- Global variable names to values
    envOld :: Map Id Value,             -- Global variable names to old values (in two-state contexts)
    envConstants :: Map Id Expression,  -- Constant names to expressions
    envFunctions :: Map Id FDef,        -- Function names to definitions
    envProcedures :: Map Id [PDef],     -- Procedure names to definitions
    envTypeContext :: TypeContext       -- Type context (see TypeChecker)
  }
   
emptyEnv = Environment
  {
    envLocals = M.empty,
    envGlobals = M.empty,
    envOld = M.empty,
    envConstants = M.empty,
    envFunctions = M.empty,
    envProcedures = M.empty,
    envTypeContext = TC.emptyContext
  }

setGlobal id val env = env { envGlobals = M.insert id val (envGlobals env) }    
setLocal id val env = env { envLocals = M.insert id val (envLocals env) }
addConstant id def env = env { envConstants = M.insert id def (envConstants env) }
addFunction id def env = env { envFunctions = M.insert id def (envFunctions env) }
addProcedure id def env = env { envProcedures = M.insert id (def : oldDefs) (envProcedures env) } 
  where
    oldDefs = case M.lookup id (envProcedures env) of
      Nothing -> []
      Just defs -> defs

-- | Pretty-printed mapping of variables to values
envDoc :: Map Id Value -> Doc
envDoc env = vsep $ map varDoc (M.toList env)
  where varDoc (id, val) = text id <+> text "=" <+> valueDoc val      

-- | Computations with Environment as state, which can result in either a or RuntimeError  
type Execution a = ErrorT RuntimeError (State Environment) a  
        
-- | Set value of variable id to val.
-- | id has to be declared in the current type context.
setV :: Id -> Value -> Execution ()    
setV id val = do
  tc <- gets envTypeContext
  if M.member id (TC.localScope tc)
    then modify $ setLocal id val
    else modify $ setGlobal id val      
    
-- | Set values of variables ids to vals.  
setAll :: [Id] -> [Value] -> Execution ()
setAll ids vals = zipWithM_ setV ids vals  

-- | Enter local scope (apply localTC to the type context, assign actuals to formals, save globals in the old state),
-- | execute computation,
-- | then restore type context, local variables and the old state to their initial values
executeLocally :: (TypeContext -> TypeContext) -> [Id] -> [Value] -> Execution a -> Execution a
executeLocally localTC formals actuals computation = do
  env <- get
  put env { envTypeContext = localTC (envTypeContext env), envOld = envGlobals env }
  setAll formals actuals
  res <- computation
  env' <- get
  put env' { envTypeContext = envTypeContext env, envLocals = envLocals env, envOld = envOld env }
  return res
  
{- Nondeterminism -}  
  
-- | Generate a value of type t,
-- | such that when it is set, guard does not fail.
-- | Fail if cannot find such a value.
-- | (So far just returns the default value, but will be more elaborate in the future)
generateValue :: Type -> (Value -> Execution ()) -> (Execution ()) -> Execution Value          
generateValue t set guard = let newValue = defaultValue t in
  do
    set newValue 
    guard
    return newValue  
  
{- Errors -}

data RuntimeErrorInfo = AssertViolation SpecType Expression | 
  AssumeViolation SpecType Expression |
  DivisionByZero |
  UnsupportedConstruct String |
  NoEntryPoint String |
  OtherError String

-- | Information about a procedure or function call  
data StackFrame = StackFrame {
  callPos :: SourcePos, -- Source code position of the call
  callName :: Id        -- Name of procedure or function
}

type StackTrace = [StackFrame]

data RuntimeError = RuntimeError {
  rteInfo :: RuntimeErrorInfo,  -- Type of error and additional information
  rtePos :: SourcePos,          -- Location where the error occurred
  rteTrace :: StackTrace        -- Stack trace from the program entry point to the procedure where the error occurred
}

-- | Throw a runtime error
throwRuntimeError info pos = throwError (RuntimeError info pos [])

-- | Push frame on the stack trace of a runtime error
addStackFrame frame (RuntimeError info pos trace) = throwError (RuntimeError info pos (frame : trace))

-- | Is err an assumptionviolation?
isAssumeViolation :: RuntimeError -> Bool
isAssumeViolation err = case rteInfo err of
  AssumeViolation _ _ -> True
  _ -> False
  
instance Error RuntimeError where
  noMsg    = RuntimeError (OtherError "Unknown error") noPos []
  strMsg s = RuntimeError (OtherError s) noPos []
  
runtimeErrorDoc err = errorInfoDoc (rteInfo err) <+> posDoc (rtePos err) $+$ vsep (map stackFrameDoc (reverse (rteTrace err)))
  where
  errorInfoDoc (AssertViolation specType e) = text (assertClauseName specType) <+> doubleQuotes (exprDoc e) <+> defPosition specType e <+> text "violated" 
  errorInfoDoc (AssumeViolation specType e) = text (assumeClauseName specType) <+> doubleQuotes (exprDoc e) <+> defPosition specType e <+> text "violated"
  errorInfoDoc (DivisionByZero) = text "Division by zero"
  errorInfoDoc (UnsupportedConstruct s) = text "Unsupported construct" <+> text s
  errorInfoDoc (NoEntryPoint name) = text "Cannot find program entry point:" <+> text name
  errorInfoDoc (OtherError s) = text "Unknown error type:" <+> text s
  
  assertClauseName Inline = "Assertion"  
  assertClauseName Precondition = "Precondition"  
  assertClauseName Postcondition = "Postcondition"
  assertClauseName LoopInvariant = "Loop invariant"  
  
  assumeClauseName Inline = "Assumption"  
  assumeClauseName Precondition = "Free precondition"  
  assumeClauseName Postcondition = "Free postcondition"
  assumeClauseName LoopInvariant = "Free loop invariant"
  assumeClauseName Where = "Where clause"
  
  defPosition Inline _ = empty
  defPosition _ e = text "defined" <+> posDoc (position e)
  
  stackFrameDoc f = text "in call to" <+> text (callName f) <+> posDoc (callPos f)
  posDoc pos = text "at" <+> text (sourceName pos) <+> text "line" <+> int (sourceLine pos)

instance Show RuntimeError where
  show err = show (runtimeErrorDoc err)

{- Expressions -}

-- | Semantics of unary operators
unOp :: UnOp -> Value -> Value
unOp Neg (IntValue n)   = IntValue (-n)
unOp Not (BoolValue b)  = BoolValue (not b)

-- | Semi-strict semantics of binary operators:
-- | binOpLazy op lhs: returns the value of "lhs `op`" if already defined, otherwise Nothing 
binOpLazy :: BinOp -> Value -> Maybe Value
binOpLazy And     (BoolValue False) = Just $ BoolValue False
binOpLazy Or      (BoolValue True)  = Just $ BoolValue True
binOpLazy Implies (BoolValue False) = Just $ BoolValue True
binOpLazy _ _                       = Nothing

-- | Strict semantics of binary operators
binOp :: SourcePos -> BinOp -> Value -> Value -> Execution Value 
binOp pos Plus    (IntValue n1) (IntValue n2)   = return $ IntValue (n1 + n2)
binOp pos Minus   (IntValue n1) (IntValue n2)   = return $ IntValue (n1 - n2)
binOp pos Times   (IntValue n1) (IntValue n2)   = return $ IntValue (n1 * n2)
binOp pos Div     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                then throwRuntimeError DivisionByZero pos
                                                else return $ IntValue (n1 `div` n2)
binOp pos Mod     (IntValue n1) (IntValue n2)   = if n2 == 0 
                                                then throwRuntimeError DivisionByZero pos
                                                else return (IntValue (n1 `mod` n2))
binOp pos Leq     (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 <= n2)
binOp pos Ls      (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 < n2)
binOp pos Geq     (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 >= n2)
binOp pos Gt      (IntValue n1) (IntValue n2)   = return $ BoolValue (n1 > n2)
binOp pos And     (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 && b2)
binOp pos Or      (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 || b2)
binOp pos Implies (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 <= b2)
binOp pos Equiv   (BoolValue b1) (BoolValue b2) = return $ BoolValue (b1 == b2)
binOp pos Eq      v1 v2                         = return $ BoolValue (v1 == v2)
binOp pos Neq     v1 v2                         = return $ BoolValue (v1 /= v2)
binOp pos Lc      v1 v2                         = throwRuntimeError (UnsupportedConstruct "orders") pos

-- | Evaluate an expression;
-- | can have a side-effect of initializing variables that were not previously defined
eval :: Expression -> Execution Value
eval e = case contents e of
  TT -> return $ BoolValue True
  FF -> return $ BoolValue False
  Numeral n -> return $ IntValue n
  Var id -> evalVar id (position e)
  Application id args -> evalApplication id args (position e)
  MapSelection m args -> evalMapSelection m args (position e)
  MapUpdate m args new -> evalMapUpdate m args new
  Old e -> evalOld e
  UnaryExpression op e -> unOp op <$> eval e
  BinaryExpression op e1 e2 -> evalBinary op e1 e2
  Quantified op args vars e -> throwRuntimeError (UnsupportedConstruct "quantified expressions") (position e)
  
evalVar id pos = do
  tc <- gets envTypeContext
  case M.lookup id (TC.localScope tc) of
    Just t -> lookup envLocals setLocal t
    Nothing -> case M.lookup id (TC.ctxGlobals tc) of
      Just t -> lookup envGlobals setGlobal t
      Nothing -> case M.lookup id (TC.ctxConstants tc) of
        Just t -> do
          constants <- gets envConstants
          case M.lookup id constants of
            Just e -> eval e
            Nothing -> return $ defaultValue t -- ToDo: cache constant value?
  where
    lookup getter setter t = do
      vars <- gets getter
      case M.lookup id vars of
        Just val -> return val
        Nothing -> generateValue t (modify . setter id) (checkWhere id pos)
  
evalApplication name args pos = do
  functions <- gets envFunctions
  tc <- gets envTypeContext
  case M.lookup name functions of
    Nothing -> return $ defaultValue (returnType tc)
    Just (FDef formals body) -> do
      argsV <- mapM eval args
      catchError (evalBody formals argsV body) (addStackFrame frame)
  where
    evalBody formals actuals body = executeLocally (TC.enterFunction name formals args) formals actuals (eval body)
    returnType tc = fromRight $ TC.checkExpression tc (gen $ Application name args)
    frame = StackFrame pos name
    
evalMapSelection m args pos = do 
  tc <- gets envTypeContext
  mV <- eval m
  argsV <- mapM eval args
  case mV of 
    MapValue map -> case M.lookup argsV map of
      Nothing -> case mapVariable tc (contents m) of
        Nothing -> return $ defaultValue (rangeType tc) -- The underlying map comes from a constant or function, nothing to check
        Just v -> generateValue (rangeType tc) (\_ -> return ()) (checkWhere v pos) -- The underlying map comes from a variable: check the where clause
        -- Decided not to cache map access so far, because it leads to strange effects when the map is passed as an argument and can take a lot of memory 
        -- Just v -> generateValue (rangeType tc) (cache v map argsV) (checkWhere v pos) -- The underlying map comes from a variable: check the where clause and cache the value
      Just v -> return v
  where
    rangeType tc = fromRight $ TC.checkExpression tc (gen $ MapSelection m args)
    mapVariable tc (Var v) = if M.member v (TC.allVars tc)
      then Just v
      else Nothing
    mapVariable tc (MapUpdate m _ _) = mapVariable tc (contents m)
    mapVariable tc _ = Nothing 
    -- cache m map args val = setV m (MapValue (M.insert args val map))
    
evalMapUpdate m args new = do
  mV <- eval m
  argsV <- mapM eval args
  newV <- eval new
  case mV of 
    MapValue map -> return $ MapValue (M.insert argsV newV map)
    
evalOld e = do
  env <- get
  put env { envGlobals = envOld env }
  res <- eval e
  put env
  return res
  
evalBinary op e1 e2 = do
  left <- eval e1
  case binOpLazy op left of
    Just result -> return result
    Nothing -> do
      right <- eval e2
      binOp (position e1) op left right
  
{- Statements -}

-- | Execute a simple statement
exec :: Statement -> Execution ()
exec stmt = case contents stmt of
  Assert specType e -> execAssert specType e (position stmt)
  Assume specType e -> execAssume specType e (position stmt)
  Havoc ids -> execHavoc ids (position stmt)
  Assign lhss rhss -> execAssign lhss rhss
  Call lhss name args -> execCall lhss name args (position stmt)
  CallForall name args -> return () -- ToDo: assume (forall args :: pre ==> post)?

execAssert specType e pos = do
  b <- eval e
  case b of 
    BoolValue True -> return ()
    BoolValue False -> throwRuntimeError (AssertViolation specType e) pos
    
execAssume specType e pos = do
  b <- eval e
  case b of 
    BoolValue True -> return ()
    BoolValue False -> throwRuntimeError (AssumeViolation specType e) pos
    
execHavoc ids pos = do
  tc <- gets envTypeContext
  mapM_ (havoc tc) ids 
  where
    havoc tc id = generateValue (fromRight . TC.checkExpression tc . gen . Var $ id) (setV id) (checkWhere id pos) 
    
execAssign lhss rhss = do
  rVals <- mapM eval rhss'
  setAll lhss' rVals
  where
    lhss' = map fst (zipWith normalize lhss rhss)
    rhss' = map snd (zipWith normalize lhss rhss)
    normalize (id, []) rhs = (id, rhs)
    normalize (id, argss) rhs = (id, mapUpdate (gen $ Var id) argss rhs)
    mapUpdate e [args] rhs = gen $ MapUpdate e args rhs
    mapUpdate e (args1 : argss) rhs = gen $ MapUpdate e args1 (mapUpdate (gen $ MapSelection e args1) argss rhs)
    
execCall lhss name args pos = do
  tc <- gets envTypeContext
  procedures <- gets envProcedures
  case M.lookup name procedures of
    Nothing -> execHavoc lhss pos
    Just (def : defs) -> do
      retsV <- catchError (execProcedure name def args) (addStackFrame frame)
      setAll lhss retsV
  where
    frame = StackFrame pos name
    
-- | Execute program consisting of blocks starting from the block labeled label.
-- | Return the location of the exit point.
execBlock :: Map Id [Statement] -> Id -> Execution SourcePos
execBlock blocks label = let
  block = blocks ! label
  statements = init block
  in do
    mapM exec statements
    case last block of
      Pos pos Return -> return pos
      Pos _ (Goto lbs) -> tryOneOf blocks lbs
  
-- | tryOneOf blocks labels: try executing blocks starting with each of labels,
-- | until we find one that does not result in an assumption violation      
tryOneOf :: Map Id [Statement] -> [Id] -> Execution SourcePos        
tryOneOf blocks (l : lbs) = catchError (execBlock blocks l) retry
  where
    retry e 
      | isAssumeViolation e && not (null lbs) = tryOneOf blocks lbs
      | otherwise = throwError e
  
-- | Execute definition def of procedure name with actual arguments actuals 
execProcedure :: Id -> PDef -> [Expression] -> Execution [Value]
execProcedure name def args = let 
  ins = pdefIns def
  outs = pdefOuts def
  blocks = snd (pdefBody def)
  exitPoint pos = if pos == noPos 
    then pdefPos def  -- Fall off the procedure body: take the procedure definition location
    else pos          -- A return statement inside the body
  execBody = do
    checkPreconditions name def
    pos <- exitPoint <$> execBlock blocks startLabel
    checkPostonditions name def pos
    mapM (eval . attachPos (pdefPos def) . Var) outs
  in do
    tc <- gets envTypeContext
    argsV <- mapM eval args
    executeLocally (TC.enterProcedure name def args) ins argsV execBody
    
{- Specs -}

-- | Assert preconditions of definition def of procedure name
checkPreconditions name def = do
  s <- TC.procSig name <$> gets envTypeContext
  mapM_ (exec . attachPos (pdefPos def) . check . subst s) (psigRequires s)
  where 
    subst s (SpecClause t f e) = SpecClause t f (paramSubst s def e)

-- | Assert postconditions of definition def of procedure name at exitPoint    
checkPostonditions name def exitPoint = do
  s <- TC.procSig name <$> gets envTypeContext
  mapM_ (exec . attachPos exitPoint . check . subst s) (psigEnsures s)
  where 
    subst s (SpecClause t f e) = SpecClause t f (paramSubst s def e)

-- | Assume where clause of variable at a program location pos
-- | (pos will be reported as the location of the error instead of the location of the variable definition).
checkWhere id pos = do
  whereClauses <- TC.ctxWhere <$> gets envTypeContext
  case M.lookup id whereClauses of
    Nothing -> return ()
    Just w -> (exec . attachPos pos . Assume Where) w

{- Preprocessing -}

-- | Collect constant, function and procedure definitions from p
collectDefinitions :: Program -> Execution ()
collectDefinitions p = mapM_ processDecl p
  where
    processDecl (Pos _ (FunctionDecl name _ args _ (Just body))) = processFunctionBody name args body
    processDecl (Pos pos (ProcedureDecl name _ args rets _ (Just body))) = processProcedureBody name pos (map noWhere args) (map noWhere rets) body
    processDecl (Pos pos (ImplementationDecl name _ args rets bodies)) = mapM_ (processProcedureBody name pos args rets) bodies
    processDecl (Pos _ (AxiomDecl expr)) = processAxiom expr
    processDecl _ = return ()
  
processFunctionBody name args body = modify $ addFunction name (FDef (map (formalName . fst) args) body) 
  where
    formalName Nothing = dummyFArg 
    formalName (Just n) = n

processProcedureBody name pos args rets body = do
  sig <- TC.procSig name <$> gets envTypeContext
  modify $ addProcedure name (PDef argNames retNames (paramsRenamed sig) (flatten body) pos) 
  where
    argNames = map fst args
    retNames = map fst rets
    flatten (locals, statements) = (concat locals, M.fromList (toBasicBlocks statements))
    paramsRenamed sig = map itwId (psigArgs sig ++ psigRets sig) /= (argNames ++ retNames)     
      
processAxiom expr = case contents expr of
  -- c == expr: remember expr as a definition for c
  BinaryExpression Eq (Pos _ (Var c)) rhs -> modify $ addConstant c rhs
  -- ToDo: add axioms that (partially) define functions
  _ -> return ()
