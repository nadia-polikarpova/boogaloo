-- | Pretty printer for Boogie 2
module Language.Boogie.PrettyPrinter (
  -- * Pretty-printing programs
  programDoc,
  renderWithTabs,
  typeDoc,
  exprDoc,
  statementDoc,
  declDoc,
  -- * Utility
  newline,
  vsep,
  commaSep,
  angles,
  spaces,  
  option,
  optionMaybe,
  unOpDoc,
  binOpDoc,
  sigDoc
) where

import Language.Boogie.AST
import Language.Boogie.Position
import Language.Boogie.Tokens
import Data.Maybe
import Data.Map (Map, (!))
import qualified Data.Map as M
import Text.PrettyPrint
  
{- Interface -}

-- | Pretty-printed program
programDoc :: Program -> Doc
programDoc (Program decls) = (vsep . punctuate newline . map declDoc) decls

instance Show Program where show p = show (programDoc p)

-- | Render document with tabs instead of spaces
renderWithTabs = fullRender (mode style) (lineLength style) (ribbonsPerLine style) spacesToTabs ""
  where
    spacesToTabs :: TextDetails -> String -> String
    spacesToTabs (Chr c) s  = c:s
    spacesToTabs (Str s1) s2 = if s1 == replicate (length s1) ' ' && length s1 > 1 
      then replicate (length s1 `div` defaultIndent) '\t' ++ s2 
      else s1 ++ s2
      
{- Tokens -}

-- | Pretty-printed unary operator
unOpDoc op = text (opName op unOpTokens)
-- | Pretty-printed binary operator
binOpDoc op = text (opName op binOpTokens)
-- | Pretty-printed quantifier
qOpDoc op = text (opName op qOpTokens)

{- Types -}

-- | Pretty-printed type
typeDoc :: Type -> Doc
typeDoc BoolType = text "bool"
typeDoc IntType = text "int"
typeDoc (MapType fv domains range) = typeArgsDoc fv <> 
  brackets (commaSep (map typeDoc domains)) <+>
  typeDoc range
typeDoc (IdType id args) = text id <+> hsep (map typeDoc args)

instance Show Type where show t = show (typeDoc t)

-- | Pretty-printed function or procedure signature
sigDoc :: [Type] -> [Type] -> Doc
sigDoc argTypes retTypes = parens(commaSep (map typeDoc argTypes)) <+> 
  text "returns" <+> 
  parens(commaSep (map typeDoc retTypes))
  
{- Expressions -}

-- | Binding power of an expression
power :: BareExpression -> Int
power TT = 10
power FF = 10
power (Numeral _) = 10
power (Var _) = 10
power (Application _ _) = 10
power (Old _) = 10
power (IfExpr _ _ _) = 10
power (Quantified _ _ _ _) = 10
power (MapSelection _ _) = 9
power (MapUpdate _ _ _) = 9
power (Coercion _ _) = 8
power (UnaryExpression _ _) = 7
power (BinaryExpression op _ _) 
  | op `elem` [Times, Div, Mod] = 6 
  | op `elem` [Plus, Minus] = 5
  | op `elem` [Eq, Neq, Ls, Leq, Gt, Geq, Lc] = 3
  | op `elem` [And, Or] = 2
  | op `elem` [Implies, Explies] = 1
  | op `elem` [Equiv] = 0

-- | Pretty-printed expression  
exprDoc :: Expression -> Doc
exprDoc e = exprDocAt (-1) e

-- | 'exprDocAt' @n expr@ : print @expr@ in a context with binding power @n@
exprDocAt :: Int -> Expression -> Doc
exprDocAt n (Pos _ e) = condParens (n' <= n) (
  case e of
    FF -> text "false"
    TT -> text "true"
    Numeral n -> integer n
    Var id -> text id
    Application id args -> text id <> parens (commaSep (map exprDoc args))
    MapSelection m args -> exprDocAt n' m <> brackets (commaSep (map exprDoc args))
    MapUpdate m args val -> exprDocAt n' m <> brackets (commaSep (map exprDoc args) <+> text ":=" <+> exprDoc val)
    Old e -> text "old" <+> parens (exprDoc e)
    IfExpr cond e1 e2 -> text "if" <+> exprDoc cond <+> text "then" <+> exprDoc e1 <+> text "else" <+> exprDoc e2
    Coercion e t -> exprDocAt n' e <+> text ":" <+> typeDoc t
    UnaryExpression unOp e -> unOpDoc unOp <> exprDocAt n' e
    BinaryExpression binOp e1 e2 -> exprDocAt n' e1 <+> binOpDoc binOp <+> exprDocAt n' e2
    Quantified qOp fv vars e -> parens (qOpDoc qOp <+> typeArgsDoc fv <+> commaSep (map idTypeDoc vars) <+> text "::" <+> exprDoc e)
  )
  where
    n' = power e
    
instance Show BareExpression where show e = show (exprDoc (gen e))      

{- Statements -}

-- | Pretty-printed statement
statementDoc :: Statement -> Doc
statementDoc (Pos _ s) = case s of
  Predicate (SpecClause _ isAssume e) -> (if isAssume then text "assume" else text "assert") <+> exprDoc e <> semi
  Havoc vars -> text "havoc" <+> commaSep (map text vars) <> semi
  Assign lhss rhss -> commaSep (map lhsDoc lhss) <+> 
    text ":=" <+> commaSep (map exprDoc rhss) <> semi
  Call lhss name args -> text "call" <+>
    commaSep (map text lhss) <+>
    option (not (null lhss)) (text ":=") <+> 
    text name <> 
    parens (commaSep (map exprDoc args)) <> 
    semi
  CallForall name args -> text "call forall" <+> 
    text name <> 
    parens (commaSep (map wildcardDoc args)) <> 
    semi
  If cond thenBlock elseBlock -> text "if" <+> parens (wildcardDoc cond) <+> 
    bracedBlockDoc thenBlock <+>
    optionMaybe elseBlock elseDoc
  While cond invs b -> text "while" <+> parens (wildcardDoc cond) $+$
    nestDef (vsep (map specClauseDoc invs)) $+$
    bracedBlockDoc b
  Break ml -> text "break" <+> optionMaybe ml text <> semi
  Return -> text "return" <> semi
  Goto ids -> text "goto" <+> commaSep (map text ids) <> semi
  Skip -> empty
  where
    lhsDoc (id, selects) = text id <> hcat (map (\sel -> brackets (commaSep (map exprDoc sel))) selects)
    wildcardDoc Wildcard = text "*"
    wildcardDoc (Expr e) = exprDoc e
    elseDoc b = text "else" <+> bracedBlockDoc b
    
instance Show BareStatement where show s = show (statementDoc (gen s))   

{- Blocks -}

blockDoc block = vsep (map lStatementDoc block)
  where
    lStatementDoc (Pos _ (lbs, s)) = hsep (map labelDoc lbs) <+> statementDoc s
    
bracedBlockDoc block = 
  lbrace $+$
  nestDef (blockDoc block) $+$
  rbrace
    
bodyDoc (vars, block) =
  lbrace $+$
  nestDef (vsep (map varDeclDoc vars) $+$ blockDoc block) $+$
  rbrace
  
transformedBlockDoc block = vsep (map basicBlockDoc block)
  where
    basicBlockDoc (l, stmts) = labelDoc l $+$ 
      nestDef (vsep (map statementDoc stmts))

labelDoc l = text l <> text ":"

{- Specs -}     

specTypeDoc Precondition = text "precondition"
specTypeDoc Postcondition = text "postcondition"
specTypeDoc LoopInvariant = text "invariant"

specClauseDoc (SpecClause t free e) = option free (text "free") <+> specTypeDoc t <+> exprDoc e <> semi

{- Declarations -}

-- | Pretty-printed top-level declaration
declDoc :: Decl -> Doc
declDoc (Pos pos d) = case d of
  TypeDecl ts -> typeDeclDoc ts
  ConstantDecl unique names t orderSpec complete -> constantDoc unique names t orderSpec complete
  FunctionDecl name fv args ret mb -> functionDoc name fv args ret mb
  AxiomDecl e -> text "axiom" <+> exprDoc e <> semi
  VarDecl vars -> varDeclDoc vars
  ProcedureDecl name fv args rets specs mb -> procedureDoc name fv args rets specs mb
  ImplementationDecl name fv args rets bodies -> implementationDoc name fv args rets bodies
  
instance Show BareDecl where show d = show (declDoc (gen d))  
  
typeDeclDoc ts = 
  text "type" <+> 
  commaSep (map newTypeDoc ts) <> 
  semi
  where
    newTypeDoc (NewType id args mVal) = text id <+> hsep (map text args) <+> optionMaybe mVal (\t -> text "=" <+> typeDoc t)
    
constantDoc unique names t orderSpec complete =
  text "const" <+>
  option unique (text "unique") <+>
  commaSep (map text names) <>
  text ":" <+> typeDoc t <+>
  optionMaybe orderSpec orderSpecDoc <+>
  option complete (text "complete") <> 
  semi
  where
    orderSpecDoc parents = text "extends" <+> commaSep (map parentDoc parents)
    parentDoc (u, id) = option u (text "unique") <+> text id
    
functionDoc name fv args ret mb =
  text "function" <+>
  text name <>
  typeArgsDoc fv <>
  parens (commaSep (map fArgDoc args)) <+>
  text "returns" <+>
  parens (fArgDoc ret) <>
  option (isNothing mb) semi $+$
  optionMaybe mb (braces . spaces . exprDoc)
  where
    fArgDoc (Nothing, t) = typeDoc t
    fArgDoc (Just id, t) = idTypeDoc (id, t) 
    
varDeclDoc vars =
  text "var" <+>
  commaSep (map idTypeWhereDoc vars) <>
  semi
      
procedureDoc name fv args rets specs mb =
  text "procedure" <+>
  text name <>
  typeArgsDoc fv <>
  parens (commaSep (map idTypeWhereDoc args)) <+>
  text "returns" <+>
  parens (commaSep (map idTypeWhereDoc rets)) <>
  option (isNothing mb) semi $+$
  nestDef (vsep (map specDoc specs)) $+$
  optionMaybe mb bodyDoc
  where
    specDoc (Requires free e) = option free (text "free") <+>
      text "requires" <+>
      exprDoc e <>
      semi
    specDoc (Ensures free e) = option free (text "free") <+>
      text "ensures" <+>
      exprDoc e <>
      semi
    specDoc (Modifies free ids) = option free (text "free") <+>
      text "modifies" <+>
      commaSep (map text ids) <>
      semi
    
implementationDoc name fv args rets bodies =
  text "implementation" <+>
  text name <>
  typeArgsDoc fv <>
  parens (commaSep (map idTypeDoc args)) <+>
  text "returns" <+>
  parens (commaSep (map idTypeDoc rets)) $+$
  vsep (map bodyDoc bodies)
  
{- Misc -}
  
defaultIndent = 4
nestDef = nest defaultIndent

-- | New line
newline = char '\n'
-- | Separate by new lines
vsep = foldr ($+$) empty
-- | Separate by commas
commaSep = hsep . punctuate comma
-- | Enclose in \< \>
angles d = langle <> d <> rangle
  where
    langle = char '<'
    rangle = char '>'
-- | Enclose in spaces    
spaces d = space <> d <> space

-- | Conditionally produce a doc
option b doc = if b then doc else empty

-- | Convert a 'Just' value to doc
optionMaybe mVal toDoc = case mVal of
  Nothing -> empty
  Just val -> toDoc val
  
-- | Conditionally enclose in parentheses  
condParens b doc = if b then parens doc else doc
    
-- | Pretty-printed type arguments     
typeArgsDoc tv = option (not (null tv)) (angles (commaSep (map text tv)))

-- | Pretty-printed name declaration
idTypeDoc (id, t) = text id <> text ":" <+> typeDoc t

-- | Pretty-printed name declaration with a where clause
idTypeWhereDoc (IdTypeWhere id t w) = idTypeDoc (id, t) <+> case w of
  (Pos _ TT) -> empty
  e -> text "where" <+> exprDoc e
  
instance Eq Doc where
  d1 == d2 = show d1 == show d2
  
  