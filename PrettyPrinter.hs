{- Pretty printer for Boogie 2 -}
module PrettyPrinter where

import AST
import Position
import Tokens
import Data.Maybe
import Data.Map (Map, (!))
import qualified Data.Map as M
import Text.PrettyPrint
  
{- Interface -}

-- | Pretty-printed program
programDoc :: [Decl] -> Doc
programDoc decls = (vsep . punctuate newline . map declDoc) decls

-- | Render document with tabs instead of spaces
renderWithTabs = fullRender (mode style) (lineLength style) (ribbonsPerLine style) spacesToTabs ""
  where
    spacesToTabs :: TextDetails -> String -> String
    spacesToTabs (Chr c) s  = c:s
    spacesToTabs (Str s1) s2 = if s1 == replicate (length s1) ' ' && length s1 > 1 
      then replicate (length s1 `div` defaultIndent) '\t' ++ s2 
      else s1 ++ s2
      
{- Tokens -}

unOpDoc op = text (token op unOpTokens)
binOpDoc op = text (token op binOpTokens)
qOpDoc op = text (token op qOpTokens)

{- Types -}

typeDoc :: Type -> Doc
typeDoc BoolType = text "bool"
typeDoc IntType = text "int"
typeDoc (MapType fv domains range) = typeArgsDoc fv <> 
  brackets (commaSep (map typeDoc domains)) <+>
  typeDoc range
typeDoc (Instance id args) = text id <+> hsep (map typeDoc args)

{- Expressions -}

-- | Binding power of an expression
power :: BareExpression -> Int
power TT = 9
power FF = 9
power (Numeral _) = 9
power (Var _) = 9
power (Application _ _) = 9
power (Old _) = 9
power (Quantified _ _ _ _) = 9
power (MapSelection _ _) = 8
power (MapUpdate _ _ _) = 8
power (UnaryExpression _ _) = 7
power (BinaryExpression op _ _) 
  | op `elem` [Times, Div, Mod] = 6 
  | op `elem` [Plus, Minus] = 5
-- | op `elem` [Concat] = 4
  | op `elem` [Eq, Neq, Ls, Leq, Gt, Geq, Lc] = 3
  | op `elem` [And, Or] = 2
  | op `elem` [Implies] = 1
  | op `elem` [Equiv] = 0

exprDoc :: Expression -> Doc
exprDoc e = exprDocAt (-1) e

-- | exprDocAt expr: print expr in a context with binding power n
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
    UnaryExpression unOp e -> unOpDoc unOp <> exprDocAt n' e
    BinaryExpression binOp e1 e2 -> exprDocAt n' e1 <+> binOpDoc binOp <+> exprDocAt n' e2
    Quantified qOp fv vars e -> parens (qOpDoc qOp <+> typeArgsDoc fv <+> commaSep (map idTypeDoc vars) <+> text "::" <+> exprDoc e)
  )
  where
    n' = power e

{- Statements -}

statementDoc :: Statement -> Doc
statementDoc (Pos _ s) = case s of
  Assert _ e -> text "assert" <+> exprDoc e <> semi
  Assume _ e -> text "assume" <+> exprDoc e <> semi
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

declDoc :: Decl -> Doc
declDoc (Pos pos d) = case d of
  TypeDecl ts -> typeDeclDoc ts
  ConstantDecl unique names t orderSpec complete -> constantDoc unique names t orderSpec complete
  FunctionDecl name fv args ret mb -> functionDoc name fv args ret mb
  AxiomDecl e -> text "axiom" <+> exprDoc e <> semi
  VarDecl vars -> varDeclDoc vars
  ProcedureDecl name fv args rets specs mb -> procedureDoc name fv args rets specs mb
  ImplementationDecl name fv args rets bodies -> implementationDoc name fv args rets bodies
  
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

newline = char '\n'
vsep = foldr ($+$) empty
commaSep = hsep . punctuate comma
angles d = langle <> d <> rangle
  where
    langle = char '<'
    rangle = char '>'
spaces d = space <> d <> space

option b doc = if b then doc else empty

optionMaybe mVal toDoc = case mVal of
  Nothing -> empty
  Just val -> toDoc val
  
condParens b doc = if b then parens doc else doc
    
typeArgsDoc fv = option (not (null fv)) (angles (commaSep (map text fv)))

idTypeDoc (id, t) = text id <> text ":" <+> typeDoc t

idTypeWhereDoc (IdTypeWhere id t w) = idTypeDoc (id, t) <+> case w of
  (Pos _ TT) -> empty
  e -> text "where" <+> exprDoc e  