module Parser where

import AST
import Tokens
import Data.List
import Text.ParserCombinators.Parsec hiding (token)
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Expr

{- Lexical analysis -}

opNames :: [String]
opNames = map snd unOpTokens ++ map snd binOpTokens ++ otherOps

opStart :: [Char]
opStart = nub (map head opNames)

opLetter :: [Char]
opLetter = nub (concat (map tail opNames))

boogieDef :: P.LanguageDef st
boogieDef = P.LanguageDef 
	commentStart
	commentEnd
	commentLine
	False
	(letter <|> oneOf identifierChars)
	(alphaNum <|> oneOf identifierChars)
	(oneOf opStart)
	(oneOf opLetter)
	keywords
	opNames
	True
	
lexer :: P.TokenParser ()
lexer = P.makeTokenParser boogieDef    
      
identifier = P.identifier lexer
reserved = P.reserved lexer
reservedOp = P.reservedOp lexer
charLiteral = P.charLiteral lexer
stringLiteral = P.stringLiteral lexer
natural = P.natural lexer
integer = P.integer lexer
symbol = P.symbol lexer
whiteSpace = P.whiteSpace lexer
angles = P.angles lexer
brackets = P.brackets lexer
parens = P.parens lexer
braces = P.braces lexer
semi = P.semi lexer
comma = P.comma lexer
commaSep = P.commaSep lexer
commaSep1 = P.commaSep1 lexer

{- Types -}

typeAtom :: Parser Type
typeAtom = do { reserved "int"; return IntType } <|>
		   do { reserved "bool"; return BoolType } <|>
		   -- bit vector
		   parens type_
		   
typeArgs :: Parser [Id]
typeArgs = try (angles (commaSep1 identifier)) <|> return []
		   
mapType :: Parser Type
mapType = do { 
	args <- typeArgs; 
	domains <- brackets (commaSep1 type_); 
	range <- type_; 
	return (MapType args domains range) 
	}
	
typeCtorArgs :: Parser [Type]
typeCtorArgs = do { x <- typeAtom; xs <- option [] typeCtorArgs; return (x : xs) } <|>
               do { x <- identifier; xs <- option [] typeCtorArgs; return ((Instance x []) : xs) } <|>
			   do { x <- mapType; return [x] }

type_ :: Parser Type
type_ = typeAtom <|> mapType <|>
	do { id <- identifier; args <- option [] typeCtorArgs; return (Instance id args) }
	<?> "type"

{- Expressions -}

qop :: Parser QOp
qop = (do { reserved "forall"; return Forall }) <|> (do { reserved "exists"; return Exists })
	
e9 :: Parser Expression
e9 = do { reserved "false"; return FF } <|>
     do { reserved "true"; return TT } <|> 
	 do { n <- natural; return (Numeral n) } <|> 
	 -- str bitVector <|>
	 do { id <- identifier; ( do { args <- parens (commaSep e0); return (Application id args) }) <|> return (Var id) } <|>
	 do { reserved "old"; e <- parens e0; return (Old  e) } <|>
	 try (parens e0) <|>
	 parens (do { 
		op <- qop; 
		args <- typeArgs; 
		vars <- commaSep1 idsType; 
		reservedOp "::"; 
		many trigAttr; 
		e <- e0; 
		return (Quantified op args (ungroup vars) e )})

e8 :: Parser Expression
e8 = do { e <- e9; mapOps <- many (brackets (mapOp)); return (foldr (.) id (reverse mapOps) e) }

mapOp :: Parser (Expression -> Expression)
mapOp = do { args <- commaSep1 e0; option ((flip MapSelection) args) (do { reservedOp ":="; e <- e0; return (flip ((flip MapUpdate) args) e)}) }

e0 :: Parser Expression	
e0 = buildExpressionParser table e8 <?> "expression"

table = [[unOp Neg, unOp Not],
         [binOp Times AssocLeft, binOp Div AssocLeft, binOp Mod AssocLeft],
		 [binOp Plus AssocLeft, binOp Minus AssocLeft],
		 --[binOp Concat AssocLeft],
		 [binOp Eq AssocNone, binOp Neq AssocNone, binOp Ls AssocNone, binOp Leq AssocNone, binOp Gt AssocNone, binOp Geq AssocNone, binOp Lc AssocNone],
		 [binOp And AssocLeft], -- ToDo: && and || on the same level but do not interassociate
		 [binOp Or AssocLeft],
		 [binOp Implies AssocRight],
		 [binOp Equiv AssocRight]]
	where
		binOp node assoc = Infix (do { reservedOp (token node binOpTokens); return (\e1 e2 -> (BinaryExpression node e1 e2)) }) assoc
		unOp node = Prefix (do { reservedOp (token node unOpTokens); return (\e -> UnaryExpression node e)})
		
wildcardExpression :: Parser WildcardExpression
wildcardExpression = (do { e <- e0; return (Expr e) }) <|> (do { reservedOp "*"; return Wildcard })
		
{- Statements -}

lhs :: Parser (Id, [[Expression]])
lhs = do { id <- identifier; selects <- many (brackets (commaSep1 e0)); return (id, selects) }

assign :: Parser Statement
assign = do { lefts <- commaSep1 lhs; 
	reservedOp ":="; 
	rights <- commaSep1 e0; 
	semi; 
	return (Assign lefts rights) 
	}
	
call :: Parser Statement	
call = do { reserved "call"; 
	lefts <- option [] (try (do { ids <- commaSep1 identifier; reservedOp ":="; return ids }));
	id <- identifier;
	args <- parens (commaSep e0);
	semi;
	return (Call lefts id args)
	}
	
callForall :: Parser Statement	
callForall = do { reserved "call";
	reserved "forall";
	id <- identifier;
	args <- parens (commaSep wildcardExpression);
	semi;
	return (CallForall id args)
	}
	
ifStatement :: Parser Statement
ifStatement = do { reserved "if";
	cond <- parens wildcardExpression;
	thenBlock <- block;
	elseBlock <- optionMaybe (do { reserved "else"; 
		block <|> do { i <- ifStatement; return (singletonBlock i) }
		});
	return (If cond thenBlock elseBlock)
	}
	
loopInvariant :: Parser (Bool, Expression)
loopInvariant = do { free <- hasKeyword "free";
	reserved "invariant";
	e <- e0;
	semi;
	return (free, e)
	}
	
whileStatement :: Parser Statement
whileStatement = do { reserved "while";
	cond <- parens wildcardExpression;
	invs <- many loopInvariant;
	body <- block;
	return (While cond invs body)
	}	

statement :: Parser Statement
statement = do { reserved "assert"; e <- e0; semi; return (Assert e) } <|>
	do { reserved "assume"; e <- e0; semi; return (Assume e) } <|>
	do { reserved "havoc"; ids <- commaSep1 identifier; semi; return (Havoc ids) } <|>
	assign <|>
	try call <|>
	callForall <|>
	ifStatement <|>
	whileStatement <|>
	do { reserved "break"; id <- optionMaybe identifier; semi; return (Break id) } <|>
	do { reserved "return"; semi; return Return } <|>
	do { reserved "goto"; ids <- commaSep1 identifier; semi; return (Goto ids) }
	<?> "statement"
	
label :: Parser Id
label = do { id <- identifier; reservedOp ":"; return id } <?> "label"
	
lStatement :: Parser LStatement
lStatement = do { lbs <- many (try Parser.label); s <- statement; return (lbs, s) }

statementList :: Parser Block
statementList = do { lstatements <- many (try lStatement); 
	lempty <- many (try Parser.label); 
	return (if null lempty then lstatements else lstatements ++ [(lempty, Skip)]) 
	}

block :: Parser Block
block = braces statementList
		
{- Declarations -}

typeDecl :: Parser Decl
typeDecl = do { reserved "type";
	many attribute;
	finite <- hasKeyword "finite";
	name <- identifier;
	args <- many identifier;
	value <- (optionMaybe (do { reservedOp "="; type_ }));
	semi;
	return (TypeDecl finite name args value)
	}

parentEdge :: Parser ParentEdge
parentEdge = do { unique <- hasKeyword "unique"; id <- identifier; return (unique, id) }

constantDecl :: Parser Decl
constantDecl = do { reserved "const";
	many attribute;
	unique <- hasKeyword "unique";
	ids <- idsType;
	orderSpec <- optionMaybe (do { symbol "<:"; commaSep parentEdge });
	complete <- hasKeyword "complete";
	semi;
	return (ConstantDecl unique (fst ids) (snd ids) orderSpec complete)
	}
	
fArg :: Parser FArg
fArg = do { name <- optionMaybe (try (do { id <- identifier; reservedOp ":"; return id })); t <- type_; return (name, t)}
	
functionDecl :: Parser Decl
functionDecl = do { reserved "function";
	many attribute;
	name <- identifier;
	args <- parens (commaSep fArg);
	reserved "returns";
	ret <- parens fArg;
	body <- do { semi; return Nothing } <|> do { e <- (braces e0); return (Just e) };
	return (FunctionDecl name args ret body)
	}

axiomDecl :: Parser Decl
axiomDecl = do { reserved "axiom"; 
	many attribute; 
	e <- e0; 
	semi; 
	return (AxiomDecl e) 
	}

varList :: Parser [IdTypeWhere]
varList = do { reserved "var"; 
	many attribute; 
	vars <- commaSep1 idsTypeWhere; 
	semi; 
	return (ungroupWhere vars) 
	}	
	
varDecl :: Parser Decl
varDecl = do { vars <- varList; return (VarDecl vars) }
		
body :: Parser Body
body = braces (do { locals <- many varList; 
	statements <- statementList; 
	return (concat locals, statements)
	})
	
procDecl :: Parser Decl
procDecl = do { reserved "procedure";
	many attribute;
	name <- identifier;
	tArgs <- typeArgs;
	args <- parens (commaSep idsTypeWhere);
	rets <- option [] (do { reserved "returns"; parens (commaSep idsTypeWhere) });
	do { semi; specs <- many spec; return (ProcedureDecl name tArgs (ungroupWhere args) (ungroupWhere rets) specs Nothing) } <|>
	do { specs <- many spec; b <- body; return (ProcedureDecl name tArgs (ungroupWhere args) (ungroupWhere rets) specs (Just b)) }
	}

implDecl :: Parser Decl
implDecl = do { reserved "implementation";
	many attribute;
	name <- identifier;
	tArgs <- typeArgs;
	args <- parens (commaSep idsType);
	rets <- option [] (do { reserved "returns"; parens (commaSep idsType) });
	bs <- many body;
	return (ImplementationDecl name tArgs (ungroup args) (ungroup rets) bs)
	}
	
decl :: Parser Decl
decl = typeDecl <|> constantDecl <|> functionDecl <|> axiomDecl <|> varDecl <|> procDecl <|> implDecl <?> "declaration"
	
program :: Parser Program
program = do { whiteSpace; p <- many decl; eof; return p }

{- Contracts -}

spec :: Parser Spec
spec = do { free <- hasKeyword "free";
	do { reserved "requires"; e <- e0; semi; return (Requires e free) } <|> 
	do { reserved "modifies"; ids <- commaSep identifier; semi; return (Modifies ids free) } <|> 
	do { reserved "ensures"; e <- e0; semi; return (Ensures e free) }
	}

{- Misc -}

skip :: Parser a -> Parser ()
skip p = do { p; return () }

hasKeyword :: String -> Parser Bool
hasKeyword s = option False (do { reserved s; return True })

idsType :: Parser ([Id], Type)
idsType = do { ids <- commaSep1 identifier; reservedOp ":"; t <- type_; return (ids, t) }

ungroup :: [([Id], Type)] -> [(IdType)]
ungroup = concat . (map (\x -> zip (fst x) (repeat (snd x))))

idsTypeWhere :: Parser ([Id], Type, Expression)
idsTypeWhere = do { ids <- idsType; e <- option TT ( do {reserved "where"; e0 }); return ((fst ids), (snd ids), e) }

ungroupWhere :: [([Id], Type, Expression)] -> [(IdTypeWhere)]
ungroupWhere = concat . (map (\x -> zip3 (fst3 x) (repeat (snd3 x)) (repeat (trd3 x))))
	where
		fst3 (a, b, c) = a
		snd3 (a, b, c) = b
		trd3 (a, b, c) = c

trigAttr :: Parser ()
trigAttr = (try trigger) <|> attribute <?> "attribute or trigger"

trigger :: Parser ()
trigger = skip (braces (commaSep1 e0)) <?> "trigger"

attribute :: Parser ()
attribute = skip (braces (do {reservedOp ":"; identifier; commaSep1 ((skip e0) <|> (skip stringLiteral))})) <?> "attribute"
