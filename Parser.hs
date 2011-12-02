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
		   parens typeParser
		   
mapType :: Parser Type
mapType = do { 
	args <- (option [] (angles (commaSep1 identifier))); 
	domains <- brackets (commaSep1 typeParser); 
	range <- typeParser; 
	return (MapType args domains range) 
	}
	
typeCtorArgs :: Parser [Type]
typeCtorArgs = do { x <- typeAtom; xs <- option [] typeCtorArgs; return (x : xs) } <|>
               do { x <- identifier; xs <- option [] typeCtorArgs; return ((Instance x []) : xs) } <|>
			   do { x <- mapType; return [x] }

typeParser :: Parser Type
typeParser = typeAtom <|> mapType <|>
	do { id <- identifier; args <- option [] typeCtorArgs; return (Instance id args) }


{- Expressions -}
	
e9 :: Parser Expression
e9 = do { reserved "false"; return FF } <|>
     do { reserved "true"; return TT } <|> 
	 do { n <- natural; return (Numeral n) } <|> 
	 -- str bitVector <|>
	 do { id <- identifier; ( do { args <- parens (commaSep e0); return (Application id args) }) <|> return (Var id) } <|>
	 do { reserved "old"; e <- parens e0; return (Old  e) } <|>
	--try (parens (do { qop; optional typeArgs; commaSep1 idsType; qsep; many trigAttr; res <- e0; return res })) <|>
	parens e0

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

{-
qop :: Parser String
qop = str (reserved "forall" <|> reserved "exists")

qsep :: Parser String
qsep = str (reservedOp "::")

typeArgs :: Parser String
typeArgs = str (angles (commaSep1 identifier))

bitVectorType :: Parser String
bitVectorType = do { reserved "bv"; n <- natural; return (show n)}

typeAtom :: Parser String
typeAtom = str (reserved "int") <|> str (reserved "bool") <|> bitVectorType <|> parens type_

mapType :: Parser String
mapType = do {optional typeArgs; brackets (commaSep type_); type_; return "map type"}

typeCtorArgs :: Parser String
typeCtorArgs = do {type_; optional typeCtorArgs; return "typeCtorArgs"} <|>
	do {identifier; optional typeCtorArgs; return "typeCtorArgs"} <|>
	mapType

type_ :: Parser String
type_ = typeAtom <|> mapType <|> do {identifier; optional typeCtorArgs; return "type identifier"}

idsType :: Parser String
idsType = do { commaSep1 identifier; symbol ":"; type_}

trigAttr :: Parser String
trigAttr = trigger <|> attribute

trigger :: Parser String
trigger = str (braces (commaSep1 e0))

attribute :: Parser String
attribute = braces (do {reservedOp ":"; identifier; commaSep1 attrArg; return "attribute"})

attrArg :: Parser String
attrArg = e0 <|> stringLiteral

bitVector :: Parser String
bitVector = do {
		i <- many1 digit;
		string "bv";
		natural;
		return i
	}
-}			