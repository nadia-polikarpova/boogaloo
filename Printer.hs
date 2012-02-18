{- Pretty printer for Boogie 2 -}
module Printer where

import AST
import Tokens
import Data.List
import Data.Maybe

class Pretty a where
	pretty :: a -> String
	
separated :: String -> [String] -> String
separated delim xs = concat (intersperse delim xs)
	
{- Tokens -}

instance Pretty UnOp where
	pretty op = fromJust (lookup op unOpTokens)			  

instance Pretty BinOp where
	pretty op = fromJust (lookup op binOpTokens)
	
instance Pretty QOp where
	pretty Forall = "forall"
	pretty Exists = "exists"

{- Types -}

typeArgs :: [Id] -> String
typeArgs [] = ""
typeArgs args = "<" ++ separated ", " args  ++ "> "
	
instance Pretty Type where
	pretty BoolType = "bool"
	pretty IntType = "int"
	pretty (MapType fv domains range) = typeArgs fv ++
		"[" ++ separated ", " (map pretty domains) ++ "]" ++ " " ++
		pretty range
	pretty (Instance id args) = id ++ (if null args then "" else " " ++ separated " " (map parens args))
		where
			parens BoolType = pretty BoolType
			parens IntType = pretty IntType
			parens t = "(" ++ pretty t ++ ")"
			
{- Expressions -}

instance Pretty Expression where
	pretty FF = "false"
	pretty TT = "true"
	pretty (Numeral n) = show n 
	pretty (Var id) = id
	pretty (Application id args) = id ++ "(" ++ separated ", " (map pretty args) ++ ")"
	pretty (MapSelection m args) = pretty m ++ "[" ++ separated ", " (map pretty args) ++ "]"
	pretty (MapUpdate m args val) = pretty m ++ "[" ++ separated ", " (map pretty args) ++  " :=" ++ pretty val ++ "]"
	pretty (Old e) = "old(" ++ pretty e ++ ")"
	pretty (UnaryExpression op e) = pretty op ++ " (" ++ pretty e ++ ")"
	pretty (BinaryExpression op e1 e2) = "(" ++ pretty e1 ++ ") " ++ pretty op ++ " (" ++ pretty e2 ++ ")"
	pretty (Quantified qop fv vars e) = "(" ++ pretty qop ++ " " ++ typeArgs fv ++ separated ", " (map idDecl vars) ++ " :: " ++ pretty e ++ ")"
	
{- Misc -}

idDecl (id, t) = id ++ ": " ++ pretty t