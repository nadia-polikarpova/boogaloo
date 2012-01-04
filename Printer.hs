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