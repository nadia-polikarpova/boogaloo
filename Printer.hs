{- Pretty printer for Boogie 2 -}
module Printer where

import AST
import Tokens
import Data.List
import Data.Maybe

class Pretty a where
  pretty :: a -> String
  
separated delim xs = concat (intersperse delim xs)  
commaSep = separated ", "
parens s = "(" ++ s ++ ")"
brackets s = "[" ++ s ++ "]"
angles s = "<" ++ s ++ ">"
  
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
typeArgs args = angles (commaSep args)
  
instance Pretty Type where
  pretty BoolType = "bool"
  pretty IntType = "int"
  pretty (MapType fv domains range) = typeArgs fv ++
    brackets (commaSep (map pretty domains)) ++ " " ++
    pretty range
  pretty (Instance id args) = id ++ (if null args then "" else " " ++ separated " " (map optParens args))
    where
      optParens BoolType = pretty BoolType
      optParens IntType = pretty IntType
      optParens t = parens (pretty t)
      
instance Pretty PSig where
  pretty (PSig fv args rets) = typeArgs fv ++ " " ++ parens (commaSep (map pretty args)) ++ ": " ++ parens (commaSep (map pretty rets))
      
{- Expressions -}

instance Pretty Expression where
  pretty FF = "false"
  pretty TT = "true"
  pretty (Numeral n) = show n 
  pretty (Var id) = id
  pretty (Application id args) = id ++ parens (commaSep (map pretty args))
  pretty (MapSelection m args) = pretty m ++ brackets (commaSep (map pretty args))
  pretty (MapUpdate m args val) = pretty m ++ brackets (commaSep (map pretty args) ++  " :=" ++ pretty val)
  pretty (Old e) = "old" ++ parens (pretty e)
  pretty (UnaryExpression op e) = pretty op ++ " " ++ parens (pretty e)
  pretty (BinaryExpression op e1 e2) = parens (pretty e1) ++ pretty op ++ parens (pretty e2)
  pretty (Quantified qop fv vars e) = parens (pretty qop ++ " " ++ typeArgs fv ++ commaSep (map idDecl vars) ++ " :: " ++ pretty e)
  
{- Misc -}

idDecl (id, t) = id ++ ": " ++ pretty t