{- Show instances for AST nodes (to be used in error messages) -}
module Message where

import AST
import Tokens
import Data.List
import Data.Maybe

{- Util -}
  
separated delim xs = concat (intersperse delim xs)  
commaSep = separated ", "
parens s = "(" ++ s ++ ")"
brackets s = "[" ++ s ++ "]"
angles s = "<" ++ s ++ ">"
  
{- Tokens -}

instance Show UnOp where
  show op = fromJust (lookup op unOpTokens)        

instance Show BinOp where
  show op = fromJust (lookup op binOpTokens)
  
instance Show QOp where
  show Forall = "forall"
  show Exists = "exists"

{- Types -}

typeArgs :: [Id] -> String
typeArgs [] = ""
typeArgs args = angles (commaSep args)
  
instance Show Type where
  show BoolType = "bool"
  show IntType = "int"
  show (MapType fv domains range) = typeArgs fv ++
    brackets (commaSep (map show domains)) ++ " " ++
    show range
  show (Instance id args) = id ++ (if null args then "" else " " ++ separated " " (map optParens args))
    where
      optParens BoolType = show BoolType
      optParens IntType = show IntType
      optParens t = parens (show t)

instance Show FSig where
  show (FSig fv args ret) = typeArgs fv ++ " " ++ parens (commaSep (map show args)) ++ ": " ++ show ret
  
instance Show FDef where
  show (FDef args e) = "\\" ++ separated " " args ++ " -> " ++ show e
      
instance Show PSig where
  show (PSig fv args rets) = typeArgs fv ++ " " ++ parens (commaSep (map show args)) ++ ": " ++ parens (commaSep (map show rets))
  
instance Show PDef where
  show (PDef args rets _) = separated " " rets ++ "<- \\" ++ separated " " args ++ " -> ..."
      
{- Expressions -}

instance Show BareExpression where
  show FF = "false"
  show TT = "true"
  show (Numeral n) = show n 
  show (Var id) = id
  show (Application id args) = id ++ parens (commaSep (map show args))
  show (MapSelection m args) = show m ++ brackets (commaSep (map show args))
  show (MapUpdate m args val) = show m ++ brackets (commaSep (map show args) ++  " :=" ++ show val)
  show (Old e) = "old" ++ parens (show e)
  show (UnaryExpression op e) = show op ++ " " ++ parens (show e)
  show (BinaryExpression op e1 e2) = parens (show e1) ++ show op ++ parens (show e2)
  show (Quantified qop fv vars e) = parens (show qop ++ " " ++ typeArgs fv ++ commaSep (map idDecl vars) ++ " :: " ++ show e)
  
instance Show WildcardExpression where
  show Wildcard = "*"
  show (Expr e) = show e
  
{- Misc -}

idDecl (id, t) = id ++ ": " ++ show t