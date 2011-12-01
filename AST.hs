{- AST for Boogie -}
module AST where 

{- Basic -}
type Id = String

{- Expressions -}
data UnOp = Neg | Not
	deriving (Eq, Show)

data BinOp = Plus | Minus | Times | Div | Mod | And | Or | Implies | Equiv | Eq | Neq | Lc | Ls | Leq | Gt | Geq
	deriving (Eq, Show) 	-- ToDo: redefine show
	
data Expression = FF | TT | Numeral Integer | 
	Var Id | Application Id [Expression] |
	MapSelection Expression [Expression] |
	MapUpdate Expression [Expression] Expression |
	Old Expression |
	UnaryExpression UnOp Expression |
	BinaryExpression BinOp Expression Expression
	deriving Show
		
{- Types -}
data Type = BoolType | IntType | BitVectorType Int | MapType [Type] Type -- ToDo: user defined types 
	
