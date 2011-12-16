{- AST for Boogie -}
module AST where 

{- Basic -}
type Id = String

type Program = [Decl]

{- Types -}
data Type = BoolType | IntType | {-BitVectorType Int |-} 
	MapType [Id] [Type] Type |
	Instance Id [Type]
	deriving Show

{- Expressions -}
data UnOp = Neg | Not
	deriving (Eq, Show)

data BinOp = Plus | Minus | Times | Div | Mod | And | Or | Implies | Equiv | Eq | Neq | Lc | Ls | Leq | Gt | Geq
	deriving (Eq, Show) 	-- ToDo: redefine show
	
data QOp = Forall | Exists
	deriving (Eq, Show)
	
data Expression = FF | TT | Numeral Integer | 
	Var Id | Application Id [Expression] |
	MapSelection Expression [Expression] |
	MapUpdate Expression [Expression] Expression |
	Old Expression |
	UnaryExpression UnOp Expression |
	BinaryExpression BinOp Expression Expression |
	Quantified QOp [Id] [(Id, Type)] Expression
	deriving Show
	
data WildcardExpression = Wildcard | Expr Expression
	deriving Show
	
{- Statements -}

data Statement = Assert Expression |
	Assume Expression |
	Havoc [Id] |
	Assign [(Id , [[Expression]])] [Expression] |
	Call [Id] Id [Expression] |
	CallForall Id [WildcardExpression] |
	If WildcardExpression Block (Maybe Block) |
	While WildcardExpression [(Bool, Expression)] Block |
	Break (Maybe Id) |
	Return |
	Goto [Id] |
	Skip -- only used at the end of a block
	deriving Show
	
type LStatement = ([Id], Statement)

type Block = [LStatement] 

singletonBlock s = [([], s)]

{- Declarations -}

data Decl = TypeDecl Bool Id [Id] (Maybe Type) |
	ConstantDecl Bool [Id] Type ParentInfo Bool |
	FunctionDecl Id [FArg] FArg (Maybe Expression) |
	AxiomDecl Expression |
	VarDecl [(Id, Type, Expression)]
	-- ProcedureDecl |
	-- ImplementationDecl
	deriving Show

{- Misc -}

type ParentEdge = (Bool, Id)
type ParentInfo = Maybe [ParentEdge]
type FArg = (Maybe Id, Type)