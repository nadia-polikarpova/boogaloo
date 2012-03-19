{- AST for Boogie 2 -}
module AST where

{- Basic -}

type Id = String

type Program = [Decl]

{- Types -}

data Type = BoolType | IntType | {-BitVectorType Int |-} 
	MapType [Id] [Type] Type |
	Instance Id [Type]
	deriving Show

-- | Type denoted by id	without arguments
idType id = Instance id []

{- Expressions -}

-- | Unary operators
data UnOp = Neg | Not
	deriving (Eq, Show)

-- | Binary operators	
data BinOp = Plus | Minus | Times | Div | Mod | And | Or | Implies | Equiv | Eq | Neq | Lc | Ls | Leq | Gt | Geq
	deriving (Eq, Show)

-- | Quantifiers
data QOp = Forall | Exists
	deriving (Eq, Show)
	
data Expression = FF | TT |
	Numeral Integer | 								              -- Numeral value
	Var Id | 										                    -- Var name
	Application Id [Expression] |					          -- Application function_name args
	MapSelection Expression [Expression] |			    -- MapSelection map indexes
	MapUpdate Expression [Expression] Expression |	-- MapUpdate map indexes rhs
	Old Expression |
	UnaryExpression UnOp Expression |
	BinaryExpression BinOp Expression Expression |
	Quantified QOp [Id] [IdType] Expression			    -- Quantified quantifier type_vars bound_vars expression
	deriving Show
	
data WildcardExpression = Wildcard | Expr Expression
	deriving Show
	
{- Statements -}
data Statement = Assert Expression |
	Assume Expression |
	Havoc [Id] |											                     -- Havoc var_names
	Assign [(Id , [[Expression]])] [Expression] |			    -- Assign var_map_selects rhss
	Call [Id] Id [Expression] |								            -- Call call_lhss proc_name args
	CallForall Id [WildcardExpression] |					        -- CallForall proc_name args
	If WildcardExpression Block (Maybe Block) |				    -- If wild_or_expr then_block else_block
	While WildcardExpression [(Bool, Expression)] Block |	-- While wild_or_expr free_loop_inv loop_body
	Break (Maybe Id) |										                -- Break label
	Return |
	Goto [Id] |												                    -- Goto labels
	Skip 													                        -- only used at the end of a block
	deriving Show

-- | Statement labeled by multiple labels
type LStatement = ([Id], Statement)

type Block = [LStatement] 

-- | Block consisting of a single non-labeled statement
singletonBlock s = [([], s)]

{- Contracts -}

data Spec = Requires Expression Bool |	-- Requires e free 
	Modifies [Id] Bool | 				          -- Modifies var_names free
	Ensures Expression Bool				        -- Ensures e free
	deriving Show

{- Declarations -}

data Decl = 
	TypeDecl Bool Id [Id] (Maybe Type) |									                  -- TypeDecl finite name formals synonym_value
	ConstantDecl Bool [Id] Type ParentInfo Bool |					                  -- ConstantDecl unique names type orderSpec complete
	FunctionDecl Id [Id] [FArg] FArg (Maybe Expression) |	                  -- FunctionDecl name type_args formals ret body
	AxiomDecl Expression |
	VarDecl [IdTypeWhere] |
	ProcedureDecl Id [Id] [IdTypeWhere] [IdTypeWhere] [Spec] (Maybe Body) |	-- ProcedureDecl name type_args formals rets contract body 
	ImplementationDecl Id [Id] [IdType] [IdType] [Body]						          -- ImplementationDecl name type_args formals rets body
  deriving Show

{- Misc -}

type IdType = (Id, Type)
data IdTypeWhere = IdTypeWhere { 
  itwId :: Id, 
  itwType :: Type, 
  itwWhere :: Expression 
  } deriving Show
type FArg = (Maybe Id, Type)
type Body = ([IdTypeWhere], Block)
type ParentEdge = (Bool, Id)
type ParentInfo = Maybe [ParentEdge]

noWhere itw = (itwId itw, itwType itw)
