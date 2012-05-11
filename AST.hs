{- AST for Boogie 2 -}
module AST where

import Position
import Data.Maybe
import Data.List
import Data.Map (Map)

{- Basic -}

type Id = String

type Program = [Decl]

{- Types -}

data Type = BoolType | IntType | {-BitVectorType Int |-} 
	MapType [Id] [Type] Type |
	Instance Id [Type]

-- | Type denoted by id	without arguments
idType id = Instance id []

-- | Dummy type used during type checking to denote error
noType = idType "NoType"

{- Expressions -}

-- | Unary operators
data UnOp = Neg | Not
	deriving Eq

-- | Binary operators	
data BinOp = Plus | Minus | Times | Div | Mod | And | Or | Implies | Equiv | Eq | Neq | Lc | Ls | Leq | Gt | Geq
	deriving Eq

-- | Quantifiers
data QOp = Forall | Exists
	deriving Eq
  
type Expression = Pos BareExpression
	
data BareExpression = FF | TT |
	Numeral Integer | 								              -- Numeral value
	Var Id | 										                    -- Var name
	Application Id [Expression] |					          -- Application function_name args
	MapSelection Expression [Expression] |			    -- MapSelection map indexes
	MapUpdate Expression [Expression] Expression |	-- MapUpdate map indexes rhs
	Old Expression |
	UnaryExpression UnOp Expression |
	BinaryExpression BinOp Expression Expression |
	Quantified QOp [Id] [IdType] Expression			    -- Quantified quantifier type_vars bound_vars expression
	
data WildcardExpression = Wildcard | Expr Expression
	
{- Statements -}
type Statement = Pos BareStatement

data BareStatement = Assert Expression |
	Assume Expression |
	Havoc [Id] |											                    -- Havoc var_names
	Assign [(Id , [[Expression]])] [Expression] |			    -- Assign var_map_selects rhss
	Call [Id] Id [Expression] |								            -- Call call_lhss proc_name args
	CallForall Id [WildcardExpression] |					        -- CallForall proc_name args
	If WildcardExpression Block (Maybe Block) |				    -- If wild_or_expr then_block else_block
	While WildcardExpression [(Bool, Expression)] Block |	-- While wild_or_expr free_loop_inv loop_body
	Break (Maybe Id) |										                -- Break label
	Return |
	Goto [Id] |												                    -- Goto labels
	Skip 													                        -- only used at the end of a block

-- | Statement labeled by multiple labels
type LStatement = Pos BareLStatement

type BareLStatement = ([Id], Statement)

type Block = [LStatement] 

-- | Block consisting of a single non-labeled statement
singletonBlock s = [attachPos (position s) ([], s)]

type Body = ([[IdTypeWhere]], Block)

type BasicBlock = (Id, [Statement])

type BasicBody = ([IdTypeWhere], Map Id [Statement])

{- Contracts -}

data Spec = Requires Expression Bool |	-- Requires e free 
	Modifies [Id] Bool | 				          -- Modifies var_names free
	Ensures Expression Bool				        -- Ensures e free
  
preconditions :: [Spec] -> [Expression]
preconditions specs = catMaybes (map extractPre specs)
  where 
    extractPre (Requires e _) = Just e
    extractPre _ = Nothing

postconditions :: [Spec] -> [Expression]
postconditions specs = catMaybes (map extractPost specs)
  where 
    extractPost (Ensures e _) = Just e
    extractPost _ = Nothing
    
modifies :: [Spec] -> [Id]
modifies specs = (nub . concat . catMaybes) (map extractMod specs)
  where
    extractMod (Modifies ids _) = Just ids
    extractMod _ = Nothing

{- Declarations -}

type Decl = Pos BareDecl

data BareDecl = 
	TypeDecl [NewType] |
	ConstantDecl Bool [Id] Type ParentInfo Bool |					                  -- ConstantDecl unique names type orderSpec complete
	FunctionDecl Id [Id] [FArg] FArg (Maybe Expression) |	                  -- FunctionDecl name type_args formals ret body
	AxiomDecl Expression |
	VarDecl [IdTypeWhere] |
	ProcedureDecl Id [Id] [IdTypeWhere] [IdTypeWhere] [Spec] (Maybe Body) |	-- ProcedureDecl name type_args formals rets contract body 
	ImplementationDecl Id [Id] [IdType] [IdType] [Body]						          -- ImplementationDecl name type_args formals rets body
  
{- Misc -}

data NewType = NewType {
  tId :: Id,
  tArgs :: [Id],
  tValue :: Maybe Type
  }

type IdType = (Id, Type)

data IdTypeWhere = IdTypeWhere { 
  itwId :: Id, 
  itwType :: Type, 
  itwWhere :: Expression 
  }
  
type FArg = (Maybe Id, Type)

type ParentEdge = (Bool, Id)

type ParentInfo = Maybe [ParentEdge]

-- | Function signature: type variables, argument types, return type
data FSig = FSig {
    fsigTypeVars :: [Id],
    fsigArgTypes :: [Type],
    fsigRetType :: Type
  }

-- | Function definition: in-parameter names and expression
data FDef = FDef {
    fdefIns :: [Id],
    fdefBody:: Expression
  }
  
-- | Procedure signature: type variables, argument types, return types
data PSig = PSig {
    psigTypeVars :: [Id],
    psigArgTypes :: [Type], 
    psigRetTypes :: [Type]
  }

-- | Procedure definition: in-parameter names, out-parameter names and body represented with basic blocks 
data PDef = PDef { 
    pdefIns :: [Id],
    pdefOuts :: [Id], 
    pdefBody :: BasicBody
  }

noWhere itw = (itwId itw, itwType itw)

mapSelectExpr target args = attachPos (position target) (MapSelection target args)
