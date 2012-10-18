{- AST for Boogie 2 -}
module AST where

import Position
import Data.Map (Map)

{- Basic -}

type Id = String

newtype Program = Program [Decl]
  deriving Eq

{- Types -}

data Type = BoolType | IntType | {-BitVectorType Int |-} 
  MapType [Id] [Type] Type |
  Instance Id [Type]
  deriving Eq -- syntactic equality

-- | Type denoted by id without arguments
nullaryType id = Instance id []

-- | Dummy type used during type checking to denote error
noType = nullaryType "NoType"

{- Expressions -}

-- | Unary operators
data UnOp = Neg | Not
  deriving Eq

-- | Binary operators  
data BinOp = Plus | Minus | Times | Div | Mod | And | Or | Implies | Explies | Equiv | Eq | Neq | Lc | Ls | Leq | Gt | Geq
  deriving Eq

-- | Quantifiers
data QOp = Forall | Exists | Lambda
  deriving Eq
  
type Expression = Pos BareExpression
  
data BareExpression = FF | TT |
  Numeral Integer |                               -- Numeral value
  Var Id |                                        -- Var name
  Application Id [Expression] |                   -- Application function_name args
  MapSelection Expression [Expression] |          -- MapSelection map indexes
  MapUpdate Expression [Expression] Expression |  -- MapUpdate map indexes rhs
  Old Expression |
  IfExpr Expression Expression Expression |
  Coercion Expression Type |
  UnaryExpression UnOp Expression |
  BinaryExpression BinOp Expression Expression |  
  Quantified QOp [Id] [IdType] Expression          -- Quantified quantifier type_vars bound_vars expression
  deriving Eq -- syntactic equality
  
mapSelectExpr target args = attachPos (position target) (MapSelection target args)  
  
data WildcardExpression = Wildcard | Expr Expression
  deriving Eq
  
{- Statements -}

type Statement = Pos BareStatement

data BareStatement = Predicate SpecClause |      -- Predicate statement (assume or assert)
  Havoc [Id] |                                   -- Havoc var_names
  Assign [(Id , [[Expression]])] [Expression] |  -- Assign var_map_selects rhss
  Call [Id] Id [Expression] |                    -- Call call_lhss proc_name args
  CallForall Id [WildcardExpression] |           -- CallForall proc_name args
  If WildcardExpression Block (Maybe Block) |    -- If wild_or_expr then_block else_block
  While WildcardExpression [SpecClause] Block |  -- While wild_or_expr free_loop_inv loop_body
  Break (Maybe Id) |                             -- Break label
  Return |
  Goto [Id] |                                    -- Goto labels
  Skip                                           -- only used at the end of a block
  deriving Eq -- syntactic equality

-- | Statement labeled by multiple labels
type LStatement = Pos BareLStatement

type BareLStatement = ([Id], Statement)

type Block = [LStatement] 

-- | Block consisting of a single non-labeled statement
singletonBlock s = [attachPos (position s) ([], s)]

type Body = ([[IdTypeWhere]], Block)

type BasicBlock = (Id, [Statement])

type BasicBody = ([IdTypeWhere], Map Id [Statement])

{- Specs -}

data SpecType = Inline | Precondition | Postcondition | LoopInvariant | Where
  deriving Eq

-- | Specification clause that can be checked at runtime
data SpecClause = SpecClause {
  specType :: SpecType,   -- Source of the clause
  specFree :: Bool,       -- Is it free (assumption) or checked (assertions)?
  specExpr :: Expression  -- Boolean expression
  } deriving Eq

data Contract = Requires Bool Expression |  -- Requires e free 
  Modifies Bool [Id] |                      -- Modifies var_names free
  Ensures Bool Expression                   -- Ensures e free
  deriving Eq

{- Declarations -}

type Decl = Pos BareDecl

data BareDecl = 
  TypeDecl [NewType] |
  ConstantDecl Bool [Id] Type ParentInfo Bool |                            -- ConstantDecl unique names type orderSpec complete
  FunctionDecl Id [Id] [FArg] FArg (Maybe Expression) |                    -- FunctionDecl name type_args formals ret body
  AxiomDecl Expression |
  VarDecl [IdTypeWhere] |
  ProcedureDecl Id [Id] [IdTypeWhere] [IdTypeWhere] [Contract] (Maybe Body) |  -- ProcedureDecl name type_args formals rets contract body 
  ImplementationDecl Id [Id] [IdType] [IdType] [Body]                      -- ImplementationDecl name type_args formals rets body
  deriving Eq
  
{- Misc -}

data NewType = NewType {
  tId :: Id,
  tArgs :: [Id],
  tValue :: Maybe Type
  } deriving Eq

type IdType = (Id, Type)

data IdTypeWhere = IdTypeWhere { 
  itwId :: Id, 
  itwType :: Type, 
  itwWhere :: Expression 
  } deriving Eq
  
noWhere itw = (itwId itw, itwType itw)  
  
type FArg = (Maybe Id, Type)

-- | Argument name used for unnamed function arguments
-- | (does not matter, because it is never referred to from function's body)  
dummyFArg = ""

type ParentEdge = (Bool, Id)

type ParentInfo = Maybe [ParentEdge]
