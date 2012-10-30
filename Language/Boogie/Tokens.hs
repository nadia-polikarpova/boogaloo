-- | Tokens used in Boogie 2
module Language.Boogie.Tokens where

import Language.Boogie.AST
import Data.Maybe

-- | Keywords
keywords :: [String]
keywords = ["assert", "assume", "axiom", "bool", "break", "call", "complete", "const",
    "else", "div", "ensures", "exists", "extends", "false", "forall", "free", "function",
    "goto", "havoc", "if", "implementation", "int", "invariant", "lambda", "mod", "modifies",
    "old", "procedure", "requires", "return", "returns", "then", "true", "type", "unique",
    "var", "where", "while"]

-- | 'opName' @op table@ : lookup operator name in @table@
opName op table = fromJust (lookup op table)
    
-- | Names of unary operators    
unOpTokens :: [(UnOp, String)]
unOpTokens = [(Neg, "-"),
              (Not, "!")]
             
-- | Names of binary operators             
binOpTokens :: [(BinOp, String)]
binOpTokens = [(Plus,    "+"),
               (Minus,   "-"),
               (Times,   "*"),
               (Div,     "div"),
               (Mod,     "mod"),
               (And,     "&&"),
               (Or,      "||"),
               (Implies, "==>"),
               (Explies, "<=="),
               (Equiv,   "<==>"),
               (Eq,      "=="),
               (Neq,     "!="),
               (Lc,      "<:"),
               (Ls,      "<"),
               (Leq,     "<="),
               (Gt,      ">"),
               (Geq,     ">=")]
    
-- | Names of quantifiers    
qOpTokens :: [(QOp, String)]
qOpTokens = [ (Forall, "forall"),
              (Exists, "exists"),
              (Lambda, "lambda") ]         
         
-- | Other operators         
otherOps :: [String]
otherOps = [":", ";", "::", ":=", "="] 

-- | Characters allowed in identifiers (in addition to letters and digits)
identifierChars = "_.$#\'`~^\\?"
-- | Start of a multi-line comment
commentStart = "/*"
-- | End of a multi-line comment
commentEnd = "*/"
-- | Start of a single-line comment
commentLine = "//"

-- | A character that is not allowed in identifiers (used for generating unique names)
nonIdChar = '*'         