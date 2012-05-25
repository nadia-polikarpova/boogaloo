{- Tokens used in Boogie 2 -}
module Tokens where

import AST
import Data.Maybe

keywords :: [String]
keywords = ["assert", "assume", "axiom", "bool", "break", "call", "complete", -- ToDO: bit vector keywords omitted
    "const", "else", "ensures", "exists", "extends", "false", "forall", "free", "function",
    "goto", "havoc", "if", "implementation", "int", "invariant", "modifies", "old",
    "procedure", "requires", "return", "returns", "true", "type", "unique", "var",
    "where", "while"]

token node table = fromJust (lookup node table)
    
unOpTokens :: [(UnOp, String)]
unOpTokens = [(Neg, "-"),
              (Not, "!")]
                        
binOpTokens :: [(BinOp, String)]
binOpTokens = [(Plus,    "+"),
               (Minus,   "-"),
         (Times,   "*"),
         (Div,     "/"),
         (Mod,     "%"),
         --(Con,     "++"),
         (And,     "&&"),
         (Or,      "||"),
         (Implies, "==>"),
         (Equiv,   "<==>"),
         (Eq,      "=="),
         (Neq,     "!="),
         (Lc,      "<:"),
         (Ls,      "<"),
         (Leq,     "<="),
         (Gt,      ">"),
         (Geq,     ">=")]
         
otherOps :: [String]
otherOps = [":", ";", "::", ":=", "="] 

identifierChars = "_.$#\'`~^\\?"         
commentStart = "/*"
commentEnd = "*/"
commentLine = "//"

nonIdChar = '*'         