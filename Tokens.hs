{- Tokens used in Boogie 2 -}
module Tokens where

import AST
import Data.Maybe

keywords :: [String]
keywords = ["assert", "assume", "axiom", "bool", "break", "call", "complete", "const", -- ToDO: bit vector keywords omitted
    "else", "div", "ensures", "exists", "extends", "false", "forall", "free", "function",
    "goto", "havoc", "if", "implementation", "int", "invariant", "mod", "modifies", "old",
    "procedure", "requires", "return", "returns", "then", "true", "type", "unique", "var",
    "where", "while"]

token node table = fromJust (lookup node table)
    
unOpTokens :: [(UnOp, String)]
unOpTokens = [(Neg, "-"),
              (Not, "!")]
                        
binOpTokens :: [(BinOp, String)]
binOpTokens = [(Plus,    "+"),
               (Minus,   "-"),
         (Times,   "*"),
         (Div,     "div"),
         (Mod,     "mod"),
         --(Con,     "++"),
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
         
qOpTokens :: [(QOp, String)]
qOpTokens = [(Forall, "forall"),
              (Exists, "exists")]         
         
otherOps :: [String]
otherOps = [":", ";", "::", ":=", "="] 

identifierChars = "_.$#\'`~^\\?"         
commentStart = "/*"
commentEnd = "*/"
commentLine = "//"

nonIdChar = '*'         