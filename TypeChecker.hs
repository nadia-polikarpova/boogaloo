module TypeChecker where

import AST
import qualified Data.Map as M
import Control.Monad.Identity
import Control.Monad.Error

type Checked a = ErrorT String Identity a

type Context = M.Map Id Type

checkProgram :: Program -> Checked Context
checkProgram p = foldM checkDecl M.empty p

checkDecl :: Context -> Decl -> Checked Context
checkDecl c d = case d of
	VarDecl vars -> foldM checkIdType c (map noWhere vars)
	ConstantDecl _ ids t _ _ -> foldM checkIdType c (zip ids (repeat t))
	otherwise -> return c
		
checkIdType :: Context -> IdType -> Checked Context
checkIdType c (i, t) 	
	| M.member i c = throwError ("Multiple declarations of variable or constant " ++ i) 
	| otherwise = return (M.insert i t c)