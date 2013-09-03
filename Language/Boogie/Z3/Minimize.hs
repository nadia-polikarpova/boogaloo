module Language.Boogie.Z3.Minimize where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.IO.Class

import           Data.Maybe
import qualified Data.Map as Map

import           Z3.Monad

import           Language.Boogie.AST
import           Language.Boogie.Solver
import           Language.Boogie.Z3.Eval
import           Language.Boogie.Z3.GenMonad

minimizeModel :: Model -> [Expression] -> Z3Gen Model
minimizeModel model constrs = 
    do v <- evalObj model 
       go model Nothing (v-1) (v+1)
    where
      go :: Model -> Maybe Integer -> Integer -> Integer -> Z3Gen Model
      go m loMb pivot hi
         | isNothing loMb || hi - fromJust loMb > 2 =
             do push
                assertPivot pivot
                check
                (_, modelMb) <- getModel
                case modelMb of
                  Just m' ->
                      case loMb of
                        Nothing ->
                            do let pivot' = if pivot >= 0
                                            then (-1)
                                            else pivot * 2
                               debug ("go SAT Nothing:" ++ show (loMb, pivot, hi))
                               pop 1
                               go m' loMb pivot' (pivot + 1)
                        Just lo ->
                            do lv <- evalObj m'
                               let pivot' = lo + (lv + 1 - lo) `div` 2
                               debug ("go SAT Just:" ++ show (loMb, pivot, hi))
                               pop 1
                               go m' loMb pivot' (pivot + 1)
                  Nothing ->
                      do let pivot' = pivot + ((hi - pivot) `div` 2)
                         debug ("go UNSAT:" ++ show (loMb, pivot, hi))
                         pop 1
                         go m (Just pivot) pivot' hi
         | otherwise = debug ("go DONE:" ++ show (loMb, pivot,hi)) >> return m
                

      assertPivot pivot =
          do obj <- objective
             piv <- mkInt pivot
             pivCnstr <- mkLe obj piv
             assertCnstr pivCnstr

      evalObj :: Model -> Z3Gen Integer
      evalObj m =
          do objAst <- objective
             Just objVal <- eval m objAst
             v <- getInt objVal
             str <- astToString objAst
             debug (unwords ["Objective value:", show v, str])
             return v



-- | Objective function taken from the current ref map.
objective :: Z3Gen AST
objective =
    do intMbs <- mapM (uncurry intAst) =<< uses refMap Map.toList
       let ints = catMaybes intMbs
       if null ints
         then mkInt 0
         else mkAdd ints
    where
      intAst :: TaggedRef -> AST -> Z3Gen (Maybe AST)
      intAst (LogicRef t _ref) ast =
          case t of 
            IntType -> Just <$> absT ast
            IdType ident types ->
                do (_, _, proj) <- lookupCustomType ident types
                   val <- mkApp proj [ast]
                   Just <$> absT val
            _ -> return Nothing
      intAst _ _ = return Nothing
          

      absT :: AST -> Z3Gen AST
      absT ast =
          do zero <- mkInt 0
             less <- mkLt ast zero
             negAst <- mkUnaryMinus ast
             mkIte less negAst ast
