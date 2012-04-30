module Main where

import Text.ParserCombinators.Parsec
import AST
import Parser
import TypeChecker
import PrettyPrinter
import Control.Monad.Identity
import Control.Monad.Error

-- main = do { result <- parseFromFile program "test.bpl"; 
  -- case (result) of
    -- Left err -> print err
    -- Right p -> print p
  -- }
  
-- main = case (parse program "" "var x, y: int; const z: Wicket;") of
    -- Left err -> print ("Parsing error: " ++ show err)
    -- Right ast -> 
      -- case (runIdentity (runErrorT (checkProgram ast))) of
      -- Left err -> print ("Type error: " ++ err)
      -- Right c -> print c
      
main = do 
  result <- parseFromFile program "test.bpl" 
  case (result) of
    Left err -> print err
    Right ast -> case checkProgram ast of
      Left err -> putStr err
      Right p -> print (programDoc ast)
      
test = do
  result <- parseFromFile program "test.bpl" 
  case (result) of
    Left err -> print err
    Right ast -> do
      case parse program "test1.bpl" (show (programDoc ast)) of
        Left err -> print err
        Right ast' -> if show (programDoc ast) == show (programDoc ast') 
          then putStr ("Passed.\n")
          else putStr ("Failed with different ASTs.\n")

  