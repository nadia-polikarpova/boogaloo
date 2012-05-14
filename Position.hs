{- Utility for attaching source code positions to AST nodes -}
module Position 
    (Pos (..)
    ,Line
    ,Column
    ,SourcePos

    ,sourceLine
    ,sourceColumn
    ,sourceName

    ,noPos
    ,attachPos
    ,attachPosM
    ,gen
    ,attachPosBefore
    ,inheritPos    

    ) where

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.Parsec.Pos

data Pos a = Pos {
  position :: SourcePos,
  contents :: a
}

instance Eq a => Eq (Pos a) where
    (==) p1 p2 = contents p1 == contents p2

instance Show a => Show (Pos a) where
    show p = show (contents p)

instance Functor Pos where
    fmap f (Pos s a) = Pos s (f a)
    
attachPos :: SourcePos -> a -> Pos a
attachPos = Pos

noPos = (initialPos "<no file name>")

gen = attachPos noPos

attachPosM :: Monad m => m SourcePos -> m a -> m (Pos a)
attachPosM = liftM2 attachPos

attachPosBefore :: Parser a -> Parser (Pos a)
attachPosBefore = attachPosM getPosition

inheritPos :: (Pos a -> b) -> Pos a -> Pos b
inheritPos f a = attachPos (position a) (f a)