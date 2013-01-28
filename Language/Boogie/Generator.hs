-- | Deterministic and non-deterministic input generators
module Language.Boogie.Generator where

import Control.Monad.Identity hiding (join)
import Control.Monad.Stream
import System.Random

-- | Input generator
data Generator m = Generator {
  genBool :: m Bool,        -- Generate a boolean
  genInteger :: m Integer,  -- Generate an arbitrary precision integer
  genNatural :: m Integer,  -- Generate an arbitrary precision, non-negative integer
  genIndex :: Int -> m Int  -- Generate a natural smaller than a given bound
  }
  
-- | Always generates the same default value
defaultGenerator :: Generator Identity  
defaultGenerator = Generator {
  genBool = Identity False,
  genInteger = Identity 0,
  genNatural = Identity 0,
  genIndex = Identity . const 0
}

-- | Generates all possible values once, in a predefined order
exhaustiveGenerator :: Maybe Integer -> Generator Stream
exhaustiveGenerator mBound = Generator {
  genBool = return False `mplus` return True,
  genInteger = case mBound of
    Nothing -> allIntegers
    Just n -> fromInterval $ intInterval n,
  genNatural = case mBound of
    Nothing -> fromList [0..]
    Just n -> fromInterval $ natInterval n,
  genIndex = \n -> fromList [0 .. n - 1]
}
  where
    allIntegers = fromList [0, -1..] `mplus` fromList [1..]
    fromInterval (a, b)
      | b < a = mzero
      | a >= 0 || b <= 0 = fromList [a..b]
      | otherwise = fromList [0, -1..a] `mplus` fromList [1..b]

-- | Generated values randomly; the same value can be generated multiple times
randomGenerator :: StdGen -> Maybe Integer -> Generator Stream
randomGenerator rGen mBound = Generator {
  genBool = fromList $ randoms rGen,
  genInteger = fromList $ case mBound of
    Nothing -> randoms rGen
    Just n -> randomRs (intInterval n) rGen,
  genNatural = fromList $ case mBound of
    Nothing -> map abs $ randoms rGen
    Just n -> randomRs (natInterval n) rGen,
  genIndex = \n -> fromList $ randomRs (0, n - 1) rGen
}

-- | 'intInterval' @n@: interval centered around 0 of size n
intInterval n = let n2 = n `div` 2 in (-n2, n - n2 - 1)

-- | 'natInterval' @n@: interval starting from 0 of size n
natInterval n = (0, n - 1)

-- | Convert a (possibly infinite) nonempty list into a stream      
fromList :: [a] -> Stream a
fromList xs = foldr1 mplus (map return xs)
