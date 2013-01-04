-- | Deterministic and non-deterministic input generators
module Language.Boogie.Generator where

import Control.Monad.Identity hiding (join)
import Control.Monad.Stream
import System.Random

-- | Input generator
data Generator m = Generator {
  genBool :: m Bool,        -- Generate a boolean
  genInteger :: m Integer,  -- Generate an arbitrary precision integer
  genIndex :: Int -> m Int  -- Generate a natural smaller than a given bound
  }
  
-- | Always generates the same default value
defaultGenerator :: Generator Identity  
defaultGenerator = Generator {
  genBool = Identity False,
  genInteger = Identity 0,
  genIndex = Identity . const 0
}

-- | Generates all possible values once, in a predefined order
exhaustiveGenerator :: Maybe (Integer, Integer) -> Generator Stream
exhaustiveGenerator mBounds = Generator {
  genBool = return False `mplus` return True,
  genInteger = case mBounds of
    Nothing -> allIntegers
    Just (a, b) -> fromInterval a b,
  genIndex = \n -> fromList [0 .. n - 1]
}
  where
    allIntegers = fromList [0, -1..] `mplus` fromList [1..]
    fromInterval a b 
      | b < a = mzero
      | a >= 0 || b <= 0 = fromList [a..b]
      | otherwise = fromList [0, -1..a] `mplus` fromList [1..b]

-- | Generated values randomly; the same value can be generated multiple times
randomGenerator :: StdGen -> Maybe (Integer, Integer) -> Generator Stream
randomGenerator rGen mBounds = Generator {
  genBool = fromList $ randoms rGen,
  genInteger = fromList $ case mBounds of
    Nothing -> randoms rGen
    Just bounds -> randomRs bounds rGen,
  genIndex = \n -> fromList $ randomRs (0, n - 1) rGen
}

-- | Convert a (possibly infinite) nonempty list into a stream      
fromList :: [a] -> Stream a
fromList xs = foldr1 mplus (map return xs)
