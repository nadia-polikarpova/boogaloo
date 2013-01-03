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
exhaustiveGenerator :: Generator Stream
exhaustiveGenerator = Generator {
  genBool = return False `mplus` return True,
  genInteger = allIntegers,
  genIndex = \n -> foldr1 mplus (map return [0 .. n - 1])
}

-- | Generated values randomly; the same value can be generated multiple times
randomGenerator :: StdGen -> Generator Stream
randomGenerator rGen = Generator {
  genBool = foldr1 mplus (map return (randoms rGen)),
  genInteger = foldr1 mplus (map return (randoms rGen)),
  genIndex = \n -> foldr1 mplus (map return (randomRs (0, n - 1) rGen))
}

-- | Infinite stream that produces all values of type Integer in the order [0, 1, -1, 2, -2, ...]
allIntegers :: Stream Integer
allIntegers = (return 0) `mplus` genNonZero
  where 
    genNonZero = (return 1) `mplus` (do
      x <- genNonZero
      if x > 0 
        then return $ -x  
        else return $ -x + 1
      )