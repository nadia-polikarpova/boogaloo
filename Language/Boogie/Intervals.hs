{-# LANGUAGE PatternGuards #-}

-- | Lattice of integer intervals
module Language.Boogie.Intervals where

import Data.Ratio
import Data.Maybe

-- | Lattice type class 
class Eq a => Lattice a where
  top   :: a              -- ^ Top
  bot   :: a              -- ^ Bottom
  (<:)  :: a -> a -> Bool -- ^ Partial order
  join  :: a -> a -> a    -- ^ Least upper bound
  meet  :: a -> a -> a    -- ^ Greatest lower bound
  
  x <: y = meet x y == x

-- | Integers extended with infinity
data Extended = NegInf | Finite Integer | Inf
  deriving Eq
  
instance Show Extended where
  show NegInf = "-Infinity"
  show (Finite i) = show i
  show Inf = "Infinity"
  
instance Num Extended where
  Inf + NegInf = error ("Cannot add " ++ show Inf ++ " and " ++ show NegInf)
  NegInf + Inf = error ("Cannot add " ++ show NegInf ++ " and " ++ show Inf)
  Inf + _ = Inf
  NegInf + _ = NegInf
  Finite _ + Inf = Inf
  Finite _ + NegInf = NegInf
  Finite i + Finite j = Finite (i + j)
  
  Finite 0 * _ = Finite 0
  _ * Finite 0 = Finite 0
  e1 * e2 | signum (e1) == -1 && signum (e2) == -1 = negate e1 * negate e2
  e1 * e2 | signum (e1) == -1 = negate $ negate e1 * e2
  e1 * e2 | signum (e2) == -1 = negate $ e1 * negate e2
  Inf * _ = Inf
  _ * Inf = Inf
  Finite i * Finite j = Finite (i * j)
  
  negate Inf = NegInf
  negate NegInf = Inf
  negate (Finite i) = Finite (-i)
  
  abs Inf = Inf
  abs NegInf = Inf
  abs (Finite i) = Finite (abs i)
  
  signum Inf = 1
  signum NegInf = -1
  signum (Finite i) = Finite (signum i)
  
  fromInteger i = Finite i

-- | 'extDiv' @r a b@ : result of dividing @a@ by @b@, rounded with @r@ in the finite case;
-- dividing infinty by infinity yields 'Nothing'.
extDiv :: (Ratio Integer -> Integer) -> Extended -> Extended -> Maybe Extended  
extDiv r (Finite i) (Finite j) = Just $ Finite (r (i % j))
extDiv _ Inf (Finite j) = Just $ signum (Finite j) * Inf
extDiv _ NegInf (Finite j) = Just $ signum (Finite j) * NegInf
extDiv _ (Finite i) Inf = Just $ 0
extDiv _ (Finite i) NegInf = Just $ 0
extDiv _ _ _ = Nothing  

instance Ord Extended where
  NegInf <= b = True
  b <= NegInf = False
  b <= Inf = True
  Inf <= b = False
  Finite x <= Finite y = x <= y
 
-- | Integer intervals
data Interval = Interval {
  lower :: Extended,
  upper :: Extended
}

-- | Is interval empty?
isBottom (Interval l u) = l > u

-- | Are both bounds of the interval finite?
isBounded (Interval (Finite l) (Finite u)) = True
isBounded _ = False

-- | All positive integers
positives = Interval 1 Inf
-- | All negative integers
negatives = Interval NegInf (-1)
-- | All positive integers and 0
nonNegatives = Interval 0 Inf
-- | All netaive integers and 0
nonPositives = Interval NegInf 0

-- | Apply function to all pairs of bounds coming from two different intervals
mapBounds f (Interval l1 u1) (Interval l2 u2) = [f b1 b2 | b1 <- [l1, u1], b2 <- [l2, u2]]

instance Show Interval where
  show int | isBottom int = "[]"
  show (Interval l u)     = "[" ++ show l ++ ".." ++ show u ++ "]"

instance Eq Interval where
  int1 == int2 | isBottom int1, isBottom int2 = True
  Interval l1 u1 == Interval l2 u2            = l1 == l2 && u1 == u2
  
instance Lattice Interval where  
  top = Interval NegInf Inf
  bot = Interval Inf NegInf
  
  join int1 int2 | isBottom int1 = int2
  join int1 int2 | isBottom int2 = int1
  join (Interval l1 u1) (Interval l2 u2) = Interval (min l1 l2) (max u1 u2)

  meet int1 int2 | isBottom int1 = int1
  meet int1 int2 | isBottom int2 = int2
  meet (Interval l1 u1) (Interval l2 u2) = Interval (max l1 l2) (min u1 u2)
  
instance Num Interval where
  int1 + int2 | isBottom int1 || isBottom int2 = bot
  Interval l1 u1 + Interval l2 u2 = Interval (l1 + l2) (u1 + u2)
  
  int1 * int2 | isBottom int1 || isBottom int2 = bot
              | otherwise = Interval (minimum (mapBounds (*) int1 int2)) (maximum (mapBounds (*) int1 int2))
  
  negate (Interval l u) = Interval (-u) (-l)  
  abs int = int
  signum _ = 1
  fromInteger n = Interval (Finite n) (Finite n)

-- | Division on integer intervals
(//) int1 int2 | isBottom int1 || isBottom int2 = bot
               | 0 <: int2 = join (int1 // meet int2 negatives) (int1 // meet int2 positives)
               | otherwise = Interval (minimum (catMaybes (mapBounds (extDiv ceiling) int1 int2))) (maximum (catMaybes (mapBounds (extDiv floor) int1 int2)))
  