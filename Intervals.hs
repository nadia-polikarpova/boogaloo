{- Lattice of integer intervals -}
module Intervals where

-- | Lattice type class 
class Eq a => Lattice a where
  top   :: a
  bot   :: a
  (<:)  :: a -> a -> Bool
  join  :: a -> a -> a
  meet  :: a -> a -> a
  
  x <: y = meet x y == x

-- | Integers extended with infinity
data Extended = NegInf | Finite Integer | Inf
  deriving Eq
  
instance Show Extended where
  show NegInf = "-Infinity"
  show (Finite i) = show i
  show Inf = "Infinity"
  
instance Num Extended where
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

isBottom (Interval l u) = l > u

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
  Interval l1 u1 * Interval l2 u2 = Interval (minimum [l * u | l <- [l1, l2], u <- [u1, u2]]) (maximum [l * u | l <- [l1, l2], u <- [u1, u2]])
  
  negate (Interval l u) = Interval (-u) (-l)  
  abs int = int
  signum _ = 1
  fromInteger n = Interval (Finite n) (Finite n)
