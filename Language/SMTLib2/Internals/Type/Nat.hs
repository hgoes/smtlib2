module Language.SMTLib2.Internals.Type.Nat where

import Data.Typeable
import Data.Constraint
import Data.GADT.Compare
import Data.GADT.Show
import Language.Haskell.TH

-- | Natural numbers on the type-level.
data Nat = Z | S Nat deriving Typeable

-- | A concrete representation of the 'Nat' type.
data Natural (n::Nat) where
  Zero :: Natural Z
  Succ :: Natural n -> Natural (S n)

type family (+) (n :: Nat) (m :: Nat) :: Nat where
  (+) Z n = n
  (+) (S n) m = S ((+) n m)

type family (-) (n :: Nat) (m :: Nat) :: Nat where
  (-) n Z = n
  (-) (S n) (S m) = n - m

type family (<=) (n :: Nat) (m :: Nat) :: Bool where
  (<=) Z m = True
  (<=) (S n) Z = False
  (<=) (S n) (S m) = (<=) n m

naturalToInteger :: Natural n -> Integer
naturalToInteger = conv 0
  where
    conv :: Integer -> Natural m -> Integer
    conv n Zero = n
    conv n (Succ x) = conv (n+1) x

naturalAdd :: Natural n -> Natural m -> Natural (n + m)
naturalAdd Zero n = n
naturalAdd (Succ x) y = Succ (naturalAdd x y)

naturalSub :: Natural (n + m) -> Natural n -> Natural m
naturalSub n Zero = n
naturalSub (Succ sum) (Succ n) = naturalSub sum n

naturalSub' :: Natural n -> Natural m
            -> (forall diff. ((m + diff) ~ n) => Natural diff -> a)
            -> a
naturalSub' n Zero f = f n
naturalSub' (Succ sum) (Succ n) f = naturalSub' sum n f

naturalLEQ :: Natural n -> Natural m -> Maybe (Dict ((n <= m) ~ True))
naturalLEQ Zero _ = Just Dict
naturalLEQ (Succ n) (Succ m) = case naturalLEQ n m of
  Just Dict -> Just Dict
  Nothing -> Nothing
naturalLEQ _ _ = Nothing

instance Show (Natural n) where
  showsPrec p = showsPrec p . naturalToInteger

instance Eq (Natural n) where
  (==) _ _ = True

instance Ord (Natural n) where
  compare _ _ = EQ

-- | Get a static representation for a dynamically created natural number.
--
--   Example:
--
-- >>> reifyNat (S (S Z)) show
-- "2"
reifyNat :: Nat -> (forall n. Natural n -> r) -> r
reifyNat Z f = f Zero
reifyNat (S n) f = reifyNat n $ \n' -> f (Succ n')

-- | A template haskell function to create nicer looking numbers.
--
--   Example:
--
-- >>> :t $(nat 5)
-- $(nat 5) :: Natural ('S ('S ('S ('S ('S 'Z)))))
nat :: (Num a,Ord a) => a -> ExpQ
nat n
  | n < 0 = error $ "nat: Can only use numbers >= 0."
  | otherwise = nat' n
  where
    nat' 0 = [| Zero |]
    nat' n = [| Succ $(nat' (n-1)) |]

-- | A template haskell function to create nicer looking number types.
--
--   Example:
--
-- >>> $(nat 5) :: Natural $(natT 5)
-- 5
natT :: (Num a,Ord a) => a -> TypeQ
natT n
  | n < 0 = error $ "natT: Can only use numbers >= 0."
  | otherwise = natT' n
  where
    natT' 0 = [t| Z |]
    natT' n = [t| S $(natT' (n-1)) |]

instance Eq Nat where
  (==) Z Z = True
  (==) (S x) (S y) = x == y
  (==) _ _ = False

instance Ord Nat where
  compare Z Z = EQ
  compare Z _ = LT
  compare _ Z = GT
  compare (S x) (S y) = compare x y

instance Num Nat where
  (+) Z n = n
  (+) (S n) m = S (n + m)
  (-) n Z = n
  (-) (S n) (S m) = n - m
  (-) _ _ = error $ "Cannot produce negative natural numbers."
  (*) Z n = Z
  (*) (S n) m = m+(n*m)
  negate _ = error $ "Cannot produce negative natural numbers."
  abs = id
  signum Z = Z
  signum (S _) = S Z
  fromInteger x
    | x<0 = error $ "Cannot produce negative natural numbers."
    | otherwise = f x
    where
      f 0 = Z
      f n = S (f (n-1))

instance Enum Nat where
  succ = S
  pred (S n) = n
  pred Z = error $ "Cannot produce negative natural numbers."
  toEnum 0 = Z
  toEnum n = S (toEnum (n-1))
  fromEnum Z = 0
  fromEnum (S n) = (fromEnum n)+1

instance Real Nat where
  toRational Z = 0
  toRational (S n) = (toRational n)+1

instance Integral Nat where
  quotRem x y = let (q,r) = quotRem (toInteger x) (toInteger y)
                in (fromInteger q,fromInteger r)
  toInteger = f 0
    where
      f n Z = n
      f n (S m) = f (n+1) m

type N0  = Z
type N1  = S N0
type N2  = S N1
type N3  = S N2
type N4  = S N3
type N5  = S N4
type N6  = S N5
type N7  = S N6
type N8  = S N7
type N9  = S N8
type N10 = S N9
type N11 = S N10
type N12 = S N11
type N13 = S N12
type N14 = S N13
type N15 = S N14
type N16 = S N15
type N17 = S N16
type N18 = S N17
type N19 = S N18
type N20 = S N19
type N21 = S N20
type N22 = S N21
type N23 = S N22
type N24 = S N23
type N25 = S N24
type N26 = S N25
type N27 = S N26
type N28 = S N27
type N29 = S N28
type N30 = S N29
type N31 = S N30
type N32 = S N31
type N33 = S N32
type N34 = S N33
type N35 = S N34
type N36 = S N35
type N37 = S N36
type N38 = S N37
type N39 = S N38
type N40 = S N39
type N41 = S N40
type N42 = S N41
type N43 = S N42
type N44 = S N43
type N45 = S N44
type N46 = S N45
type N47 = S N46
type N48 = S N47
type N49 = S N48
type N50 = S N49
type N51 = S N50
type N52 = S N51
type N53 = S N52
type N54 = S N53
type N55 = S N54
type N56 = S N55
type N57 = S N56
type N58 = S N57
type N59 = S N58
type N60 = S N59
type N61 = S N60
type N62 = S N61
type N63 = S N62
type N64 = S N63

instance GEq Natural where
  geq Zero Zero = Just Refl
  geq (Succ x) (Succ y) = do
    Refl <- geq x y
    return Refl
  geq _ _ = Nothing

instance GCompare Natural where
  gcompare Zero Zero = GEQ
  gcompare Zero _ = GLT
  gcompare _ Zero = GGT
  gcompare (Succ x) (Succ y) = case gcompare x y of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance GShow Natural where
  gshowsPrec = showsPrec

class IsNatural n where
  getNatural :: Natural n

instance IsNatural Z where
  getNatural = Zero

instance IsNatural n => IsNatural (S n) where
  getNatural = Succ getNatural
