{-# LANGUAGE StandaloneDeriving #-}
module Language.SMTLib2.Internals.Type.Nat where

import Data.Proxy
import Data.Typeable
import Data.Constraint
import Data.GADT.Compare

data Nat = Z | S Nat deriving Typeable

#if __GLASGOW_HASKELL__ < 710
deriving instance Typeable 'Z
deriving instance Typeable 'S
#endif

class Typeable n => KnownNat (n :: Nat) where
  natVal :: p n -> Integer
  natPred :: p n -> Pred n

data Pred (n::Nat) where
   NoPred :: Pred Z
   Pred :: KnownNat n => Proxy n -> Pred (S n)

instance KnownNat Z where
  natVal _ = 0
  natPred _ = NoPred
instance KnownNat n => KnownNat (S n) where
  natVal (_::p (S n)) = succ (natVal (Proxy::Proxy n))
  natPred _ = Pred Proxy

type family (+) (n :: Nat) (m :: Nat) :: Nat where
  (+) Z n = n
  (+) (S n) m = S ((+) n m)

type family (<=) (n :: Nat) (m :: Nat) :: Bool where
  (<=) Z m = True
  (<=) (S n) Z = False
  (<=) (S n) (S m) = (<=) n m

type family Sum (n :: [Nat]) :: Nat where
  Sum '[] = Z
  Sum (a ': b) = a + (Sum b)

sameNat :: (KnownNat a,KnownNat b) => Proxy a -> Proxy b
        -> Maybe (a :~: b)
sameNat _ _ = eqT

gcompareNat :: (KnownNat a,KnownNat b) => Proxy a -> Proxy b -> GOrdering a b
gcompareNat p1 p2 = case sameNat p1 p2 of
  Just Refl -> GEQ
  Nothing -> case compare (natVal p1) (natVal p2) of
    LT -> GLT
    GT -> GGT

reifyNat :: (Num a,Ord a) => a -> (forall n. KnownNat n => Proxy n -> r) -> r
reifyNat n f
  | n < 0 = error "smtlib2: Can only reify numbers >= 0."
  | otherwise = reifyNat' n f
  where
    reifyNat' :: (Num a,Eq a) => a -> (forall n. KnownNat n => Proxy n -> r) -> r
    reifyNat' 0 f' = f' (Proxy::Proxy Z)
    reifyNat' n' f' = reifyNat' (n'-1) (f'.g)

    g :: Proxy n -> Proxy (S n)
    g _ = Proxy

reifyAdd :: (Num a,Ord a) => a -> a -> (forall n1 n2. (KnownNat n1,KnownNat n2,KnownNat (n1 + n2))
                                        => Proxy n1 -> Proxy n2 -> r) -> r
reifyAdd n1 n2 f
  | n1 < 0 || n2 < 0 = error "smtlib2: Can only reify numbers >= 0."
  | otherwise = reifyAdd' n1 n2 f
  where
    reifyAdd' :: (Num a,Ord a) => a -> a
                 -> (forall n1 n2. (KnownNat n1,KnownNat n2,KnownNat (n1 + n2))
                     => Proxy n1 -> Proxy n2 -> r) -> r
    reifyAdd' 0 n2' f' = reifyNat n2' $ \(_::Proxy i) -> f' (Proxy::Proxy Z) (Proxy::Proxy i)
    reifyAdd' n1' n2' f' = reifyAdd' (n1'-1) n2' $
                           \(_::Proxy i1) (_::Proxy i2)
                           -> f' (Proxy::Proxy (S i1)) (Proxy::Proxy i2)

reifyExtract :: (Num a,Ord a) => a -> a -> a
             -> (forall start len size.
                 (KnownNat start,KnownNat len,KnownNat size,
                  ((start + len) <= size) ~ True) =>
                 Proxy start -> Proxy len -> Proxy size -> r)
             -> Maybe r
reifyExtract start len sz f
  | start < 0 || len < 0 || sz < 0 || start+len > sz = Nothing
  | otherwise = Just $ reifyExtract' start len sz f
  where
    reifyExtract' :: (Num a,Ord a) => a -> a -> a
                  -> (forall start len size.
                      (KnownNat start,KnownNat len,KnownNat size,
                       ((start + len) <= size) ~ True) =>
                      Proxy start -> Proxy len -> Proxy size -> r)
                  -> r
    reifyExtract' 0 len sz f
      = reifyLeq len sz $
        \plen psz -> f (Proxy::Proxy Z) plen psz
    reifyExtract' start len sz f
      = reifyExtract' (start-1) len (sz-1) $
        \(_::Proxy start) plen (_::Proxy sz)
         -> f (Proxy::Proxy (S start)) plen (Proxy::Proxy (S sz))
    reifyLeq :: (Num a,Ord a) => a -> a
             -> (forall n1 n2. (KnownNat n1,KnownNat n2,(n1 <= n2) ~ True)
                 => Proxy n1 -> Proxy n2 -> r) -> r
    reifyLeq 0 sz f = reifyNat sz $
                      \pr -> f (Proxy::Proxy Z) pr
    reifyLeq len sz f = reifyLeq (len-1) (sz-1) $
                        \(_::Proxy len) (_::Proxy sz)
                         -> f (Proxy::Proxy (S len)) (Proxy::Proxy (S sz))

deriveAdd :: (KnownNat n1,KnownNat n2) => Proxy n1 -> Proxy n2 -> Dict (KnownNat (n1 + n2))
deriveAdd (n1::Proxy n1) (n2::Proxy n2) = reifyAdd (natVal n1) (natVal n2) $
                  \(_::Proxy n1') (_::Proxy n2') -> case eqT of
                     Just (Refl::n1 :~: n1') -> case eqT of
                       Just (Refl::n2 :~: n2') -> Dict

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

