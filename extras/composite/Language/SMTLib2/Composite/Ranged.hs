{-# LANGUAGE KindSignatures,DataKinds,GADTs,TypeFamilies,StandaloneDeriving,MultiWayIf #-}
{- | A value bounded by static bounds. -}
module Language.SMTLib2.Composite.Ranged
  (Ranged(..),
   -- * Range
   Range(..),
   rangeType,
   unionRange,intersectionRange,
   rangeFixpoint,
   isConst,
   includes,
   fullRange,
   emptyRange,
   isEmptyRange,
   singletonRange,
   ltRange,leqRange,gtRange,geqRange,
   betweenRange,
   -- * Functions
   rangedITE,
   rangedConst,
   rangeInvariant,
   Bounds,Inf(..),
   toBounds,fromBounds
  ) where

import Language.SMTLib2.Composite.Class
import Language.SMTLib2
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type (bvPred,bvSucc)
import Data.GADT.Compare
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Constraint

newtype Ranged (tp :: Type) e = Ranged { getRanged :: e tp }

-- | The boolean states if the range starts included (True) or not (False).
--   Invariant: The range elements are sorted ascending.
type IntRange = (Bool,[Integer])

-- | Describes the allowed values that an expression may have.
--   BoolRange x y describes if value False is allowed (x) and if value True is allowed (y).
data Range tp where
  BoolRange :: Bool -> Bool -> Range BoolType
  IntRange :: IntRange -> Range IntType
  BitVecRange :: Natural bw -> [(Integer,Integer)] -> Range (BitVecType bw)

deriving instance Eq (Range tp)
deriving instance Show (Range tp)

instance Ord (Range tp) where
  compare (BoolRange f1 t1) (BoolRange f2 t2) = compare (f1,t1) (f2,t2)
  compare (IntRange x) (IntRange y) = compare x y
  compare (BitVecRange _ rx) (BitVecRange _ ry) = compare rx ry

instance Composite (Ranged tp) where
  type CompDescr (Ranged tp) = Range tp
  type RevComp (Ranged tp) = (:~:) tp
  compositeType (BoolRange _ _) = Ranged bool
  compositeType (IntRange _) = Ranged int
  compositeType (BitVecRange bw _) = Ranged (bitvec bw)
  foldExprs f (Ranged e) = do
    ne <- f Refl e
    return $ Ranged ne
  accessComposite Refl (Ranged e) = Just e

instance CompositeExtract (Ranged tp) where
  type CompExtract (Ranged tp) = Value tp
  compExtract f (Ranged x) = f x

unionRange :: Range tp -> Range tp -> Range tp
unionRange (BoolRange f1 t1) (BoolRange f2 t2) = BoolRange (f1 || f2) (t1 || t2)
unionRange (IntRange x) (IntRange y) = IntRange (unionIntRange x y)
  where
    unionIntRange :: IntRange -> IntRange -> IntRange
    unionIntRange (False,[]) ys = ys
    unionIntRange (True,[]) _ = (True,[])
    unionIntRange xs (False,[]) = xs
    unionIntRange _ (True,[]) = (True,[])
    unionIntRange (False,xs) (False,ys)
      = (False,unionIntRange' xs ys)
    unionIntRange (xi,x:xs) (yi,y:ys)
      = (True,filterRange zs)
      where
        (z,zs)
          | xi && yi = (max x y,unionIntRange' xs ys)
          | xi       = (x,unionIntRange' xs (y:ys))
          | yi       = (y,unionIntRange' (x:xs) ys)
        filterRange [] = [z]
        filterRange (l:u:rest) = if l <= z-1
                                 then if u>z
                                      then u:rest
                                      else filterRange rest
                                 else z:l:u:rest

    unionIntRange' :: [Integer] -> [Integer] -> [Integer]
    unionIntRange' [] ys = ys
    unionIntRange' xs [] = xs
    unionIntRange' (xl:xu:xs) (yl:yu:ys)
      | xu < yl-1 = xl:xu:unionIntRange' xs (yl:yu:ys)
      | yu < xl-1 = yl:yu:unionIntRange' (xl:xu:xs) ys
      | otherwise = unionIntRange' (min xl yl:max xu yu:xs) ys
    unionIntRange' [x] [y] = [min x y]
    unionIntRange' [x] (yl:yu:ys)
      | yu < x-1 = yl:yu:unionIntRange' [x] ys
      | otherwise = [min x yl]
    unionIntRange' (xl:xu:xs) [y]
      | xu < y-1 = xl:xu:unionIntRange' xs [y]
      | otherwise = [min xl y]
unionRange (BitVecRange bw xr) (BitVecRange _ yr)
  = BitVecRange bw (unionRange' xr yr)
  where
    unionRange' [] yr = yr
    unionRange' xr [] = xr
    unionRange' (x@(xlower,xupper):xs) (y@(ylower,yupper):ys)
      | xupper < ylower-1 = x:unionRange' xs (y:ys)
      | yupper < xlower-1 = y:unionRange' (x:xs) ys
      | otherwise = unionRange' ((min xlower ylower,max xupper yupper):xs) ys

intersectionRange :: Range tp -> Range tp -> Range tp
intersectionRange (BoolRange f1 t1) (BoolRange f2 t2)
  = BoolRange (f1 && f2) (t1 && t2)
intersectionRange (IntRange x) (IntRange y) = IntRange (intersectionIntRange x y)
  where
    intersectionIntRange :: IntRange -> IntRange -> IntRange
    intersectionIntRange (True,[]) ys = ys
    intersectionIntRange xs (True,[]) = xs
    intersectionIntRange (True,u1:r1) (True,u2:r2)
      = if u1 > u2
        then (True,u2:intersectionIntRange' (u2:u1:r1) r2)
        else (True,u1:intersectionIntRange' r1 (u1:u2:r2))
    intersectionIntRange (True,u1:r1) (False,l2:r2)
      = if u1 < l2
        then (False,intersectionIntRange' r1 (l2:r2))
        else (False,intersectionIntRange' (l2:u1:r1) (l2:r2))
    intersectionIntRange (False,l1:r1) (True,u2:r2)
      = if u2 < l1
        then (False,intersectionIntRange' (l1:r1) r2)
        else (False,intersectionIntRange' (l1:r1) (l1:u2:r2))
    intersectionIntRange (False,[]) _ = (False,[])
    intersectionIntRange _ (False,[]) = (False,[])
    intersectionIntRange (False,r1) (False,r2)
      = (False,intersectionIntRange' r1 r2)

    intersectionIntRange' [] _ = []
    intersectionIntRange' _ [] = []
    intersectionIntRange' [l1] [l2] = [max l1 l2]
    intersectionIntRange' [l1] (l2:u2:r2)
      = if l1 > u2
        then intersectionIntRange' [l1] r2
        else max l1 l2:u2:r2
    intersectionIntRange' (l1:u1:r1) [l2]
      = if l2 > u1
        then intersectionIntRange' r1 [l2]
        else max l1 l2:u1:r1
    intersectionIntRange' (l1:u1:r1) (l2:u2:r2)
      | u1 < l2   = intersectionIntRange' r1 (l2:u2:r2)
      | u2 < l1   = intersectionIntRange' (l1:u1:r1) r2
      | otherwise = max l1 l2:min u1 u2:case compare u1 u2 of
          LT -> intersectionIntRange' r1 (u1:u2:r2)
          EQ -> intersectionIntRange' r1 r2
          GT -> intersectionIntRange' (u2:u1:r1) r2
intersectionRange (BitVecRange bw x) (BitVecRange _ y)
  = BitVecRange bw (intersectionBV x y)
  where
    intersectionBV [] _ = []
    intersectionBV _ [] = []
    intersectionBV ((l1,u1):r1) ((l2,u2):r2)
      | u1 < l2 = intersectionBV r1 ((l2,u2):r2)
      | u2 < l1 = intersectionBV ((l1,u1):r1) r2
      | otherwise = (max l1 l2,min u1 u2):case compare u1 u2 of
          LT -> intersectionBV r1 ((u1,u2):r2)
          EQ -> intersectionBV r1 r2
          GT -> intersectionBV ((u2,u1):r1) r2

rangedITE :: Embed m e => e BoolType -> Ranged tp e -> Ranged tp e -> m (Ranged tp e)
rangedITE c (Ranged ifT) (Ranged ifF) = do
  res <- ite c ifT ifF
  return $ Ranged res

rangedConst :: Value tp -> Range tp
rangedConst (BoolValue b) = BoolRange (not b) b
rangedConst (IntValue i) = IntRange (False,[i,i])
rangedConst (BitVecValue i bw) = BitVecRange bw [(i,i)]

isConst :: Range tp -> Maybe (Value tp)
isConst (BoolRange True False) = Just (BoolValue False)
isConst (BoolRange False True) = Just (BoolValue True)
isConst (IntRange (False,[i,j]))
  | i==j = Just (IntValue i)
isConst (BitVecRange bw [(i,j)])
  | i==j = Just (BitVecValue i bw)
isConst _ = Nothing

rangeInvariant :: Embed m e => Range tp -> e tp -> m (e BoolType)
rangeInvariant (BoolRange True True) _ = true
rangeInvariant (BoolRange False False) _ = false
rangeInvariant (BoolRange True False) e = not' e
rangeInvariant (BoolRange False True) e = return e
rangeInvariant (IntRange r) e = rangeInvariant' (\isLE c -> if isLE then e .<=. cint c else e .>=. cint c) r
rangeInvariant (BitVecRange bw r) e = do
  conds <- mapM (\(lower,upper) -> do
                    lowerCond <- if lower==0
                                 then return []
                                 else do
                      cond <- e `bvuge` cbv lower bw
                      return [cond]
                    upperCond <- if upper==2^bw'-1
                                 then return []
                                 else do
                      cond <- e `bvule` cbv upper bw
                      return [cond]
                    case lowerCond++upperCond of
                      [] -> true
                      [c] -> return c
                      xs -> and' xs
                ) r
  case conds of
    [] -> false
    [c] -> return c
    xs -> or' xs
  where
    bw' = naturalToInteger bw

rangeInvariant' :: Embed m e => (Bool -> Integer -> m (e BoolType)) -- ^ First parameter decides if the operator is <=x (True) or >=x (False).
                -> IntRange
                -> m (e BoolType)
rangeInvariant' f (c,xs) = if c then case xs of
  [] -> true
  x:xs' -> do
    conj <- mk xs'
    el <- f True x
    case conj of
      [] -> return el
      _  -> or' (el:conj)
  else do
  conj <- mk xs
  case conj of
    [] -> false
    [x] -> return x
    _ -> or' conj
  where
    mk (l:u:xs) = do
      e <- (f False l) .&. (f True u)
      es <- mk xs
      return (e:es)
    mk [l] = do
      e <- f False l
      return [e]
    mk [] = return []

lowerIntBound :: IntRange -> Maybe (Integer,Bool)
lowerIntBound (incl,x:xs) = Just (x,incl)
lowerIntBound (_,[]) = Nothing

upperIntBound :: IntRange -> Maybe (Integer,Bool)
upperIntBound (_,[]) = Nothing
upperIntBound (incl,xs) = Just $ upper incl xs
  where
    upper incl [i] = (i,not incl)
    upper incl (_:is) = upper (not incl) is

extendLowerIntBound :: IntRange -> IntRange
extendLowerIntBound (False,[]) = (True,[])
extendLowerIntBound (False,_:xs) = (True,xs)
extendLowerIntBound (True,[]) = (True,[])
extendLowerIntBound (True,[_]) = (True,[])
extendLowerIntBound (True,u:l:xs) = (True,xs)

extendUpperIntBound :: IntRange -> IntRange
extendUpperIntBound (False,[]) = (True,[])
extendUpperIntBound (False,[_]) = (True,[])
extendUpperIntBound (incl,xs) = (incl,extend incl xs)
  where
    extend True [u] = []
    extend True [u,l] = []
    extend incl (x:xs) = x:extend (not incl) xs

rangeFixpoint :: Range tp -> Range tp -> Range tp
rangeFixpoint _ (BoolRange f t) = BoolRange f t
rangeFixpoint (IntRange r1) (IntRange r2) = IntRange r3
  where
    r3' = if lowerIntBound r1 == lowerIntBound r2
          then r2
          else extendLowerIntBound r2
    r3 = if upperIntBound r1 == upperIntBound r2
         then r3'
         else extendUpperIntBound r3'
rangeFixpoint (BitVecRange bw []) (BitVecRange _ r2) = BitVecRange bw r2
rangeFixpoint (BitVecRange bw r1) (BitVecRange _ []) = BitVecRange bw r1
rangeFixpoint (BitVecRange bw r1) (BitVecRange _ r2)
  = BitVecRange bw $ fixEnd r1 (fixStart r1 r2)
  where
    fixStart ((l1,u1):r1) ((l2,u2):r2)
      | l1==l2 = (l2,u2):r2
      | otherwise = (0,u2):r2

    fixEnd [(l1,u1)] [(l2,u2)]
      | u1==u2 = [(l2,u2)]
      | otherwise = [(l2,2^(naturalToInteger bw)-1)]
    fixEnd (x:xs) [y] = fixEnd xs [y]
    fixEnd [x] (y:ys) = y:fixEnd [x] ys
    fixEnd (_:xs) (y:ys) = y:fixEnd xs ys

intRangeIncludes :: Integer -> IntRange -> Bool
intRangeIncludes _ (incl,[]) = incl
intRangeIncludes n (False,l:xs)
  | n < l = False
  | otherwise = intRangeIncludes n (True,xs)
intRangeIncludes n (True,u:xs)
  | n <= u = True
  | otherwise = intRangeIncludes n (False,xs)

includes :: Value tp -> Range tp -> Bool
includes (BoolValue v) (BoolRange f t) = if v then t else f
includes (IntValue v) (IntRange r) = intRangeIncludes v r
--includes (BitVecValue v _) (BitVecRange _ _ r) = intRangeIncludes v r

fullRange :: Repr tp -> Range tp
fullRange BoolRepr        = BoolRange True True
fullRange IntRepr         = IntRange (True,[])
fullRange (BitVecRepr bw) = BitVecRange bw [(0,2^(naturalToInteger bw)-1)]

emptyRange :: Repr tp -> Range tp
emptyRange BoolRepr        = BoolRange False False
emptyRange IntRepr         = IntRange (False,[])
emptyRange (BitVecRepr bw) = BitVecRange bw []

isEmptyRange :: Range tp -> Bool
isEmptyRange (BoolRange False False) = True
isEmptyRange (IntRange (False,[])) = True
isEmptyRange (BitVecRange _ []) = True
isEmptyRange _ = False

singletonRange :: Value tp -> Range tp
singletonRange (BoolValue b) = BoolRange (not b) b
singletonRange (IntValue v) = IntRange (False,[v,v])
singletonRange (BitVecValue v bw) = BitVecRange bw [(v,v)]

leqRange :: Integer -> Range IntType
leqRange x = IntRange (True,[x])

ltRange :: Integer -> Range IntType
ltRange x = IntRange (True,[x-1])

geqRange :: Integer -> Range IntType
geqRange x = IntRange (False,[x])

gtRange :: Integer -> Range IntType
gtRange x = IntRange (False,[x+1])

intersectionIntRange :: IntRange -> IntRange -> IntRange
intersectionIntRange (False,[]) _ = (False,[])
intersectionIntRange _ (False,[]) = (False,[])
intersectionIntRange (True,[]) ys = ys
intersectionIntRange xs (True,[]) = xs
intersectionIntRange (False,xs) (False,ys)
  = (False,intersectionIntRange' xs ys)
--intersectionIntRange (True,x:xs) (True,y:ys) = case compare x y of
--  EQ -> (True,x:intersectionIntRange' 

intersectionIntRange' :: [Integer] -> [Integer] -> [Integer]
intersectionIntRange' [] _ = []
intersectionIntRange' _ [] = []
intersectionIntRange' (xl:xu:xs) (yl:yu:ys)
  | xu < yl-1 = intersectionIntRange' xs (yl:yu:ys)
  | yu < xl-1 = intersectionIntRange' (xl:xu:xs) ys
  | otherwise = max xl yl:min xu yu:
                case compare xu yu of
                  EQ -> intersectionIntRange' xs ys
                  LT -> intersectionIntRange' xs (xu:yu:ys)
                  GT -> intersectionIntRange' (yu:xu:xs) ys

rangeType :: Range tp -> Repr tp
rangeType (BoolRange _ _) = bool
rangeType (IntRange _) = int
rangeType (BitVecRange bw _) = bitvec bw

-- To support easier manipulation of ranges, we introduce the Bounds type:

--type Bounds = Maybe (Maybe Integer,[(Integer,Integer)],Maybe Integer)

data Inf x = NegInfinity | Regular x | PosInfinity deriving (Eq,Ord,Show,Functor)

type Bounds x = [(Inf x,Inf x)]

instance (Ord x,Num x) => Num (Inf x) where
  fromInteger = Regular . fromInteger
  (+) (Regular x) (Regular y) = Regular $ x+y
  (+) NegInfinity PosInfinity = error "Adding positive and negative infinity undefined."
  (+) PosInfinity NegInfinity = error "Adding positive and negative infinity undefined."
  (+) PosInfinity _ = PosInfinity
  (+) NegInfinity _ = NegInfinity
  (+) _ PosInfinity = PosInfinity
  (+) _ NegInfinity = NegInfinity
  (-) (Regular x) (Regular y) = Regular $ x-y
  (-) NegInfinity NegInfinity = error "Subtracting negative infinity from negative infinity undefined."
  (-) PosInfinity PosInfinity = error "Subtracting positive infinity from positity infinity undefined."
  (-) NegInfinity _ = NegInfinity
  (-) PosInfinity _ = PosInfinity
  (-) _ NegInfinity = PosInfinity
  (-) _ PosInfinity = NegInfinity
  (*) (Regular x) (Regular y) = Regular $ x*y
  (*) (Regular 0) _ = 0
  (*) _ (Regular 0) = 0
  (*) PosInfinity y = if y > 0
                      then PosInfinity
                      else NegInfinity
  (*) x PosInfinity = if x > 0
                      then PosInfinity
                      else NegInfinity
  (*) NegInfinity y = if y < 0
                      then PosInfinity
                      else NegInfinity
  (*) x NegInfinity = if x < 0
                      then PosInfinity
                      else NegInfinity
  negate (Regular x) = Regular $ negate x
  negate NegInfinity = PosInfinity
  negate PosInfinity = NegInfinity
  abs (Regular x) = Regular $ abs x
  abs _ = PosInfinity
  signum (Regular x) = Regular $ signum x
  signum PosInfinity = 1
  signum NegInfinity = -1

instance Real x => Real (Inf x) where
  toRational NegInfinity = error "toRational.{Inf x}: called on negative infinity"
  toRational (Regular x) = toRational x
  toRational PosInfinity = error "toRational.{Inf x}: called on positive infinity"

instance Enum x => Enum (Inf x) where
  succ NegInfinity = NegInfinity
  succ (Regular x) = Regular (succ x)
  succ PosInfinity = PosInfinity
  pred NegInfinity = NegInfinity
  pred (Regular x) = Regular (pred x)
  pred PosInfinity = PosInfinity
  toEnum x = Regular (toEnum x)
  fromEnum NegInfinity = error "fromEnum.{Inf x}: called on negative infinity"
  fromEnum (Regular x) = fromEnum x
  fromEnum PosInfinity = error "fromEnum.{Inf x}: called on positive infinity"

{-instance Integral x => Integral (Inf x) where
  quot NegInfinity (Regular y) = case compare y 0 of
    LT -> PosInfinity
    EQ -> error "quot{Inf}: divide by zero"
    GT -> NegInfinity
  quot PosInfinity (Regular y) = case compare y 0 of
    LT -> NegInfinity
    EQ -> error "quot{Inf}: divide by zero"
    GT -> PosInfinity
  quot (Regular x) (Regular y) = Regular (x `quot` y)
  quot (Regular _) PosInfinity = Regular 0
  quot (Regular _) NegInfinity = Regular 0
  quot _ _ = error "quot{Inf}: two infinite arguments"
  rem (Regular x) (Regular y) = Regular (x `rem` y)
  rem PosInfinity _ = error "rem{Inf}: first argument cannot be infinite."
  rem NegInfinity _ = error "rem{Inf}: first argument cannot be infinite."
  rem (Regular x) PosInfinity = Regular x
  rem (Regular x) NegInfinity = Regular x
  div (Regular x) (Regular y) = Regular (x `div` y)
  div PosInfinity (Regular x) = case compare x 0 of
    LT -> NegInfinity
    EQ -> error "div{Inf}: divide by zero"
    GT -> PosInfinity
  div NegInfinity (Regular x) = case compare x 0 of
    LT -> PosInfinity
    EQ -> error "div{Inf}: divide by zero"
    GT -> NegInfinity
  div (Regular x) PosInfinity = if x>=0
                                then Regular 0
                                else Regular (-1)
  div (Regular x) NegInfinity = if x>0
                                then Regular (-1)
                                else Regular 0
  div _ _ = error "div{Inf}: two infinite arguments"
  mod (Regular x) (Regular y) = Regular (x `mod` y)
  mod (Regular x) PosInfinity = if x>=0
                                then Regular x
                                else error "mod{Inf}: undefined for negative first parameter and positive infinity second parameter"
  mod (Regular x) NegInfinity = if x<=0
                                then Regular x
                                else error "mod{Inf}: undefined for positive first parameter and negative infinity second parameter"
  mod _ _ = error "mod{Inf}: undefined"-}

toBounds :: Range tp -> Bounds (Value tp)
toBounds (BoolRange True True) = [(Regular $ BoolValue False,Regular $ BoolValue True)]
toBounds (BoolRange f t) = (if f then [(Regular $ BoolValue False,Regular $ BoolValue False)] else [])++
                           (if t then [(Regular $ BoolValue True,Regular $ BoolValue True)] else [])
toBounds (IntRange r) = case r of
  (True,[]) -> [(NegInfinity,PosInfinity)]
  (True,x:xs) -> (NegInfinity,Regular $ IntValue x):toBounds' xs
  (False,xs) -> toBounds' xs
  where
    toBounds' :: [Integer] -> Bounds (Value IntType)
    toBounds' [] = []
    toBounds' [lower] = [(Regular $ IntValue lower,PosInfinity)]
    toBounds' (lower:upper:xs) = (Regular $ IntValue lower,Regular $ IntValue upper):toBounds' xs
toBounds (BitVecRange bw rng) = [(Regular $ BitVecValue lower bw,
                                  Regular $ BitVecValue upper bw)
                                | (lower,upper) <- rng]

fromBounds :: Repr tp -> Bounds (Value tp) -> Range tp
fromBounds tp bnd = case tp of
  BoolRepr -> boolRange False bnd''
  IntRepr -> intRange bnd''
  BitVecRepr bw -> bvRange bw bnd''
  where
    bnd' = sortBy (comparing fst) bnd
    bnd'' = mergeBounds prev bnd
    prev = case tp of
      BoolRepr -> pred
      IntRepr -> pred
      RealRepr -> id
      BitVecRepr _ -> bvPred
    mergeBounds :: Ord a => (a -> a) -> Bounds a -> Bounds a
    mergeBounds _ [] = []
    mergeBounds _ [x] = [x]
    mergeBounds f ((NegInfinity,NegInfinity):xs) = mergeBounds f xs
    mergeBounds f ((PosInfinity,PosInfinity):xs) = mergeBounds f xs
    mergeBounds f ((l1,u1):(l2,u2):xs)
      | l1 > u1       = mergeBounds f ((l2,u2):xs)
      | l2 > u2       = mergeBounds f ((l1,u1):xs)
      | u1>=fmap f l2 = mergeBounds f ((l1,max u1 u2):xs)
      | otherwise     = (l1,u1):mergeBounds f ((l2,u2):xs)
    boolRange :: Bool -> Bounds (Value BoolType) -> Range BoolType
    boolRange hasF [] = BoolRange hasF False
    boolRange _ ((NegInfinity,PosInfinity):_) = BoolRange True True
    boolRange _ ((NegInfinity,Regular (BoolValue x)):xs)
      = if x
        then BoolRange True True
        else boolRange True xs
    boolRange hasF ((Regular (BoolValue x),PosInfinity):xs)
      = BoolRange (hasF && not x) True
    boolRange hasF ((Regular (BoolValue l),Regular (BoolValue u)):xs)
      = if u
        then BoolRange (hasF || not l) True
        else boolRange True xs
             
    intRange :: Bounds (Value IntType) -> Range IntType
    intRange [] = IntRange (False,[])
    intRange [(NegInfinity,PosInfinity)] = IntRange (True,[])
    intRange ((NegInfinity,Regular (IntValue x)):xs) = IntRange (True,x:intRange' xs)
    intRange xs = IntRange (False,intRange' xs)

    intRange' :: Bounds (Value IntType) -> [Integer]
    intRange' [] = []
    intRange' [(Regular (IntValue x),PosInfinity)] = [x]
    intRange' ((Regular (IntValue l),Regular (IntValue u)):xs) = l:u:intRange' xs

    bvRange :: Natural bw -> Bounds (Value (BitVecType bw)) -> Range (BitVecType bw)
    bvRange bw xs = BitVecRange bw (bvRange' (naturalToInteger bw) xs)

    bvRange' :: Integer -> Bounds (Value (BitVecType bw)) -> [(Integer,Integer)]
    bvRange' _ [] = []
    bvRange' bw ((NegInfinity,PosInfinity):_) = [(0,2^bw-1)]
    bvRange' bw ((NegInfinity,Regular (BitVecValue u _)):xs)
      | u >= 0 = (0,u):bvRange' bw xs
      | otherwise = bvRange' bw xs
    bvRange' bw ((Regular (BitVecValue l _),PosInfinity):_)
      | l < 2^bw = [(l,2^bw-1)]
      | otherwise = []
    bvRange' bw ((Regular (BitVecValue l _),Regular (BitVecValue u _)):xs)
      | u < 0 || l >= 2^bw = bvRange' bw xs
      | otherwise          = (max l 0,min u (2^bw-1)):bvRange' bw xs

addOverflow :: (Num a,Ord a) => a -> a -> (a,Bool)
addOverflow x y = (sum,overf)
  where
    sum = x + y
    overf = if x >= 0
            then sum < y
            else sum > y

multOverflow :: (Integral a,Eq a) => a -> a -> (a,Bool)
multOverflow x y = (prod,prod `div` y /= x)
  where
    prod = x * y

addBounds :: (Num a,Ord a) => Maybe a -> Bounds a -> Bounds a -> Bounds a
addBounds lim b1 b2 = [ r
                      | r1 <- b1
                      , r2 <- b2
                      , r <- addRange lim r1 r2 ]

addRange :: (Num a,Ord a) => Maybe a -> (Inf a,Inf a) -> (Inf a,Inf a) -> [(Inf a,Inf a)]
addRange (Just lim) (l1,u1) (l2,u2)
  | overfL = [(nl,nu)]
  | overfU = if nl <= nu
             then [(0,Regular lim)]
             else [(0,nu),(nl,Regular lim)]
  | otherwise = [(nl,nu)]
  where
    (nl,overfL) = addOverflow l1 l2
    (nu,overfU) = addOverflow u1 u2
addRange Nothing (l1,u1) (l2,u2)
  = [(l1+l2,u1+u2)]

subBounds :: (Num a,Ord a) => Maybe a -> Bounds a -> Bounds a -> Bounds a
subBounds lim b1 b2 = [ r
                      | r1 <- b1
                      , r2 <- b2
                      , r <- addRange lim r1 (negRange r2) ]
  where
    negRange :: (Num a,Ord a) => (Inf a,Inf a) -> (Inf a,Inf a)
    negRange (l,u) = (-u,-l)

multBounds :: (Integral a,Ord a) => Maybe a -> Bounds a -> Bounds a -> Bounds a
multBounds lim b1 b2 = [ r | r1 <- b1
                           , r2 <- b2
                           , r <- multRange lim r1 r2 ]
  where
    multRange :: (Integral a,Ord a) => Maybe a -> (Inf a,Inf a) -> (Inf a,Inf a) -> [(Inf a,Inf a)]
    multRange (Just lim) (Regular l1,Regular u1) (Regular l2,Regular u2)
      | overfL || overfU = [(0,Regular lim)]
      | otherwise = [(Regular nl,Regular nu)]
      where
        (nl,overfL) = multOverflow l1 l2
        (nu,overfU) = multOverflow u1 u2
    multRange Nothing (l1,u1) (l2,u2) = [(l1*l2,u1*u2)]

negBounds :: (Num a,Ord a) => Bounds a -> Bounds a
negBounds = reverse . fmap neg
  where
    neg (l,u) = (negate u,negate l)

absBounds :: (Num a,Ord a) => Bounds a -> Bounds a
absBounds = fmap abs'
  where
    abs' (l,u)
      | l >= 0    = (l,u)
      | u >= 0    = (0,u)
      | otherwise = (abs u,abs l)

signumBounds :: (Num a,Ord a) => Bounds a -> Bounds a
signumBounds = sign False False False
  where
    sign True True True _     = [(-1,1)]
    sign True True False []   = [(-1,0)]
    sign True False True []   = [(-1,-1),(1,1)]
    sign True False False []  = [(-1,-1)]
    sign False True True []   = [(0,1)]
    sign False True False []  = [(0,0)]
    sign False False True []  = [(1,1)]
    sign False False False [] = []
    sign hasN hasZ hasP ((l,u):xs)
      = case compare l 0 of
          LT -> case compare u 0 of
            LT -> sign True hasZ hasP xs
            EQ -> sign True True hasP xs
            GT -> sign True True True xs
          EQ -> case compare u 0 of
            EQ -> sign hasN True hasP xs
            GT -> sign hasN True True xs
          GT -> sign hasN hasZ True xs

instance Num (Range IntType) where
  (+) r1 r2 = fromBounds int $ addBounds Nothing (toBounds r1) (toBounds r2)
  (-) r1 r2 = fromBounds int $ subBounds Nothing (toBounds r1) (toBounds r2)
  (*) r1 r2 = fromBounds int $ multBounds Nothing (toBounds r1) (toBounds r2)
  negate r = fromBounds int $ negBounds (toBounds r)
  abs r = fromBounds int $ absBounds (toBounds r)
  signum r = fromBounds int $ signumBounds (toBounds r)
  fromInteger x = IntRange (False,[x,x])

instance IsNatural bw => Num (Range (BitVecType bw)) where
  (+) r1@(BitVecRange bw _) r2 = fromBounds (bitvec bw) $ addBounds (Just maxBound) (toBounds r1) (toBounds r2)
  (-) r1@(BitVecRange bw _) r2 = fromBounds (bitvec bw) $ subBounds (Just maxBound) (toBounds r1) (toBounds r2)
  (*) r1@(BitVecRange bw _) r2 = fromBounds (bitvec bw) $ multBounds (Just maxBound) (toBounds r1) (toBounds r2)
  negate r@(BitVecRange bw _) = fromBounds (bitvec bw) $ negBounds (toBounds r)
  abs r@(BitVecRange bw _) = fromBounds (bitvec bw) $ absBounds (toBounds r)
  signum r@(BitVecRange bw _) = fromBounds (bitvec bw) $ signumBounds (toBounds r)
  fromInteger x = BitVecRange getNatural [(x,x)]

betweenBounds :: Ord a => Bounds a -> Bounds a -> Bounds a
betweenBounds b1 b2 = [ (min l1 l2,max u1 u2)
                      | (l1,u1) <- b1, (l2,u2) <- b2 ]

betweenRange :: Range tp -> Range tp -> Range tp
betweenRange r1 r2 = fromBounds (rangeType r1) $ betweenBounds (toBounds r1) (toBounds r2)
