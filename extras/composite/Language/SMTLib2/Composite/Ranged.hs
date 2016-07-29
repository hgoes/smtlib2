{-# LANGUAGE KindSignatures,DataKinds,GADTs,TypeFamilies,StandaloneDeriving,MultiWayIf #-}
{- | A value bounded by static bounds. -}
module Language.SMTLib2.Composite.Ranged
  (Ranged(..),
   -- * Range
   Range(..),
   rangeType,
   unionRange,
   rangeFixpoint,
   isConst,
   includes,
   fullRange,
   emptyRange,
   singletonRange,
   ltRange,leqRange,gtRange,geqRange,
   -- * Functions
   rangedITE,
   rangedConst,
   rangeInvariant
  ) where

import Language.SMTLib2.Composite.Class
import Language.SMTLib2
import Data.GADT.Compare
import Data.List (sortBy)
import Data.Ord (comparing)

newtype Ranged (tp :: Type) e = Ranged { getRanged :: e tp }

-- | The boolean states if the range starts included (True) or not (False).
--   Invariant: The range elements are sorted ascending.
type IntRange = (Bool,[Integer])

-- | Describes the allowed values that an expression may have.
--   BoolRange x y describes if value False is allowed (x) and if value True is allowed (y).
data Range tp where
  BoolRange :: Bool -> Bool -> Range BoolType
  IntRange :: IntRange -> Range IntType
  BitVecRange :: Natural bw -> Bool -> IntRange -> Range (BitVecType bw)

deriving instance Eq (Range tp)
deriving instance Show (Range tp)

instance Ord (Range tp) where
  compare (BoolRange f1 t1) (BoolRange f2 t2) = compare (f1,t1) (f2,t2)
  compare (IntRange x) (IntRange y) = compare x y
  compare (BitVecRange _ sx rx) (BitVecRange _ sy ry)
    = compare (sx,rx) (sy,ry)

instance Composite (Ranged tp) where
  type CompDescr (Ranged tp) = Range tp
  type RevComp (Ranged tp) = (:~:) tp
  compositeType (BoolRange _ _) = Ranged bool
  compositeType (IntRange _) = Ranged int
  compositeType (BitVecRange bw _ _) = Ranged (bitvec bw)
  foldExprs f (Ranged e) = do
    ne <- f Refl e
    return $ Ranged ne
  accessComposite Refl (Ranged e) = Just e

instance CompositeExtract (Ranged tp) where
  type CompExtract (Ranged tp) = Value tp
  compExtract f (Ranged x) = f x

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

unionRange :: Range tp -> Range tp -> Range tp
unionRange (BoolRange f1 t1) (BoolRange f2 t2) = BoolRange (f1 || f2) (t1 || t2)
unionRange (IntRange x) (IntRange y) = IntRange (unionIntRange x y)
unionRange (BitVecRange bw xs xr) (BitVecRange _ ys yr)
  | xs==ys = BitVecRange bw xs (unionIntRange xr yr)
  | otherwise = error "Cannot union ranges for signed and unsigned bitvectors."

rangedITE :: Embed m e => e BoolType -> Ranged tp e -> Ranged tp e -> m (Ranged tp e)
rangedITE c (Ranged ifT) (Ranged ifF) = do
  res <- ite c ifT ifF
  return $ Ranged res

rangedConst :: Value tp -> Range tp
rangedConst (BoolValue b) = BoolRange (not b) b
rangedConst (IntValue i) = IntRange (False,[i,i])
rangedConst (BitVecValue i bw) = BitVecRange bw False (False,[i,i])

isConst :: Range tp -> Maybe (Value tp)
isConst (BoolRange True False) = Just (BoolValue False)
isConst (BoolRange False True) = Just (BoolValue True)
isConst (IntRange (False,[i,j]))
  | i==j = Just (IntValue i)
isConst (BitVecRange bw _ (False,[i,j]))
  | i==j = Just (BitVecValue i bw)
isConst _ = Nothing

rangeInvariant :: Embed m e => Range tp -> e tp -> m (e BoolType)
rangeInvariant (BoolRange True True) _ = true
rangeInvariant (BoolRange False False) _ = false
rangeInvariant (BoolRange True False) e = not' e
rangeInvariant (BoolRange False True) e = return e
rangeInvariant (IntRange r) e = rangeInvariant' (\isLE c -> if isLE then e .<=. cint c else e .>=. cint c) r
rangeInvariant (BitVecRange bw s r) e
  = rangeInvariant' (\isLE c -> if | isLE && s -> e `bvsle` cbv c bw
                                   | isLE && not s -> e `bvule` cbv c bw
                                   | not isLE && s -> e `bvsge` cbv c bw
                                   | not isLE && not s -> e `bvuge` cbv c bw) r

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
rangeFixpoint (BitVecRange bw s r1) (BitVecRange _ s' r2)
  | s==s' = BitVecRange bw s r3
  where
    r3' = if lowerIntBound r1 == lowerIntBound r2
          then r2
          else extendLowerIntBound r2
    r3 = if upperIntBound r1 == upperIntBound r2
         then r3'
         else extendUpperIntBound r3'

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
includes (BitVecValue v _) (BitVecRange _ _ r) = intRangeIncludes v r

fullRange :: Repr tp -> Range tp
fullRange BoolRepr        = BoolRange True True
fullRange IntRepr         = IntRange (True,[])
fullRange (BitVecRepr bw) = BitVecRange bw False (True,[])

emptyRange :: Repr tp -> Range tp
emptyRange BoolRepr        = BoolRange False False
emptyRange IntRepr         = IntRange (False,[])
emptyRange (BitVecRepr bw) = BitVecRange bw False (False,[])

singletonRange :: Value tp -> Range tp
singletonRange (BoolValue b) = BoolRange (not b) b
singletonRange (IntValue v) = IntRange (False,[v,v])
singletonRange (BitVecValue v bw) = BitVecRange bw False (False,[v,v])

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
rangeType (BitVecRange bw _ _) = bitvec bw

-- To support easier manipulation of ranges, we introduce the Bounds type:

--type Bounds = Maybe (Maybe Integer,[(Integer,Integer)],Maybe Integer)

data InfInteger = NegInfinity | NormalInt Integer | PosInfinity deriving (Eq,Ord,Show)

type Bounds = [(InfInteger,InfInteger)]

instance Num InfInteger where
  fromInteger = NormalInt
  (+) (NormalInt x) (NormalInt y) = NormalInt $ x+y
  (+) NegInfinity PosInfinity = error "Adding positive and negative infinity undefined."
  (+) PosInfinity NegInfinity = error "Adding positive and negative infinity undefined."
  (+) PosInfinity _ = PosInfinity
  (+) NegInfinity _ = NegInfinity
  (+) _ PosInfinity = PosInfinity
  (+) _ NegInfinity = NegInfinity
  (-) (NormalInt x) (NormalInt y) = NormalInt $ x-y
  (-) NegInfinity NegInfinity = error "Subtracting negative infinity from negative infinity undefined."
  (-) PosInfinity PosInfinity = error "Subtracting positive infinity from positity infinity undefined."
  (-) NegInfinity _ = NegInfinity
  (-) PosInfinity _ = PosInfinity
  (-) _ NegInfinity = PosInfinity
  (-) _ PosInfinity = NegInfinity
  (*) (NormalInt x) (NormalInt y) = NormalInt $ x*y
  (*) (NormalInt 0) _ = NormalInt 0
  (*) _ (NormalInt 0) = NormalInt 0
  (*) PosInfinity y = if y > NormalInt 0
                      then PosInfinity
                      else NegInfinity
  (*) x PosInfinity = if x > NormalInt 0
                      then PosInfinity
                      else NegInfinity
  (*) NegInfinity y = if y < NormalInt 0
                      then PosInfinity
                      else NegInfinity
  (*) x NegInfinity = if x < NormalInt 0
                      then PosInfinity
                      else NegInfinity
  negate (NormalInt x) = NormalInt $ negate x
  negate NegInfinity = PosInfinity
  negate PosInfinity = NegInfinity
  abs (NormalInt x) = NormalInt $ abs x
  abs _ = PosInfinity
  signum (NormalInt x) = NormalInt $ signum x
  signum PosInfinity = NormalInt 1
  signum NegInfinity = NormalInt (-1)

-- | Convert an int range to a (canonicalized) bounds.
toBounds :: IntRange -> Bounds
toBounds (True,[]) = [(NegInfinity,PosInfinity)]
toBounds (True,x:xs) = (NegInfinity,NormalInt x):toBounds' xs
toBounds (False,xs) = toBounds' xs

toBounds' :: [Integer] -> Bounds
toBounds' [] = []
toBounds' [lower] = [(NormalInt lower,PosInfinity)]
toBounds' (lower:upper:xs) = (NormalInt lower,NormalInt upper):toBounds' xs

-- | Convert bounds to an int range.
fromBounds :: Bounds -> IntRange
fromBounds xs = case mergeBounds $ sortBy (comparing fst) xs of
  [(NegInfinity,PosInfinity)] -> (True,[])
  (NegInfinity,NormalInt upper):rest -> (True,upper:fromBounds' rest)
  ys -> (False,fromBounds' ys)
  where
    mergeBounds :: Bounds -> Bounds
    mergeBounds [] = []
    mergeBounds [x] = [x]
    mergeBounds ((lower1,upper1):(lower2,upper2):rest)
      | lower1 > upper1   = mergeBounds ((lower2,upper2):rest)
      | lower2 > upper2   = mergeBounds ((lower1,upper1):rest)
      | upper1 < lower2-1 = (lower1,upper1):mergeBounds ((lower2,upper2):rest)
      | otherwise         = mergeBounds ((lower1,max upper1 upper2):rest)

    fromBounds' :: Bounds -> [Integer]
    fromBounds' [] = []
    fromBounds' [(NormalInt lower,PosInfinity)] = [lower]
    fromBounds' ((NormalInt lower,NormalInt upper):rest)
      = lower:upper:fromBounds' rest

addBounds :: Bounds -> Bounds -> Bounds
addBounds xs ys = [ (l1+l2,u1+u2)
                  | (l1,u1) <- xs, (l2,u2) <- ys ]

subBounds :: Bounds -> Bounds -> Bounds
subBounds xs ys = [ (l1-u2,u1-l2)
                  | (l1,u1) <- xs, (l2,u2) <- ys ]

multBounds :: Bounds -> Bounds -> Bounds
multBounds xs ys = [ (minimum mults,maximum mults)
                   | (l1,u1) <- xs, (l2,u2) <- ys
                   , let mults = [ x1*x2 | x1 <- [l1,u1], x2 <- [l2,u2] ] ]

negBounds :: Bounds -> Bounds
negBounds xs = [ (-u,-l) | (l,u) <- xs ]

absBounds :: Bounds -> Bounds
absBounds = fmap f
  where
    f (l,u) = if l < 0
              then if u <= 0
                   then (-u,-l)
                   else (0,max u (-l))
              else (l,u)

signumBounds :: Bounds -> Bounds
signumBounds xs = if neg
                  then if zero
                       then if pos
                            then [(NormalInt (-1),NormalInt 1)]
                            else [(NormalInt (-1),NormalInt 0)]
                       else if pos
                            then [(NormalInt (-1),NormalInt (-1)),
                                  (NormalInt 1,NormalInt 1)]
                            else [(NormalInt (-1),NormalInt (-1))]
                  else if zero
                       then if pos
                            then [(NormalInt 0,NormalInt 1)]
                            else [(NormalInt 0,NormalInt 0)]
                       else if pos
                            then [(NormalInt 1,NormalInt 1)]
                            else []
  where
    neg = not $ null [ l | (l,_) <- xs, l < 0 ]
    zero = not $ null [ l | (l,u) <- xs, l <= 0, u >= 0 ]
    pos = not $ null [ u | (_,u) <- xs, u > 0 ]

instance Num (Range IntType) where
  fromInteger x = IntRange (False,[x,x])
  (+) (IntRange r1) (IntRange r2)
    = IntRange $ fromBounds $ addBounds (toBounds r1) (toBounds r2)
  (-) (IntRange r1) (IntRange r2)
    = IntRange $ fromBounds $ subBounds (toBounds r1) (toBounds r2)
  (*) (IntRange r1) (IntRange r2)
    = IntRange $ fromBounds $ multBounds (toBounds r1) (toBounds r2)
  negate (IntRange r)
    = IntRange $ fromBounds $ negBounds $ toBounds r
  abs (IntRange r)
    = IntRange $ fromBounds $ absBounds $ toBounds r
  signum (IntRange r)
    = IntRange $ fromBounds $ signumBounds $ toBounds r
