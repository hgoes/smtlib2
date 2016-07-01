{-# LANGUAGE KindSignatures,DataKinds,GADTs,TypeFamilies,StandaloneDeriving,MultiWayIf #-}
{- | A value bounded by static bounds. -}
module Language.SMTLib2.Composite.Ranged
  (Ranged(..),
   -- * Range
   Range(..),
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

newtype Ranged (tp :: Type) e = Ranged { getRanged :: e tp }

-- | Invariant: The range elements are sorted ascending.
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
