module Language.SMTLib2.Composite.Array.Bounded where

import Language.SMTLib2 hiding (select,store)
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains

import Data.Monoid
import Data.GADT.Compare
import Data.GADT.Show
import Prelude hiding (Bounded)

data Bounded arr idx (e :: Type -> *)
  = Bounded { boundedArray :: arr e
            , bound :: idx e }

data RevBounded arr idx tp where
  RevBoundedArray :: RevComp arr tp -> RevBounded arr idx tp
  RevBound :: RevComp idx tp -> RevBounded arr idx tp

instance (Composite arr,Composite idx) => Composite (Bounded arr idx) where
  type RevComp (Bounded arr idx) = RevBounded arr idx
  foldExprs f (Bounded arr bnd) = do
    narr <- foldExprs (f . RevBoundedArray) arr
    nbnd <- foldExprs (f . RevBound) bnd
    return (Bounded narr nbnd)
  mapExprs f (Bounded arr bnd) = do
    narr <- mapExprs f arr
    nbnd <- mapExprs f bnd
    return (Bounded narr nbnd)
  getRev (RevBoundedArray r) arr = getRev r (boundedArray arr)
  getRev (RevBound r) arr = getRev r (bound arr)
  setRev (RevBoundedArray r) e (Just arr) = do
    narr <- setRev r e (Just $ boundedArray arr)
    return arr { boundedArray = narr }
  setRev (RevBound r) e (Just arr) = do
    nbnd <- setRev r e (Just $ bound arr)
    return arr { bound = nbnd }
  setRev _ _ Nothing = Nothing
  compCombine f b1 b2 = do
    arr <- compCombine f (boundedArray b1) (boundedArray b2)
    case arr of
      Nothing -> return Nothing
      Just narr -> do
        bnd <- compCombine f (bound b1) (bound b2)
        case bnd of
          Nothing -> return Nothing
          Just nbnd -> return $ Just $ Bounded narr nbnd
  compCompare (Bounded arr1 bnd1) (Bounded arr2 bnd2)
    = compCompare arr1 arr2 `mappend`
      compCompare bnd1 bnd2
  compShow p (Bounded arr bnd)
    = showParen (p>10) $
      showString "Bounded " .
      compShow 11 arr . showChar ' ' .
      compShow 11 bnd
  compInvariant (Bounded arr bnd) = do
    inv1 <- compInvariant arr
    inv2 <- compInvariant bnd
    return $ inv1++inv2

instance (Wrapper arr,Composite idx) => Wrapper (Bounded arr idx) where
  type ElementType (Bounded arr idx) = ElementType arr
  elementType arr = elementType (boundedArray arr)

instance (IsArray arr idx,IsRanged idx,IsSingleton idx,IsNumeric idx,Integral (Value (SingletonType idx))) => IsArray (Bounded arr idx) idx where
  newArray idx el = do
    arr <- newArray idx el
    bnd <- compositeFromValue (fromInteger 0)
    return $ Bounded arr bnd
  select (Bounded arr _) idx = select arr idx
  store (Bounded arr sz) idx nel = do
    narr <- store arr idx nel
    case narr of
      Nothing -> return Nothing
      Just narr' -> return $ Just $ Bounded narr' sz

instance (IsArray arr idx,IsRanged idx,IsNumSingleton idx)
  => IsStaticBounded (Bounded arr idx) where
  checkStaticIndex arr idx = do
    let idx' = fromInteger idx
        idxRange = singletonRange idx'
    sizeRange <- getRange $ bound arr
    let zeroRange = rangedConst (toEnum 0)
        arrRange = betweenRange zeroRange sizeRange
        outsideRange = setMinusRange arrRange idxRange
        insideRange = intersectionRange arrRange idxRange
    if nullRange outsideRange
      then return NoError
      else if nullRange insideRange
           then return AlwaysError
           else do
      ridx <- compositeFromValue idx'
      Just errCond <- compositeGEQ ridx (bound arr)
      return $ SometimesError errCond

instance (IsArray arr idx,IsRanged idx,IsNumSingleton idx)
  => IsBounded (Bounded arr idx) idx where
  checkIndex arr idx = do
    idxRange <- getRange idx
    sizeRange <- getRange $ bound arr
    let zeroRange = rangedConst (fromInteger 0)
        arrRange = betweenRange zeroRange sizeRange
        outsideRange = setMinusRange idxRange arrRange
        insideRange = intersectionRange arrRange idxRange
    if nullRange outsideRange
      then return NoError
      else if nullRange insideRange
           then return AlwaysError
           else do
      Just errCond <- compositeGEQ idx (bound arr)
      return $ SometimesError errCond
  arraySize arr = return $ bound arr

instance (Composite arr,Composite idx) => GEq (RevBounded arr idx) where
  geq (RevBoundedArray r1) (RevBoundedArray r2) = do
    Refl <- geq r1 r2
    return Refl
  geq (RevBound r1) (RevBound r2) = do
    Refl <- geq r1 r2
    return Refl
  geq _ _ = Nothing

instance (Composite arr,Composite idx) => GCompare (RevBounded arr idx) where
  gcompare (RevBoundedArray r1) (RevBoundedArray r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (RevBoundedArray _) _ = GLT
  gcompare _ (RevBoundedArray _) = GGT
  gcompare (RevBound r1) (RevBound r2) = case gcompare r1 r2 of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance (Composite arr,Composite idx) => Show (RevBounded arr idx tp) where
  showsPrec p (RevBoundedArray r) = showParen (p>10) $
    showString "RevBoundedArray " .
    gshowsPrec 11 r
  showsPrec p (RevBound r) = showParen (p>10) $
    showString "RevBound " .
    gshowsPrec 11 r

instance (Composite arr,Composite idx) => GShow (RevBounded arr idx) where
  gshowsPrec = showsPrec

instance (Composite idx,StaticByteAccess arr el) => StaticByteAccess (Bounded arr idx) el where
  staticByteRead (Bounded arr _) off sz = staticByteRead arr off sz
  staticByteWrite (Bounded arr arrSz) off el = do
    res <- staticByteWrite arr off el
    case res of
      Nothing -> return Nothing
      Just (narr,rest) -> return $ Just (Bounded narr arrSz,rest)
