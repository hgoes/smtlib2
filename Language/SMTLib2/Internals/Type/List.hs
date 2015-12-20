module Language.SMTLib2.Internals.Type.List where

import Language.SMTLib2.Internals.Type.Nat

import Prelude hiding (length,mapM,insert)
import Data.GADT.Compare
import Data.GADT.Show

type family Index (lst :: [a]) (idx :: Nat) :: a where
  Index (x ': xs) Z = x
  Index (x ': xs) (S n) = Index xs n

type family Insert (lst :: [a]) (idx :: Nat) (el :: a) :: [a] where
  Insert (x ': xs) Z y = y ': xs
  Insert (x ': xs) (S n) y = x ': (Insert xs n y)

type family Remove (lst :: [a]) (idx :: Nat) :: [a] where
  Remove (x ': xs) Z = xs
  Remove (x ': xs) (S n) = x ': (Remove xs n)

type family Append (lst :: [a]) (el :: a) :: [a] where
  Append '[] y = y ': '[]
  Append (x ': xs) y = x ': (Append xs y)

type family Length (lst :: [a]) :: Nat where
  Length '[] = Z
  Length (x ': xs) = S (Length xs)

data List e (tp :: [a]) where
  Nil :: List e '[]
  Cons :: e x -> List e xs -> List e (x ': xs)

access :: Monad m => List e lst -> Natural idx -> (e (Index lst idx) -> m (a,e tp)) -> m (a,List e (Insert lst idx tp))
access (Cons x xs) Zero f = do
  (res,nx) <- f x
  return (res,Cons nx xs)
access (Cons x xs) (Succ n) f = do
  (res,nxs) <- access xs n f
  return (res,Cons x nxs)

index :: List e lst -> Natural idx -> e (Index lst idx)
index (Cons x xs) Zero = x
index (Cons x xs) (Succ n) = index xs n

insert :: List e lst -> Natural idx -> e tp -> List e (Insert lst idx tp)
insert (Cons x xs) Zero y = Cons y xs
insert (Cons x xs) (Succ n) y = Cons x (insert xs n y)

remove :: List e lst -> Natural idx -> List e (Remove lst idx)
remove (Cons x xs) Zero = xs
remove (Cons x xs) (Succ n) = Cons x (remove xs n)

mapM :: Monad m => (forall x. e x -> m (e' x)) -> List e lst -> m (List e' lst)
mapM _ Nil = return Nil
mapM f (Cons x xs) = do
  nx <- f x
  nxs <- mapM f xs
  return (Cons nx nxs)

mapIndexM :: Monad m => (forall n. Natural n -> e (Index lst n) -> m (e' (Index lst n)))
          -> List e lst
          -> m (List e' lst)
mapIndexM f Nil = return Nil
mapIndexM f (Cons x xs) = do
  nx <- f Zero x
  nxs <- mapIndexM (\n -> f (Succ n)) xs
  return (Cons nx nxs)

cons :: e x -> List e xs -> List e (x ': xs)
cons = Cons

append :: List e xs -> e x -> List e (Append xs x)
append Nil y = Cons y Nil
append (Cons x xs) y = Cons x (append xs y)

length :: List e lst -> Natural (Length lst)
length Nil = Zero
length (Cons _ xs) = Succ (length xs)

toList :: Monad m => (forall x. e x -> m a) -> List e lst -> m [a]
toList f Nil = return []
toList f (Cons x xs) = do
  nx <- f x
  nxs <- toList f xs
  return (nx : nxs)

toListIndex :: Monad m => (forall n. Natural n -> e (Index lst n) -> m a)
            -> List e lst -> m [a]
toListIndex f Nil = return []
toListIndex f (Cons x xs) = do
  nx <- f Zero x
  nxs <- toListIndex (\n -> f (Succ n)) xs
  return (nx : nxs)

foldM :: Monad m => (forall x. s -> e x -> m s) -> s -> List e lst -> m s
foldM f s Nil = return s
foldM f s (Cons x xs) = do
  ns <- f s x
  foldM f ns xs

zipWithM :: Monad m => (forall x. e1 x -> e2 x -> m (e3 x))
         -> List e1 lst -> List e2 lst -> m (List e3 lst)
zipWithM f Nil Nil = return Nil
zipWithM f (Cons x xs) (Cons y ys) = do
  z <- f x y
  zs <- zipWithM f xs ys
  return $ Cons z zs

zipToListM :: Monad m => (forall x. e1 x -> e2 x -> m a)
           -> List e1 lst -> List e2 lst
           -> m [a]
zipToListM f Nil Nil = return []
zipToListM f (Cons x xs) (Cons y ys) = do
  z <- f x y
  zs <- zipToListM f xs ys
  return (z : zs)

mapAccumM :: Monad m => (forall x. s -> e x -> m (s,e' x))
          -> s -> List e xs
          -> m (s,List e' xs)
mapAccumM _ s Nil = return (s,Nil)
mapAccumM f s (Cons x xs) = do
  (s1,x') <- f s x
  (s2,xs') <- mapAccumM f s1 xs
  return (s2,Cons x' xs')

instance GEq e => Eq (List e lst) where
  (==) Nil Nil = True
  (==) (Cons x xs) (Cons y ys) = case geq x y of
    Just Refl -> xs==ys
    Nothing -> False

instance GEq e => GEq (List e) where
  geq Nil Nil = Just Refl
  geq (Cons x xs) (Cons y ys) = do
    Refl <- geq x y
    Refl <- geq xs ys
    return Refl
  geq _ _ = Nothing

instance GCompare e => Ord (List e lst) where
  compare Nil Nil = EQ
  compare (Cons x xs) (Cons y ys) = case gcompare x y of
    GEQ -> compare xs ys
    GLT -> LT
    GGT -> GT

instance GCompare e => GCompare (List e) where
  gcompare Nil Nil = GEQ
  gcompare Nil _ = GLT
  gcompare _ Nil = GGT
  gcompare (Cons x xs) (Cons y ys) = case gcompare x y of
    GEQ -> case gcompare xs ys of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

instance GShow e => Show (List e lst) where
  showsPrec p Nil = showString "[]"
  showsPrec p (Cons x xs) = showChar '[' .
                            gshowsPrec 0 x .
                            showLst xs .
                            showChar ']'
    where
      showLst :: List e lst' -> ShowS
      showLst Nil = id
      showLst (Cons x xs) = showChar ',' .
                            gshowsPrec 0 x .
                            showLst xs

instance GShow e => GShow (List e) where
  gshowsPrec = showsPrec
