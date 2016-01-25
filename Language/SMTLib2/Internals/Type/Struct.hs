module Language.SMTLib2.Internals.Type.Struct where

import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List

import Prelude hiding (mapM,insert)
import Data.GADT.Compare
import Data.GADT.Show
import Data.Functor.Identity

data Tree a = Leaf a
            | Node [Tree a]

data Struct e tp where
  Singleton :: e t -> Struct e (Leaf t)
  Struct :: List (Struct e) ts -> Struct e (Node ts)

type family Index (struct :: Tree a) (idx :: [Nat]) :: Tree a where
  Index x '[] = x
  Index (Node xs) (n ': ns) = Index (List.Index xs n) ns

type family ElementIndex (struct :: Tree a) (idx :: [Nat]) :: a where
  ElementIndex (Leaf x) '[] = x
  ElementIndex (Node xs) (n ': ns) = ElementIndex (List.Index xs n) ns

type family Insert (struct :: Tree a) (idx :: [Nat]) (el :: Tree a) :: Tree a where
  Insert x '[] y = y
  Insert (Node xs) (n ': ns) y = Node (List.Insert xs n
                                       (Insert (List.Index xs n) ns y))

type family Remove (struct :: Tree a) (idx :: [Nat]) :: Tree a where
  Remove (Node xs) '[n] = Node (List.Remove xs n)
  Remove (Node xs) (n1 ': n2 ': ns) = Node (List.Insert xs n1
                                            (Remove (List.Index xs n1) (n2 ': ns)))

type family Size (struct :: Tree a) :: Nat where
  Size (Leaf x) = S Z
  Size (Node '[]) = Z
  Size (Node (x ': xs)) = (Size x) + (Size (Node xs))

access :: Monad m => Struct e tp -> List Natural idx
       -> (e (ElementIndex tp idx) -> m (a,e (ElementIndex tp idx)))
       -> m (a,Struct e tp)
access (Singleton x) Nil f = do
  (res,nx) <- f x
  return (res,Singleton nx)
access (Struct xs) (n ::: ns) f = do
  (res,nxs) <- List.access' xs n (\x -> access x ns f)
  return (res,Struct nxs)

accessElement :: Monad m => Struct e tp -> List Natural idx
              -> (e (ElementIndex tp idx) -> m (a,e ntp))
              -> m (a,Struct e (Insert tp idx (Leaf ntp)))
accessElement (Singleton x) Nil f = do
  (res,nx) <- f x
  return (res,Singleton nx)
accessElement (Struct xs) (n ::: ns) f = do
  (res,nxs) <- List.access xs n (\x -> accessElement x ns f)
  return (res,Struct nxs)

index :: Struct e tp -> List Natural idx -> Struct e (Index tp idx)
index x Nil = x
index (Struct xs) (n ::: ns) = index (List.index xs n) ns

elementIndex :: Struct e tp -> List Natural idx -> e (ElementIndex tp idx)
elementIndex (Singleton x) Nil = x
elementIndex (Struct xs) (n ::: ns)
  = elementIndex (List.index xs n) ns

insert :: Struct e tps -> List Natural idx -> Struct e tp
       -> Struct e (Insert tps idx tp)
insert x Nil y = y
insert (Struct xs) (n ::: ns) y
  = Struct (List.insert xs n (insert (List.index xs n) ns y))

remove :: Struct e tps -> List Natural idx -> Struct e (Remove tps idx)
remove (Struct xs) (n ::: Nil) = Struct (List.remove xs n)
remove (Struct xs) (n1 ::: n2 ::: ns)
  = Struct (List.insert xs n1
            (remove (List.index xs n1) (n2 ::: ns)))

mapM :: Monad m => (forall x. e x -> m (e' x)) -> Struct e tps -> m (Struct e' tps)
mapM f (Singleton x) = do
  nx <- f x
  return (Singleton nx)
mapM f (Struct xs) = do
  nxs <- List.mapM (mapM f) xs
  return (Struct nxs)

mapIndexM :: Monad m
          => (forall idx.
              List Natural idx
              -> e (ElementIndex tps idx)
              -> m (e' (ElementIndex tps idx)))
          -> Struct e tps
          -> m (Struct e' tps)
mapIndexM f (Singleton x) = do
  nx <- f Nil x
  return (Singleton nx)
mapIndexM f (Struct xs) = do
  nxs <- List.mapIndexM (\n -> mapIndexM (\ns -> f (n ::: ns))) xs
  return (Struct nxs)

map :: (forall x. e x -> e' x) -> Struct e tps -> Struct e' tps
map f = runIdentity . (mapM (return.f))

size :: Struct e tps -> Natural (Size tps)
size (Singleton x) = Succ Zero
size (Struct Nil) = Zero
size (Struct (x ::: xs)) = naturalAdd (size x) (size (Struct xs))

flatten :: Monad m => (forall x. e x -> m a) -> ([a] -> m a) -> Struct e tps -> m a
flatten f _ (Singleton x) = f x
flatten f g (Struct xs) = do
  nxs <- List.toList (flatten f g) xs
  g nxs

flattenIndex :: Monad m => (forall idx. List Natural idx
                            -> e (ElementIndex tps idx)
                            -> m a)
             -> ([a] -> m a)
             -> Struct e tps -> m a
flattenIndex f _ (Singleton x) = f Nil x
flattenIndex f g (Struct xs) = do
  nxs <- List.toListIndex (\n x -> flattenIndex (\idx -> f (n ::: idx)) g x) xs
  g nxs

zipWithM :: Monad m => (forall x. e1 x -> e2 x -> m (e3 x))
         -> Struct e1 tps -> Struct e2 tps -> m (Struct e3 tps)
zipWithM f (Singleton x) (Singleton y) = do
  z <- f x y
  return (Singleton z)
zipWithM f (Struct xs) (Struct ys) = do
  zs <- List.zipWithM (zipWithM f) xs ys
  return (Struct zs)

zipFlatten :: Monad m => (forall x. e1 x -> e2 x -> m a)
           -> ([a] -> m a)
           -> Struct e1 tps -> Struct e2 tps -> m a
zipFlatten f _ (Singleton x) (Singleton y) = f x y
zipFlatten f g (Struct xs) (Struct ys) = do
  zs <- List.zipToListM (zipFlatten f g) xs ys
  g zs

instance GEq e => Eq (Struct e tps) where
  (==) (Singleton x) (Singleton y) = case geq x y of
    Just Refl -> True
    Nothing -> False
  (==) (Struct xs) (Struct ys) = xs==ys

instance GEq e => GEq (Struct e) where
  geq (Singleton x) (Singleton y) = do
    Refl <- geq x y
    return Refl
  geq (Struct xs) (Struct ys) = do
    Refl <- geq xs ys
    return Refl
  geq _ _ = Nothing

instance GCompare e => Ord (Struct e tps) where
  compare (Singleton x) (Singleton y) = case gcompare x y of
    GEQ -> EQ
    GLT -> LT
    GGT -> GT
  compare (Struct xs) (Struct ys) = compare xs ys

instance GCompare e => GCompare (Struct e) where
  gcompare (Singleton x) (Singleton y) = case gcompare x y of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT
  gcompare (Singleton _) _ = GLT
  gcompare _ (Singleton _) = GGT
  gcompare (Struct xs) (Struct ys) = case gcompare xs ys of
    GEQ -> GEQ
    GLT -> GLT
    GGT -> GGT

instance GShow e => Show (Struct e tps) where
  showsPrec p (Singleton x) = gshowsPrec p x
  showsPrec p (Struct xs) = showParen (p>10) $
                            showString "Struct " .
                            showsPrec 11 xs

instance GShow e => GShow (Struct e) where
  gshowsPrec = showsPrec
