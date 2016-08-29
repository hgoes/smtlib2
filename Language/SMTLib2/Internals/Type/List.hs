module Language.SMTLib2.Internals.Type.List where

import Language.SMTLib2.Internals.Type.Nat

import Prelude hiding (head,tail,length,mapM,insert,drop,take,last,reverse,map,traverse)
import Data.GADT.Compare
import Data.GADT.Show
import Language.Haskell.TH

type family Head (lst :: [a]) :: a where
  Head (x ': xs) = x

type family Tail (lst :: [a]) :: [a] where
  Tail (x ': xs) = xs

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

type family Drop (lst :: [a]) (i :: Nat) :: [a] where
  Drop lst Z = lst
  Drop (x ': xs) (S n) = Drop xs n

type family Take (lst :: [a]) (i :: Nat) :: [a] where
  Take xs Z = '[]
  Take (x ': xs) (S n) = x ': (Take xs n)

type family StripPrefix (lst :: [a]) (pre :: [a]) :: [a] where
  StripPrefix xs '[] = xs
  StripPrefix (x ': xs) (x ': ys) = StripPrefix xs ys

type family Last (lst :: [a]) :: a where
  Last '[x] = x
  Last (x ': y ': rest) = Last (y ': rest)

type family DropLast (lst :: [a]) :: [a] where
  DropLast '[x] = '[]
  DropLast (x ': y ': rest) = x ': (DropLast (y ': rest))

type family Reverse (lst :: [a]) :: [a] where
  Reverse '[] = '[]
  Reverse (x ': xs) = Append (Reverse xs) x

type family Map (lst :: [a]) (f :: a -> b) :: [b] where
  Map '[] f = '[]
  Map (x ': xs) f = (f x) ': (Map xs f)

-- | Strongly typed heterogenous lists.
--
--   A /List e '[tp1,tp2,tp3]/ contains 3 elements of types /e tp1/, /e tp2/ and
--   /e tp3/ respectively.
--
--   As an example, the following list contains two types:
--
-- >>> int ::: bool ::: Nil :: List Repr '[IntType,BoolType]
-- [IntRepr,BoolRepr]
data List e (tp :: [a]) where
  Nil :: List e '[]
  (:::) :: e x -> List e xs -> List e (x ': xs)

infixr 9 :::

list :: [ExpQ] -> ExpQ
list [] = [| Nil |]
list (x:xs) = [| $(x) ::: $(list xs) |]

nil :: List e '[]
nil = Nil

list1 :: e t1 -> List e '[t1]
list1 x1 = x1 ::: Nil

list2 :: e t1 -> e t2 -> List e '[t1,t2]
list2 x1 x2 = x1 ::: x2 ::: Nil

list3 :: e t1 -> e t2 -> e t3 -> List e '[t1,t2,t3]
list3 x1 x2 x3 = x1 ::: x2 ::: x3 ::: Nil

-- | Get a static representation of a dynamic list.
--
--   For example, to convert a list of strings into a list of types:
--
-- >>> reifyList (\name f -> case name of { "int" -> f int ; "bool" -> f bool }) ["bool","int"] show
-- "[BoolRepr,IntRepr]"
reifyList :: (forall r'. a -> (forall tp. e tp -> r') -> r')
          -> [a] -> (forall tp. List e tp -> r)
          -> r
reifyList _ [] g = g Nil
reifyList f (x:xs) g = f x $ \x' -> reifyList f xs $ \xs' -> g (x' ::: xs')

access :: Monad m => List e lst -> Natural idx
       -> (e (Index lst idx) -> m (a,e tp))
       -> m (a,List e (Insert lst idx tp))
access (x ::: xs) Zero f = do
  (res,nx) <- f x
  return (res,nx ::: xs)
access (x ::: xs) (Succ n) f = do
  (res,nxs) <- access xs n f
  return (res,x ::: nxs)

access' :: Monad m => List e lst -> Natural idx
        -> (e (Index lst idx) -> m (a,e (Index lst idx)))
        -> m (a,List e lst)
access' (x ::: xs) Zero f = do
  (res,nx) <- f x
  return (res,nx ::: xs)
access' (x ::: xs) (Succ n) f = do
  (res,nxs) <- access' xs n f
  return (res,x ::: nxs)

head :: List e lst -> e (Head lst)
head (x ::: xs) = x

tail :: List e lst -> List e (Tail lst)
tail (x ::: xs) = xs

index :: List e lst -> Natural idx -> e (Index lst idx)
index (x ::: xs) Zero = x
index (x ::: xs) (Succ n) = index xs n

insert :: List e lst -> Natural idx -> e tp -> List e (Insert lst idx tp)
insert (x ::: xs) Zero y = y ::: xs
insert (x ::: xs) (Succ n) y = x ::: (insert xs n y)

remove :: List e lst -> Natural idx -> List e (Remove lst idx)
remove (x ::: xs) Zero = xs
remove (x ::: xs) (Succ n) = x ::: (remove xs n)

mapM :: Monad m => (forall x. e x -> m (e' x)) -> List e lst -> m (List e' lst)
mapM _ Nil = return Nil
mapM f (x ::: xs) = do
  nx <- f x
  nxs <- mapM f xs
  return (nx ::: nxs)

mapIndexM :: Monad m => (forall n. Natural n -> e (Index lst n) -> m (e' (Index lst n)))
          -> List e lst
          -> m (List e' lst)
mapIndexM f Nil = return Nil
mapIndexM f (x ::: xs) = do
  nx <- f Zero x
  nxs <- mapIndexM (\n -> f (Succ n)) xs
  return (nx ::: nxs)

traverse :: Applicative f => (forall x. e x -> f (e' x)) -> List e lst -> f (List e' lst)
traverse f Nil = pure Nil
traverse f (x ::: xs) = (:::) <$> f x <*> traverse f xs

cons :: e x -> List e xs -> List e (x ': xs)
cons = (:::)

append :: List e xs -> e x -> List e (Append xs x)
append Nil y = y ::: Nil
append (x ::: xs) y = x ::: (append xs y)

length :: List e lst -> Natural (Length lst)
length Nil = Zero
length (_ ::: xs) = Succ (length xs)

drop :: List e lst -> Natural i -> List e (Drop lst i)
drop xs Zero = xs
drop (x ::: xs) (Succ n) = drop xs n

take :: List e lst -> Natural i -> List e (Take lst i)
take xs Zero = Nil
take (x ::: xs) (Succ n) = x ::: (take xs n)

last :: List e lst -> e (Last lst)
last (x ::: Nil) = x
last (x ::: y ::: rest) = last (y ::: rest)

dropLast :: List e lst -> List e (DropLast lst)
dropLast (_ ::: Nil) = Nil
dropLast (x ::: y ::: rest) = x ::: (dropLast (y ::: rest))

stripPrefix :: GEq e => List e lst -> List e pre -> Maybe (List e (StripPrefix lst pre))
stripPrefix xs Nil = Just xs
stripPrefix (x ::: xs) (y ::: ys)
  = case geq x y of
  Just Refl -> stripPrefix xs ys
  Nothing -> Nothing

reverse :: List e lst -> List e (Reverse lst)
reverse Nil = Nil
reverse (x ::: xs) = append (reverse xs) x

map :: List e lst -> (forall x. e x -> e (f x)) -> List e (Map lst f)
map Nil _ = Nil
map (x ::: xs) f = (f x) ::: (map xs f)

unmap :: List p lst -> List e (Map lst f) -> (forall x. e (f x) -> e x) -> List e lst
unmap Nil Nil _ = Nil
unmap (_ ::: tps) (x ::: xs) f = (f x) ::: (unmap tps xs f)

unmapM :: Monad m => List p lst -> List e (Map lst f)
       -> (forall x. e (f x) -> m (e x)) -> m (List e lst)
unmapM Nil Nil _ = return Nil
unmapM (_ ::: tps) (x ::: xs) f = do
  x' <- f x
  xs' <- unmapM tps xs f
  return $ x' ::: xs'

mapM' :: Monad m => List e lst -> (forall x. e x -> m (e (f x))) -> m (List e (Map lst f))
mapM' Nil _ = return Nil
mapM' (x ::: xs) f = do
  x' <- f x
  xs' <- mapM' xs f
  return (x' ::: xs')

toList :: Monad m => (forall x. e x -> m a) -> List e lst -> m [a]
toList f Nil = return []
toList f (x ::: xs) = do
  nx <- f x
  nxs <- toList f xs
  return (nx : nxs)

toListIndex :: Monad m => (forall n. Natural n -> e (Index lst n) -> m a)
            -> List e lst -> m [a]
toListIndex f Nil = return []
toListIndex f (x ::: xs) = do
  nx <- f Zero x
  nxs <- toListIndex (\n -> f (Succ n)) xs
  return (nx : nxs)

foldM :: Monad m => (forall x. s -> e x -> m s) -> s -> List e lst -> m s
foldM f s Nil = return s
foldM f s (x ::: xs) = do
  ns <- f s x
  foldM f ns xs

zipWithM :: Monad m => (forall x. e1 x -> e2 x -> m (e3 x))
         -> List e1 lst -> List e2 lst -> m (List e3 lst)
zipWithM f Nil Nil = return Nil
zipWithM f (x ::: xs) (y ::: ys) = do
  z <- f x y
  zs <- zipWithM f xs ys
  return $ z ::: zs

zipToListM :: Monad m => (forall x. e1 x -> e2 x -> m a)
           -> List e1 lst -> List e2 lst
           -> m [a]
zipToListM f Nil Nil = return []
zipToListM f (x ::: xs) (y ::: ys) = do
  z <- f x y
  zs <- zipToListM f xs ys
  return (z : zs)

mapAccumM :: Monad m => (forall x. s -> e x -> m (s,e' x))
          -> s -> List e xs
          -> m (s,List e' xs)
mapAccumM _ s Nil = return (s,Nil)
mapAccumM f s (x ::: xs) = do
  (s1,x') <- f s x
  (s2,xs') <- mapAccumM f s1 xs
  return (s2,x' ::: xs')

instance GEq e => Eq (List e lst) where
  (==) Nil Nil = True
  (==) (x ::: xs) (y ::: ys) = case geq x y of
    Just Refl -> xs==ys
    Nothing -> False

instance GEq e => GEq (List e) where
  geq Nil Nil = Just Refl
  geq (x ::: xs) (y ::: ys) = do
    Refl <- geq x y
    Refl <- geq xs ys
    return Refl
  geq _ _ = Nothing

instance GCompare e => Ord (List e lst) where
  compare Nil Nil = EQ
  compare (x ::: xs) (y ::: ys) = case gcompare x y of
    GEQ -> compare xs ys
    GLT -> LT
    GGT -> GT

instance GCompare e => GCompare (List e) where
  gcompare Nil Nil = GEQ
  gcompare Nil _ = GLT
  gcompare _ Nil = GGT
  gcompare (x ::: xs) (y ::: ys) = case gcompare x y of
    GEQ -> case gcompare xs ys of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    GLT -> GLT
    GGT -> GGT

instance GShow e => Show (List e lst) where
  showsPrec p Nil = showString "[]"
  showsPrec p (x ::: xs) = showChar '[' .
                           gshowsPrec 0 x .
                           showLst xs .
                           showChar ']'
    where
      showLst :: List e lst' -> ShowS
      showLst Nil = id
      showLst (x ::: xs) = showChar ',' .
                           gshowsPrec 0 x .
                           showLst xs

instance GShow e => GShow (List e) where
  gshowsPrec = showsPrec
