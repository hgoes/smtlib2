module Language.SMTLib2.Composite.Lens where

import Language.SMTLib2
import Language.SMTLib2.Internals.Embed

import qualified Data.Traversable as T
import Control.Monad
import Data.Functor.Constant
import Control.Lens
import Data.GADT.Compare
import Control.Applicative
import Data.Functor.Identity

type LensM  m s t a b
    = forall f . (Traversable f) => (a -> f b) -> s -> m (f t)
type LensM' m s a
    = LensM m s s a a

lensM :: (Monad m) => (s -> m a) -> (s -> b -> m t)
      -> LensM m s t a b
lensM g s f x = g x >>= T.mapM (s x) . f

mget :: (Monad m) => LensM m s t a b -> s -> m a
mget l s = liftM getConstant $ l Constant s

mset :: (Monad m) => LensM m s t a b -> s -> b -> m t
mset l s v = liftM runIdentity $ l (const $ Identity v) s

withLensM :: (Monad m) => LensM' m a b -> (b -> m b) -> a -> m a
withLensM l f x = do
  el <- mget l x
  nel <- f el
  mset l x nel

type CompLens a b = forall m e. (Embed m e,GetType e,GCompare e,Monad m) => LensM' m (a e) (b e)

composeLensM :: Monad m => LensM' m a b -> LensM' m b c -> LensM' m a c
composeLensM l1 l2
  = lensM (\st -> do
              x <- mget l1 st
              mget l2 x)
    (\st y -> do
        x <- mget l1 st
        nx <- mset l2 x y
        mset l1 st nx)

idLensM :: Monad m => LensM' m a a
idLensM = liftLens id

liftLens :: Monad m => Lens' a b -> LensM' m a b
liftLens l = lensM (\st -> return (st ^. l))
             (\st el -> return (st & l .~ el))

type MaybeLens a b = Lens a (Maybe a) (Maybe b) b

getMaybe :: a -> MaybeLens a b -> Maybe b
getMaybe x l = getConst $ l Const x

setMaybe :: a -> MaybeLens a b -> b -> Maybe a
setMaybe x l y = runIdentity $ l (const $ return y) x

composeMaybe :: MaybeLens a b -> MaybeLens b c -> MaybeLens a c
composeMaybe l1 l2
  = lens (\x -> do
             y <- x `getMaybe` l1
             y `getMaybe` l2)
    (\x new -> do
        y <- x `getMaybe` l1
        ny <- y & l2 .~ new
        x & l1 .~ ny)

maybeLens :: Lens' a b -> MaybeLens a b
maybeLens l = lens (\x -> Just $ x ^. l)
              (\x new -> Just $ x & l .~ new)

nothingLens :: MaybeLens a b
nothingLens = lens (\_ -> Nothing)
              (\_ _ -> Nothing)

forceMaybe :: MaybeLens a b -> Lens' a b
forceMaybe l = lens (\x -> case getMaybe x l of
                        Just r -> r)
               (\x new -> case setMaybe x l new of
                   Just nx -> nx)

just :: MaybeLens (Maybe a) a
just = lens id (const $ Just . Just)
