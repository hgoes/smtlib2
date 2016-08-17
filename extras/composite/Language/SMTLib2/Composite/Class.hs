module Language.SMTLib2.Composite.Class where

import Language.SMTLib2

import Data.GADT.Compare
import Data.GADT.Show
import Data.Proxy
import Control.Monad.Writer

-- | A composite is a data-structure composed of multiple SMT expressions.
class (Ord (CompDescr arg),GCompare (RevComp arg),GShow (RevComp arg))
      => Composite (arg :: (Type -> *) -> *) where
  type CompDescr arg
  type RevComp arg :: Type -> *
  compositeType :: CompDescr arg -> arg Repr
  foldExprs :: (Monad m,GetType e)
            => (forall t. RevComp arg t -> e t -> m (e' t))
            -> arg e
            -> m (arg e')
  accessComposite :: GetType e => RevComp arg t -> arg e -> Maybe (e t)
  createComposite :: (Monad m)
                  => (forall t. Repr t -> RevComp arg t -> m (e t))
                  -> CompDescr arg
                  -> m (arg e)
  createComposite f descr
    = foldExprs (\rev tp -> f tp rev)
      (compositeType descr)
  revName :: Proxy arg -> RevComp arg tp -> String
  revName _ _ = "rev"
  revType :: Proxy arg -> CompDescr arg -> RevComp arg tp -> Repr tp
  revType (_::Proxy arg) descr rev = case accessComposite rev (compositeType descr :: arg Repr) of
    Just r -> r
    Nothing -> error "revType: Internal error, type for unknown element requested."

class Composite arg => CompositeExtract arg where
  type CompExtract arg
  compExtract :: (Embed m e,Monad m,GetType e) => (forall tp. e tp -> m (Value tp)) -> arg e -> m (CompExtract arg)

defaultUnion :: (Composite arg,Monad m,GetType a,GetType b)
             => (forall t. RevComp arg t -> Maybe (a t) -> Maybe (b t) -> m (c t))
             -> CompDescr arg
             -> arg a
             -> arg b
             -> m (arg c)
defaultUnion f descr x y
  = createComposite (\_ rev -> f rev (accessComposite rev x) (accessComposite rev y)) descr

defaultEq :: (Composite arg,Embed m e,Monad m,GetType e)
          => CompDescr arg
          -> arg e
          -> arg e
          -> m (e BoolType)
defaultEq descr x y = do
  eqs <- execWriterT $ defaultUnion (\_ -> comb) descr x y
  case eqs of
    [] -> true
    [x] -> return x
    _ -> and' eqs
  where
    comb Nothing Nothing = return undefined
    comb (Just x) (Just y) = do
      eq <- lift $ x .==. y
      tell [eq]
      return undefined
    comb _ _ = do
      f <- lift false
      tell [f]
      return undefined
