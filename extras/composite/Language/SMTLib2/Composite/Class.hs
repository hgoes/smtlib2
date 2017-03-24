module Language.SMTLib2.Composite.Class where

import Language.SMTLib2
import Language.SMTLib2.Internals.Embed

import Data.GADT.Compare
import Data.GADT.Show
import Data.Proxy
import Data.Functor.Identity
import Control.Monad.Writer

type CompDescr arg = arg Repr

-- | A composite is a data-structure composed of multiple SMT expressions.
class (GCompare (RevComp arg),GShow (RevComp arg))
      => Composite (arg :: (Type -> *) -> *) where
  type RevComp arg :: Type -> *
  foldExprs :: (Monad m)
            => (forall t. RevComp arg t -> e t -> m (e' t))
            -> arg e
            -> m (arg e')
  mapExprs :: (Monad m)
           => (forall t. e t -> m (e' t))
           -> arg e
           -> m (arg e')
  mapExprs f = foldExprs (const f)
  getRev :: RevComp arg tp -> arg e -> Maybe (e tp)
  setRev :: RevComp arg tp -> e tp -> Maybe (arg e) -> Maybe (arg e)
  withRev :: (Monad m) => RevComp arg tp -> arg e -> (e tp -> m (e tp)) -> m (arg e)
  withRev rev x f = case getRev rev x of
    Nothing -> return x
    Just e -> do
      ne <- f e
      case setRev rev ne (Just x) of
        Nothing -> return x
        Just nx -> return nx
  compCombine :: (Embed m e,Monad m,GCompare e)
              => (forall tp. e tp -> e tp -> m (e tp))
              -> arg e -> arg e -> m (Maybe (arg e))

  revName :: Proxy arg -> RevComp arg tp -> String
  revName _ _ = "rev"
  compCompare :: GCompare e => arg e -> arg e -> Ordering
  compShow :: GShow e => Int -> arg e -> ShowS

  compInvariant :: (Embed m e,Monad m) => arg e -> m [e BoolType]
  compInvariant _ = return []

{-

XXX: These overlap

instance (Composite arg,GCompare e) => Eq (arg e) where
  (==) x y = compCompare x y == EQ

instance (Composite arg,GCompare e) => Ord (arg e) where
  compare = compCompare

instance (Composite arg,GShow e) => Show (arg e) where
  showsPrec = compShow -}

unionDescr :: Composite arg => arg Repr -> arg Repr -> Maybe (arg Repr)
unionDescr x y = runIdentity $ compCombine (\tp _ -> return tp) x y

compITE :: (Composite arg,Embed m e,Monad m,GCompare e) => e BoolType -> arg e -> arg e -> m (Maybe (arg e))
compITE cond = compCombine (\x y -> case geq x y of
                               Just Refl -> return x
                               Nothing -> ite cond x y)

compITEs :: (Composite arg,Embed m e,Monad m,GCompare e) => [(e BoolType,arg e)] -> m (Maybe (arg e))
compITEs [] = return Nothing
compITEs [(_,x)] = return (Just x)
compITEs ((c,x):xs) = do
  rest <- compITEs xs
  case rest of
    Nothing -> return Nothing
    Just rest' -> compITE c x rest'

compType :: (Composite arg,GetType e) => arg e -> arg Repr
compType = runIdentity . mapExprs (return . getType)

compTypeM :: (Composite arg,Embed m e,Monad m) => arg e -> m (arg Repr)
compTypeM = mapExprs (\x -> do
                         tp <- embedTypeOf
                         return $ tp x)

newtype EqT e m a = EqT (WriterT [e BoolType] m a) deriving (Applicative,Functor,Monad,MonadWriter [e BoolType])

instance (Embed m e,Monad m) => Embed (EqT e m) e where
  type EmVar (EqT e m) e = EmVar m e
  type EmQVar (EqT e m) e = EmQVar m e
  type EmFun (EqT e m) e = EmFun m e
  type EmFunArg (EqT e m) e = EmFunArg m e
  type EmLVar (EqT e m) e = EmLVar m e
  embed e = do
    re <- e
    EqT (lift $ embed (pure re))
  embedQuantifier q arg f
    = EqT (lift $ embedQuantifier q arg f)
  embedTypeOf = EqT (lift embedTypeOf)

compEq :: (Composite arg,Embed m e,Monad m,GCompare e) => arg e -> arg e -> m (Maybe (e BoolType))
compEq x y = do
  let EqT wr = compCombine (\vx vy -> do
                               eq <- vx .==. vy
                               tell [eq]
                               return vx) x y
  (res,eqs) <- runWriterT wr
  case res of
    Nothing -> return Nothing
    Just _ -> case eqs of
      [] -> fmap Just true
      [c] -> return $ Just c
      _ -> fmap Just $ and' eqs

createComposite :: (Composite arg,Monad m)
                => (forall t. Repr t -> RevComp arg t -> m (e t))
                -> CompDescr arg
                -> m (arg e)
createComposite f descr
  = foldExprs (\rev tp -> f tp rev) descr

revType :: Composite arg => CompDescr arg -> RevComp arg tp -> Repr tp
revType descr rev = case getRev rev descr of
  Just r -> r
  Nothing -> error $ "revType: Internal error, type for unknown element "++gshowsPrec 11 rev ""++" requested."

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
  = createComposite (\_ rev -> f rev (getRev rev x) (getRev rev y)) descr

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
