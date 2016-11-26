module Language.SMTLib2.Composite.Container
  (Container(..),Iterable(..),(|*>),(<|*>),Accessor(..),Accessors(..),Muxer(..),IdxPath(..),IdxPaths(..),Muxed(..),
   at,update,field,lensA,focusAccessor,mapAccessor,depAcc,getUpdateList) where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Null (NoComp(..))

import Data.GADT.Compare
import Data.Foldable
#if MIN_VERSION_base(4,9,0)
import Data.Functor.Const
#endif
import Data.Functor.Identity
import Prelude hiding (read)

class Container (c :: ((Type -> *) -> *) -> (Type -> *) -> *) where
  type CIndex c :: (Type -> *) -> *
  elementGet :: (Embed m e,Monad m,GetType e,Composite a)
             => CIndex c e -> c a e -> m (a e)
  elementSet :: (Embed m e,Monad m,GetType e,Composite a)
             => CIndex c e -> a e -> c a e -> m (c a e)

#if !MIN_VERSION_base(4,9,0)
newtype Const a b = Const { getConst :: a } deriving Functor
#endif

at :: (Container c,Embed m e,Monad m,GetType e,Composite a)
   => CIndex c e
   -> Accessor (c a) (CIndex c) a m e
at idx = Accessor { accessorGet = \cont -> do
                      el <- elementGet idx cont
                      return [(idx,[],el)]
                  , accessorSet = \els cont
                                  -> foldlM (\cont (idx,el)
                                              -> elementSet idx el cont
                                            ) cont els
                  }

update :: (Composite a,Embed m e,Monad m,GetType e,GCompare e)
       => a e -> [e BoolType] -> a e -> m (a e)
update x [] _ = return x
update x cs y = do
  cond <- case cs of
    [c] -> return c
    _ -> and' cs
  res <- compITE cond x y
  case res of
    Nothing -> error $ "Container.update: Incompatible element written."
    Just res' -> return res'

field :: Monad m => (a e -> b e) -> (b e -> a e -> a e) -> Accessor a (NoComp ()) b m e
field get set = Accessor { accessorGet = \x -> return [(NoComp (),[],get x)]
                         , accessorSet = \upd x -> return $
                                                   foldl' (\cx (_,el)
                                                           -> set el cx
                                                          ) x upd }

lensA :: Monad m
      => (forall f. Functor f => (b e -> f (b e)) -> a e -> f (a e))
      -> Accessor a (NoComp ()) b m e
lensA l = Accessor { accessorGet = \x -> return [(NoComp (),[],getConst (l Const x))]
                   , accessorSet = \upd x -> return $
                                             foldl' (\cx (_,el)
                                                     -> runIdentity $ l (\_ -> Identity el) cx
                                                    ) x upd
                   }

data Accessor a idx b m e
  = Accessor { accessorGet :: a e -> m [(idx e,[e BoolType],b e)]
             , accessorSet :: [(idx e,b e)] -> a e -> m (a e) }

data Accessors a idxs b m e where
  NilAcc  :: Accessors a '[] a m e
  ConsAcc :: Accessor a idx b m e
          -> Accessors b idxs c m e
          -> Accessors a ('(idx,b) ': idxs) c m e

data Muxer a paths els m e where
  NoMux :: Muxer a '[] '[] m e
  Mux :: Accessors a path b m e
      -> Muxer a paths els m e
      -> Muxer a (path ': paths) (b ': els) m e

data IdxPath i a path b (e :: Type -> *) where
  NilIdx  :: IdxPath i a '[] a e
  ConsIdx :: [(idx e,i,b e,IdxPath i b path c e)]
          -> IdxPath i a ('(idx,b) ': path) c e

data IdxPaths i a paths bs (e :: Type -> *) where
  NilPaths  :: IdxPaths i a '[] '[] e
  ConsPaths :: IdxPath i a path b e
            -> IdxPaths i a paths bs e
            -> IdxPaths i a (path ': paths) (b ': bs) e

data Muxed els (e :: Type -> *) where
  NilMuxed :: Muxed '[] e
  Muxed    :: a e -> Muxed as e -> Muxed (a ': as) e

withAccessors :: Monad m
              => Accessors a idxs b m e
              -> a e
              -> ([e BoolType] -> b e -> m (b e))
              -> m (a e)
withAccessors acc x f = do
  path <- accessorsGet acc x
  npath <- withPath path f
  accessorsSet acc npath x

withPath :: (Monoid i,Monad m)
         => IdxPath i a path b e
         -> (i -> b e -> m (b e))
         -> m (IdxPath i a path b e)
withPath p f = do
  res <- withPathHead p (\c h t -> do
                            nh <- f c h
                            nt <- withPath t f
                            return ((),nh,nt)
                        )
  case res of
    Nothing -> return p
    Just ((),np) -> return np

accessorsGet :: Monad m
             => Accessors a idxs b m e
             -> a e
             -> m (IdxPath [e BoolType] a idxs b e)
accessorsGet NilAcc x = return NilIdx
accessorsGet (ConsAcc acc accs) x = do
  els <- accessorGet acc x
  fmap ConsIdx $
    mapM (\(idx,cond,el) -> do
             path <- accessorsGet accs el
             return (idx,cond,el,path)
         ) els

accessorsSet :: Monad m
             => Accessors a idxs b m e
             -> IdxPath i a idxs b e
             -> a e
             -> m (a e)
accessorsSet NilAcc NilIdx x = return x
accessorsSet (ConsAcc acc accs) (ConsIdx els) x = do
  nels <- mapM (\(idx,_,el,path) -> do
                   nel <- accessorsSet accs path el
                   return (idx,nel)
               ) els
  accessorSet acc nels x

pathHead :: Monoid i
         => IdxPath i a path b e
         -> Maybe (i,b e,IdxPath i a path b e)
pathHead NilIdx = Nothing
pathHead (ConsIdx []) = Nothing
pathHead (ConsIdx ((idx,cond,el,NilIdx):xs))
  = Just (cond,el,ConsIdx xs)
pathHead (ConsIdx ((idx,cond,el,path):xs)) = case pathHead path of
  Just (cond',res,path') -> Just (mappend cond cond',res,
                                  ConsIdx ((idx,cond,el,path'):xs))
  Nothing -> pathHead (ConsIdx xs)

pathHead' :: (Monoid i,Monad m)
          => Accessors a path b m e
          -> IdxPath i a path b e
          -> Maybe (i,b e,b e -> a e -> m (a e),IdxPath i a path b e)
pathHead' _ NilIdx = Nothing
pathHead' _ (ConsIdx []) = Nothing
pathHead' (ConsAcc acc NilAcc) (ConsIdx ((idx,cond,el,NilIdx):xs))
  = Just (cond,el,\nel -> accessorSet acc [(idx,nel)],ConsIdx xs)
pathHead' (ConsAcc acc accs) (ConsIdx ((idx,cond,el,path):xs))
  = case pathHead' accs path of
  Just (cond',res,f,path')
    -> Just (mappend cond cond',res,
             \new src -> do
               nel <- f new el
               accessorSet acc [(idx,nel)] src,
             ConsIdx ((idx,cond,el,path'):xs))
  Nothing -> pathHead' (ConsAcc acc accs) (ConsIdx xs)

withPathHead :: (Monoid i,Monad m)
             => IdxPath i a path b e
             -> (i -> b e -> IdxPath i a path b e ->
                 m (res,b e,IdxPath i a path b e))
             -> m (Maybe (res,IdxPath i a path b e))
withPathHead NilIdx _ = return Nothing
withPathHead (ConsIdx []) _ = return Nothing
withPathHead (ConsIdx ((idx,cond,el,NilIdx):xs)) f = do
  (res,nel,ConsIdx nxs) <- f cond el (ConsIdx xs)
  return $ Just (res,ConsIdx ((idx,cond,nel,NilIdx):nxs))
withPathHead (ConsIdx ((idx,cond,el,path):xs)) f = do
  r1 <- withPathHead path (\cond' phead ptail -> do
                              (res,nhead,ConsIdx ((nidx,ncond,nel,npath):nxs))
                                <- f (mappend cond cond') phead
                                   (ConsIdx ((idx,cond,el,ptail):xs))
                              return ((res,(nidx,ncond,nel,nxs)),nhead,npath)
                          )
  case r1 of
    Just ((res,(nidx,ncond,nel,nxs)),npath)
      -> return $ Just (res,ConsIdx ((nidx,ncond,nel,npath):nxs))
    Nothing -> do
      r2 <- withPathHead (ConsIdx xs) f
      case r2 of
        Nothing -> return Nothing
        Just (res,ConsIdx nxs)
          -> return $ Just (res,ConsIdx ((idx,cond,el,path):nxs))

combine :: (Monad m,Monoid i)
        => c
        -> IdxPaths i a paths bs e
        -> (c -> i -> Muxed bs e -> m (c,Muxed bs e))
        -> m (c,IdxPaths i a paths bs e)
combine c NilPaths f = do
  (nc,NilMuxed) <- f c mempty NilMuxed
  return (nc,NilPaths)
combine c (ConsPaths p ps) f = do
  res <- withPathHead p
         (\cond phead ptail -> do
             ((c1,nhead),ps1)
               <- combine (c,phead) ps
                  (\(c,phead) cond' row -> do
                      (nc,Muxed nhead nrow)
                        <- f c (mappend cond cond')
                           (Muxed phead row)
                      return ((nc,nhead),nrow))
             (c2,ConsPaths ntail ps2)
               <- combine c1 (ConsPaths ptail ps1) f
             return ((c2,ps2),nhead,ntail)
         )
  case res of
    Just ((nc,nps),np) -> return (nc,ConsPaths np nps)
    Nothing -> return (c,ConsPaths p ps)

withMux :: Monad m
        => Muxer a paths els m e
        -> a e
        -> ([e BoolType] -> Muxed els e -> m (Muxed els e))
        -> m (a e)
withMux muxer x f = do
  paths <- muxerGet muxer x
  ((),npaths) <- combine () paths (\_ cond m -> do
                                      nm <- f cond m
                                      return ((),nm)
                                  )
  muxerSet muxer npaths x

muxerGet :: Monad m
         => Muxer a paths els m e
         -> a e
         -> m (IdxPaths [e BoolType] a paths els e)
muxerGet NoMux _ = return NilPaths
muxerGet (Mux acc accs) x = do
  p <- accessorsGet acc x
  ps <- muxerGet accs x
  return (ConsPaths p ps)

muxerSet :: Monad m
         => Muxer a paths els m e
         -> IdxPaths [e BoolType] a paths els e
         -> a e
         -> m (a e)
muxerSet NoMux NilPaths x = return x
muxerSet (Mux acc accs) (ConsPaths p ps) x = do
  nx <- accessorsSet acc p x
  muxerSet accs ps nx

depAcc :: (a e -> Accessor a idx b m e)
       -> Accessor a idx b m e
depAcc f = Accessor get set
  where
    get x = accessorGet (f x) x
    set upd x = accessorSet (f x) upd x

mapAccessor :: Monad m
            => (b e -> a e)
            -> (a e -> b e -> b e)
            -> Accessor a idx c m e
            -> Accessor b idx c m e
mapAccessor f g acc = Accessor get set
  where
    get x = accessorGet acc (f x)
    set upd x = do
      y <- accessorSet acc upd (f x)
      return $ g y x

focusAccessor :: Monad m
              => (forall f. Functor f => (b e -> f (b e)) -> a e -> f (a e))
              -> Accessor b idx c m e
              -> Accessor a idx c m e
focusAccessor l acc = Accessor get set
  where
    get x = accessorGet acc (getConst (l Const x))
    set upd x = do
      y <- accessorSet acc upd (getConst (l Const x))
      return $ runIdentity $ l (\_ -> return y) x

class Iterable it where
  data It it :: (Type -> *) -> *
  type ItSrc it :: (Type -> *) -> *
  type ItTrg it :: (Type -> *) -> *
  with :: Monad m
       => it m e
       -> ItSrc it e
       -> ([e BoolType] -> ItTrg it e -> m (ItTrg it e))
       -> m (ItSrc it e)
  read :: Monad m => it m e -> ItSrc it e -> m (It it e)
  write :: Monad m => it m e -> It it e -> ItSrc it e -> m (ItSrc it e)
  toList :: It it e -> [([e BoolType],ItTrg it e)]
  toUpdateList :: Monad m => it m e -> It it e
               -> [([e BoolType],ItTrg it e,
                    ItTrg it e -> ItSrc it e -> m (ItSrc it e))]

getUpdateList :: (Iterable it,Monad m)
              => it m e
              -> ItSrc it e
              -> m [([e BoolType],ItTrg it e,
                     ItTrg it e -> ItSrc it e -> m (ItSrc it e))]
getUpdateList acc src = do
  it <- read acc src
  return $ toUpdateList acc it

instance Iterable (Accessor a idx b) where
  newtype It (Accessor a idx b) e = Iterator [(idx e,[e BoolType],b e)]
  type ItSrc (Accessor a idx b) = a
  type ItTrg (Accessor a idx b) = b
  with acc x f = do
    els <- accessorGet acc x
    nels <- mapM (\(idx,cond,el) -> do
                     nel <- f cond el
                     return (idx,nel)
                 ) els
    accessorSet acc nels x
  read acc src = do
    els <- accessorGet acc src
    return $ Iterator els
  write acc (Iterator els) src
    = accessorSet acc (fmap (\(idx,_,el) -> (idx,el)) els) src
  toList (Iterator els) = fmap (\(_,cond,el) -> (cond,el)) els
  toUpdateList acc (Iterator els)
    = fmap (\(idx,cond,el)
            -> (cond,el,\nel -> accessorSet acc [(idx,nel)])
           ) els

instance Iterable (Accessors a idx b) where
  newtype It (Accessors a idx b) e = Iterators (IdxPath [e BoolType] a idx b e)
  type ItSrc (Accessors a idx b) = a
  type ItTrg (Accessors a idx b) = b
  with = withAccessors
  read acc src = fmap Iterators $ accessorsGet acc src
  write acc (Iterators it) = accessorsSet acc it
  toList (Iterators it) = toList' it
    where
      toList' it = case pathHead it of
        Nothing -> []
        Just (cond,el,it') -> (cond,el):toList' it'
  toUpdateList acc (Iterators it) = toList' acc it
    where
      toList' acc it = case pathHead' acc it of
        Nothing -> []
        Just (cond,el,upd,nit) -> (cond,el,upd):toList' acc nit
      
instance Iterable (Muxer a paths els) where
  newtype It (Muxer a paths els) e
    = MuxIterator (IdxPaths [e BoolType] a paths els e)
  type ItSrc (Muxer a paths els) = a
  type ItTrg (Muxer a paths els) = Muxed els
  with = withMux
  read mux src = fmap MuxIterator $ muxerGet mux src
  write mux (MuxIterator it) = muxerSet mux it

class (Iterable it,Iterable (LinResult it a idx)
      ) => LinIterable it a idx where
  type LinResult it a idx :: (* -> *) -> (Type -> *) -> *
  (|*>) :: Accessor a idx (ItSrc it) m e
        -> it m e
        -> LinResult it a idx m e

infixr 5 |*>

instance LinIterable (Accessor b idx2 c) a idx1 where
  type LinResult (Accessor b idx2 c) a idx1
    = Accessors a '[ '(idx1,b), '(idx2,c) ] c
  (|*>) acc1 acc2 = ConsAcc acc1 (ConsAcc acc2 NilAcc)

instance LinIterable (Accessors b idx2 c) a idx1 where
  type LinResult (Accessors b idx2 c) a idx1
    = Accessors a ( '(idx1,b) ': idx2) c
  (|*>) acc1 acc2 = ConsAcc acc1 acc2

class (Iterable a,Iterable b,Iterable (ParResult a b)
      ) => ParIterable a b where
  type ParResult a b :: (* -> *) -> (Type -> *) -> *
  (<|*>) :: a m e -> b m e -> ParResult a b m e

infixr 4 <|*>

instance ParIterable (Accessor a idx1 b) (Accessor a idx2 c) where
  type ParResult (Accessor a idx1 b) (Accessor a idx2 c)
    = Muxer a '[ '[ '(idx1,b)],'[ '(idx2,c)]] '[b,c]
  (<|*>) acc1 acc2 = Mux (ConsAcc acc1 NilAcc)
                     (Mux (ConsAcc acc2 NilAcc) NoMux)

instance ParIterable (Accessor a idx1 b) (Accessors a idx2 c) where
  type ParResult (Accessor a idx1 b) (Accessors a idx2 c)
    = Muxer a '[ '[ '(idx1,b)],idx2] '[b,c]
  (<|*>) acc1 acc2 = Mux (ConsAcc acc1 NilAcc)
                     (Mux acc2 NoMux)

instance ParIterable (Accessor a idx1 b) (Muxer a idx2 els) where
  type ParResult (Accessor a idx1 b) (Muxer a idx2 els)
    = Muxer a ( '[ '(idx1,b)] ': idx2) (b ': els)
  (<|*>) acc1 acc2 = Mux (ConsAcc acc1 NilAcc) acc2

instance ParIterable (Accessors a idx1 b) (Accessor a idx2 c) where
  type ParResult (Accessors a idx1 b) (Accessor a idx2 c)
    = Muxer a '[ idx1, '[ '(idx2,c)] ] '[b,c]
  (<|*>) acc1 acc2 = Mux acc1 (Mux (ConsAcc acc2 NilAcc) NoMux)

instance ParIterable (Accessors a idx1 b) (Accessors a idx2 c) where
  type ParResult (Accessors a idx1 b) (Accessors a idx2 c)
    = Muxer a '[idx1,idx2] '[b,c]
  (<|*>) acc1 acc2 = Mux acc1 (Mux acc2 NoMux)

instance ParIterable (Accessors a idx1 b) (Muxer a idx2 els) where
  type ParResult (Accessors a idx1 b) (Muxer a idx2 els)
    = Muxer a (idx1 ': idx2) (b ': els)
  (<|*>) acc1 acc2 = Mux acc1 acc2
