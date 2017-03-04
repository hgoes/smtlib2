{-# LANGUAGE PolyKinds #-}
module Language.SMTLib2.Composite.Container (
  -- * Container class
  Container(..),
  -- * Paths
  Path(..),
  pathGet,
  pathSet,
  withPath,
  -- * Accessors
  Acc(..),
  Accessor(..),
  AccessorFork(..),
  withAccessor,
  access,
  accessorPaths,
  -- ** Construction
  Access,(|*>),idAcc,field,
  at,
  -- * Muxer
  Muxer(..),
  Paths(..),
  Muxed(..),
  withMuxer,
  mux,
  -- ** Construction
  (<|*>),idMux,
  -- * Helper functions
  update,updateList
  ) where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Null (NoComp(..))
import qualified Language.SMTLib2.Internals.Type.List as L
import Language.SMTLib2.Internals.Type.Nat

import Data.GADT.Compare
import Data.GADT.Show
import Data.Foldable
import Data.Functor.Identity
import Prelude hiding (read)
import Text.Show

data Acc a = Id
           | Seq a (Acc a)
           | Br [Acc a]

class Composite c => Container c where
  data Index c :: ((Type -> *) -> *) -> (Type -> *) -> *
  elementGet :: (Embed m e,Monad m,Composite el)
             => c e
             -> Index c el e
             -> m (el e)
  elementsGet :: (Embed m e,Monad m,Composite el)
              => c e
              -> [Index c el e]
              -> m [el e]
  elementsGet x = mapM (elementGet x)
  elementSet :: (Embed m e,Monad m,Composite el)
             => c e
             -> Index c el e
             -> el e
             -> m (c e)
  elementsSet :: (Embed m e,Monad m,Composite el)
              => c e
              -> [(Index c el e,el e)]
              -> m (c e)
  elementsSet c upd = foldlM (\cc (idx,el) -> elementSet cc idx el
                             ) c upd
  withElement :: (Embed m e,Monad m,Composite el)
              => c e
              -> Index c el e
              -> (el e -> m (el e))
              -> m (c e)
  withElement c idx f = do
    el <- elementGet c idx
    nel <- f el
    elementSet c idx nel
  showIndex :: GShow e => Int -> Index c el e -> ShowS

update :: (Composite a,Embed m e,Monad m,GCompare e)
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

data Path a (idx :: Acc ((Type -> *) -> *)) b e where
  PathId   :: Path a 'Id a e
  PathSeq  :: (Container a,Composite b)
           => Index a b e
           -> Path b idx c e
           -> Path a ('Seq b idx) c e
  PathBr   :: Composite b
           => Natural n
           -> Path a (L.Index idxs n) b e
           -> Path a (Br idxs) b e
  PathFun  :: (a e -> b e)
           -> (b e -> a e)
           -> Path b idx c e
           -> Path a idx c e

data AccessorFork a (idxs :: [Acc ((Type -> *) -> *)]) b e where
  NilFork :: AccessorFork a '[] b e
  Fork    :: Maybe ([e BoolType],Accessor a idx b e)
          -> AccessorFork a idxs b e
          -> AccessorFork a (idx ': idxs) b e

data Accessor a (idx :: Acc ((Type -> *) -> *)) b e where
  AccId   :: Accessor a 'Id a e
  AccSeq  :: (Container a,Composite b)
          => [(Index a b e,[e BoolType],Accessor b idx c e)]
          -> Accessor a ('Seq b idx) c e
  AccFork :: Composite b
          => AccessorFork a idxs b e
          -> Accessor a ('Br idxs) b e
  AccFun  :: (a e -> b e)
          -> (b e -> a e)
          -> Accessor b idx c e
          -> Accessor a idx c e

withAccessor :: (Embed m e,Monad m)
             => Accessor a idx b e
             -> a e
             -> (Path a idx b e -> [e BoolType] -> b e -> m (b e))
             -> m (a e)
withAccessor AccId x f = f PathId [] x
withAccessor (AccSeq acc) x f = do
  els <- elementsGet x (fmap (\(idx,_,_) -> idx) acc)
  nels <- mapM (\((idx,cond,acc),el) -> do
                   nel <- withAccessor acc el
                          (\path cond' -> f (PathSeq idx path) (cond++cond'))
                   return (idx,nel)
               ) (zip acc els)
  elementsSet x nels
withAccessor (AccFork fork) x f
  = withAccessorFork fork x (\n path -> f (PathBr n path))
  where
    withAccessorFork :: (Embed m e,Monad m)
                     => AccessorFork a idxs b e
                     -> a e
                     -> (forall n. Natural n ->
                         Path a (L.Index idxs n) b e ->
                         [e BoolType] -> b e -> m (b e))
                     -> m (a e)
    withAccessorFork NilFork x _ = return x
    withAccessorFork (Fork Nothing rest) x f
      = withAccessorFork rest x (\n -> f (Succ n))
    withAccessorFork (Fork (Just (cond,acc)) rest) x f = do
      nx <- withAccessor acc x (\path cond'
                                -> f Zero path (cond++cond'))
      withAccessorFork rest nx (\n -> f (Succ n))
withAccessor (AccFun g h acc) x f
  = fmap h $ withAccessor acc (g x) (\path -> f (PathFun g h path))

accessorPaths :: Accessor a idx b e -> [([e BoolType],Path a idx b e)]
accessorPaths AccId = [([],PathId)]
accessorPaths (AccSeq lst)
  = [ (cond++cond',PathSeq idx path)
    | (idx,cond,acc) <- lst
    , (cond',path) <- accessorPaths acc ]
accessorPaths (AccFork fork)
  = forkPaths fork
  where
    forkPaths :: (Composite b)
              => AccessorFork a idxs b e
              -> [([e BoolType],Path a ('Br idxs) b e)]
    forkPaths NilFork = []
    forkPaths (Fork f fs)
      = (case f of
           Nothing -> []
           Just (cond,acc) -> [ (cond++cond',PathBr Zero path)
                              | (cond',path) <- accessorPaths acc ])++
        [ (cond,PathBr (Succ n) path)
        | (cond,PathBr n path) <- forkPaths fs ]
accessorPaths (AccFun f g acc)
  = [ (cond,PathFun f g path)
    | (cond,path) <- accessorPaths acc ]

data Paths a (idxs :: [Acc ((Type -> *) -> *)]) bs e where
  NilPaths :: Paths a '[] '[] e
  Paths :: Path a idx b e
        -> Paths a idxs bs e
        -> Paths a (idx ': idxs) (b ': bs) e

data Muxer a (idxs :: [Acc ((Type -> *) -> *)]) bs e where
  NoMux :: Muxer a '[] '[] e
  Mux :: Accessor a idx b e
      -> Muxer a idxs bs e
      -> Muxer a (idx ': idxs) (b ': bs) e

data Muxed els (e :: Type -> *) where
  NoMuxed :: Muxed '[] e
  Muxed :: a e -> Muxed as e -> Muxed (a ': as) e

accessorHead :: Accessor a idx b e
             -> Maybe (Path a idx b e,
                       [e BoolType],
                       Accessor a idx b e)
accessorHead AccId = Nothing
accessorHead (AccSeq []) = Nothing
accessorHead (AccSeq ((idx,cond,AccId):accs))
  = Just (PathSeq idx PathId,cond,AccSeq accs)
accessorHead (AccSeq ((idx,cond,acc):accs))
  = case accessorHead acc of
  Just (path,cond',acc') -> Just (PathSeq idx path,cond++cond'
                                 ,AccSeq ((idx,cond,acc'):accs))
  Nothing -> accessorHead (AccSeq accs)
accessorHead (AccFork NilFork) = Nothing
accessorHead (AccFork (Fork Nothing rest)) = do
  (PathBr n path,cond,AccFork nrest) <- accessorHead (AccFork rest)
  return (PathBr (Succ n) path,cond,AccFork (Fork Nothing nrest))
accessorHead (AccFork (Fork (Just (cond,acc)) rest))
  = case accessorHead acc of
  Nothing -> accessorHead (AccFork (Fork Nothing rest))
  Just (path,cond',acc') -> Just (PathBr Zero path,cond++cond',
                                  AccFork (Fork (Just (cond,acc')) rest))
accessorHead (AccFun f g acc) = do
  (path,cond,acc') <- accessorHead acc
  return (PathFun f g path,cond,AccFun f g acc')

pathGet :: (Embed m e,Monad m)
        => Path a idx b e
        -> a e
        -> m (b e)
pathGet PathId x = return x
pathGet (PathSeq idx path) x = do
  nx <- elementGet x idx
  pathGet path nx
pathGet (PathBr _ path) x = pathGet path x
pathGet (PathFun f g path) x = pathGet path (f x)

pathSet :: (Embed m e,Monad m)
        => Path a idx b e
        -> a e
        -> b e
        -> m (a e)
pathSet PathId _ x = return x
pathSet (PathSeq idx path) x y = do
  el <- elementGet x idx
  nel <- pathSet path el y
  elementSet x idx nel
pathSet (PathBr _ path) x y = pathSet path x y
pathSet (PathFun f g path) x y = fmap g $ pathSet path (f x) y

withPath :: (Embed m e,Monad m)
         => Path a idx b e
         -> a e
         -> (b e -> m (b e))
         -> m (a e)
withPath PathId x f = f x
withPath (PathSeq idx path) x f = withElement x idx $
                                  \el -> withPath path el f
withPath (PathBr _ path) x f = withPath path x f
withPath (PathFun g h path) x f = fmap h $ withPath path (g x) f

withMuxer' :: (Embed m e,Monad m)
           => Muxer a idxs bs e
           -> a e
           -> st
           -> (Paths a idxs bs e -> [e BoolType] ->
               Muxed bs e -> st -> m (Muxed bs e,st))
           -> m (a e,st)
withMuxer' NoMux x st f = do
  (NoMuxed,nst) <- f NilPaths [] NoMuxed st
  return (x,nst)
withMuxer' (Mux acc accs) x st f = case accessorHead acc of
  Nothing -> return (x,st)
  Just (path,cond,acc') -> do
    el <- pathGet path x
    (x1,(nel,nst)) <- withMuxer' accs x (el,st) $
      \paths cond' muxed (el,st) -> do
        (Muxed nel nmuxed,nst) <- f (Paths path paths) (cond++cond')
                                  (Muxed el muxed) st
        return (nmuxed,(nel,nst))
    x2 <- pathSet path x1 nel
    withMuxer' (Mux acc' accs) x2 nst f

withMuxer :: (Embed m e,Monad m)
          => Muxer a idxs bs e
          -> a e
          -> (Paths a idxs bs e -> [e BoolType] ->
              Muxed bs e -> m (Muxed bs e))
          -> m (a e)
withMuxer mux x f = do
  (nx,()) <- withMuxer' mux x () $
             \paths cond muxed () -> do
               nmuxed <- f paths cond muxed
               return (nmuxed,())
  return nx

access :: (Container a,Embed m e,Monad m)
       => Access a idx b m e
       -> a e
       -> (Path a idx b e -> [e BoolType] -> b e -> m (b e))
       -> m (a e)
access getAcc x f = do
  acc <- getAcc x
  withAccessor acc x f

type Access a idx b m e = a e -> m (Accessor a idx b e)

type family PathConcats (p1 :: [Acc a]) (p2 :: Acc a) :: [Acc a] where
  PathConcats '[] ys = '[]
  PathConcats (x ': xs) ys = PathConcat x ys ': PathConcats xs ys

type family PathConcat (p1 :: Acc a) (p2 :: Acc a) :: Acc a where
  PathConcat 'Id acc = acc
  PathConcat ('Seq x xs) ys = 'Seq x (PathConcat xs ys)
  PathConcat ('Br xs) ys = 'Br (PathConcats xs ys)

(|*>) :: (Embed m e,Monad m,Composite c)
       => Access a idx1 b m e
       -> Access b idx2 c m e
       -> Access a (PathConcat idx1 idx2) c m e
(|*>) f g x = do
  acc <- f x
  concatAcc acc x g
  where
    concatAcc :: (Embed m e,Monad m,Composite c)
              => Accessor a idx1 b e
              -> a e
              -> (b e -> m (Accessor b idx2 c e))
              -> m (Accessor a (PathConcat idx1 idx2) c e)
    concatAcc AccId x f = f x
    concatAcc (AccSeq lst) x f = do
      nlst <- mapM (\(idx,cond,acc) -> do
                       nx <- elementGet x idx
                       nacc <- concatAcc acc nx f
                       return (idx,cond,nacc)
                   ) lst
      return (AccSeq nlst)
    concatAcc (AccFork fork) x f = do
      nfork <- concatFork fork x f
      return (AccFork nfork)
    concatAcc (AccFun g h acc) x f = do
      nacc <- concatAcc acc (g x) f
      return (AccFun g h nacc)

    concatFork :: (Embed m e,Monad m,Composite c)
               => AccessorFork a idx1 b e
               -> a e
               -> (b e -> m (Accessor b idx2 c e))
               -> m (AccessorFork a (PathConcats idx1 idx2) c e)
    concatFork NilFork _ _ = return NilFork
    concatFork (Fork Nothing xs) obj f = do
      xs' <- concatFork xs obj f
      return (Fork Nothing xs')
    concatFork (Fork (Just (cond,acc)) xs) obj f = do
      nacc <- concatAcc acc obj f
      nxs <- concatFork xs obj f
      return (Fork (Just (cond,nacc)) nxs)

infixr 5 |*>
  
idAcc :: Monad m => Access a 'Id a m e
idAcc _ = return AccId

at :: (Container c,Composite el,Monad m,Embed m e)
   => Index c el e -> Access c ('Seq el 'Id) el m e
at idx x = do
  el <- elementGet x idx
  return $ AccSeq [(idx,[],AccId)]

field :: Monad m => (a e -> b e) -> (b e -> a e) -> Access a 'Id b m e
field f g _ = return $ AccFun f g AccId

(<|*>) :: (Embed m e,Monad m)
       => Access a idx b m e
       -> (a e -> m (Muxer a idxs bs e))
       -> a e
       -> m (Muxer a (idx ': idxs) (b ': bs) e)
(<|*>) f g x = do
  acc <- f x
  accs <- g x
  return (Mux acc accs)

infixr 4 <|*>

idMux :: Monad m => a e -> m (Muxer a '[] '[] e)
idMux _ = return NoMux

mux :: (Embed m e,Monad m)
    => (a e -> m (Muxer a idxs bs e))
    -> a e
    -> (Paths a idxs bs e -> [e BoolType] ->
        Muxed bs e -> m (Muxed bs e))
    -> m (a e)
mux f x g = do
  muxer <- f x
  withMuxer muxer x g

updateList' :: (Embed m e,Monad m)
            => Accessor a idx b e
            -> a e
            -> m [(Path a idx b e,[e BoolType],b e,a e -> b e -> m (a e))]
updateList' AccId x = return [(PathId,[],x,const return)]
updateList' (AccSeq lst) x
  = fmap concat $
    mapM (\(idx,cond,acc) -> do
             el <- elementGet x idx
             nlst <- updateList' acc el
             return (fmap (\(path,cond',el',wr)
                           -> (PathSeq idx path,cond++cond',el',
                               \cx nel' -> withElement cx idx
                                           (\cel -> wr cel nel'))
                          ) nlst)
         ) lst
updateList' (AccFork fork) x = fromFork fork x
  where
    fromFork :: (Embed m e,Monad m,Composite b)
             => AccessorFork a idxs b e
             -> a e
             -> m [((Path a ('Br idxs) b e),[e BoolType],b e,a e -> b e -> m (a e))]
    fromFork NilFork _ = return []
    fromFork (Fork Nothing rest) x = do
      lst <- fromFork rest x
      return $ fmap (\(PathBr n path,cond,el,up)
                     -> (PathBr (Succ n) path,cond,el,up)
                    ) lst
    fromFork (Fork (Just (cond,acc)) rest) x = do
      lst1 <- updateList' acc x
      let lst1' = fmap (\(path,cond',el,up)
                        -> (PathBr Zero path,cond++cond',el,up)
                       ) lst1
      lst2 <- fromFork rest x
      let lst2' = fmap (\(PathBr n path,cond',el,up)
                        -> (PathBr (Succ n) path,cond',el,up)
                       ) lst2
      return $ lst1'++lst2'
updateList' (AccFun f g acc) x = do
  lst <- updateList' acc (f x)
  return $ fmap (\(path,cond,el,upd)
                 -> (PathFun f g path,cond,el,
                     \cx nel -> do
                       ny <- upd (f cx) nel
                       return $ g ny)
                ) lst
    
updateList :: (Embed m e,Monad m)
           => Access a idx b m e
           -> a e
           -> m [(Path a idx b e,[e BoolType],b e,a e -> b e -> m (a e))]
updateList f x = do
  acc <- f x
  updateList' acc x

instance GShow e => Show (Accessor a idx b e) where
  showsPrec _ AccId = showString "id"
  showsPrec _ (AccSeq lst)
    = showListWith (\(idx,cond,acc)
                    -> showIndex 5 idx .
                       showString ": " .
                       showListWith (gshowsPrec 0) cond .
                       showString " -> " .
                       showsPrec 5 acc) lst
  showsPrec p (AccFork fork) = showsPrec p fork
  showsPrec p (AccFun _ _ acc) = showsPrec p acc

instance GShow e => Show (AccessorFork a idxs b e) where
  showsPrec _ NilFork = showString "empty"
  showsPrec p (Fork acc fork)
    = (case acc of
         Nothing -> showString "empty"
         Just (cond,acc') -> showListWith (gshowsPrec 0) cond .
                             showString " -> " .
                             showsPrec 5 acc'
      ) .
      (case fork of
          NilFork -> id
          _ -> showString " | " .
               showsPrec 5 fork)
