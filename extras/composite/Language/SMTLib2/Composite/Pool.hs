module Language.SMTLib2.Composite.Pool where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Container
import Language.SMTLib2.Composite.Choice as Choice
import Language.SMTLib2.Composite.Null
import Language.SMTLib2.Composite.Singleton
import Language.SMTLib2.Composite.Tuple
import Language.SMTLib2.Composite.List

import Data.Vector as Vec hiding (mapM,mapM_)
import Data.Proxy
import Data.GADT.Compare

class Composite a => PoolElement a e where
  type PoolElementCtx a e
  canFree :: PoolElementCtx a e -> a e -> Bool

class (Composite (PoolIndex p))
      => Pool (p :: ((Type -> *) -> *) -> (Type -> *) -> *) where
  type PoolIndex p :: (Type -> *) -> *
  empty :: (Embed m e,Monad m,Composite a) => m (a e) -> m (p a e)
  alloc :: (Embed m e,Monad m,PoolElement a e)
        => PoolElementCtx a e -> a e -> p a e -> m (PoolIndex p e,p a e)
  index :: (Embed m e,Monad m,Composite a)
        => PoolIndex p e -> Access (p a) ('Seq a 'Id) a m e
  elements :: Monad m
           => (forall e'. Maybe Int -> a e' -> m ())
           -> p a e
           -> m ()
  elementRev :: Composite a
             => Proxy p
             -> Proxy a
             -> (forall tp'. Maybe Int -> RevComp a tp' -> r)
             -> RevComp (p a) tp
             -> Maybe r
  indexType :: p a e -> PoolIndex p Repr
  elementType :: Composite a => p a Repr -> Maybe (a Repr)
  allSameLike :: (Composite a,Embed m e,Monad m)
              => a e
              -> p a Repr
              -> m (p a e)
  combinePoolWith :: (Embed m e,Monad m,GCompare e,Composite a)
                  => m (a e)
                  -> (a e -> a e -> m (Maybe (a e)))
                  -> p a e
                  -> p a e
                  -> m (Maybe (p a e))

instance Pool CompList where
  type PoolIndex CompList
    = Choice BoolEncoding (NoComp (Maybe Int))
  empty _ = return $ CompList Vec.empty
  alloc ctx obj (CompList objs)
    = case Vec.findIndex (canFree ctx) objs of
    Just freeIdx -> do
      cond <- true
      let nobjs = objs Vec.// [(freeIdx,obj)]
          key = initialBoolean [(NoComp $ Just freeIdx,cond)]
      return (key,CompList nobjs)
    Nothing -> do
      cond <- true
      let nobjs = Vec.snoc objs obj
          key = initialBoolean [(NoComp $ Just $ Vec.length objs,cond)]
      return (key,CompList nobjs)
  index key (CompList objs) = do
    chs <- getChoices key
    return $ AccSeq [ (ListIndex i,cond,AccId)
                    | (NoComp (Just i),cond) <- chs ]
  elements f (CompList objs) = imapM_ (\i -> f (Just i)) objs
  elementRev _ _ f (RevList i r) = Just $ f (Just i) r
  indexType (CompList objs)
    = initialBoolean $ fmap (\i -> (NoComp $ Just i,bool))
      [0..(Vec.length objs)-1]
  elementType (CompList ds) = if Vec.null ds
                              then Nothing
                              else Vec.fold1M unionDescr ds
  allSameLike def (CompList els) = return $ CompList $ fmap (const def) els
  combinePoolWith def = combineListWith (const def)
