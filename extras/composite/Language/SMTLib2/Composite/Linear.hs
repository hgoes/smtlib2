module Language.SMTLib2.Composite.Linear where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains as Comp
import Language.SMTLib2.Composite.Lens
import Language.SMTLib2.Composite.List
--import Language.SMTLib2.Composite.Choice (insertByWith,mergeByWith)

import Data.GADT.Compare
import Data.GADT.Show
import Control.Lens
import Data.Monoid
import Text.Show
import Data.Foldable
import Data.Proxy
import Data.List (sortBy)
import Data.Ord (comparing)

data Linear c (e :: Type -> *) = Linear { _linConst :: Value (SingletonType c)
                                        , _linear :: [(Value (SingletonType c),c e)] }

makeLenses ''Linear

data RevLinear c tp where
  RevFactor :: Integer -> RevComp c tp -> RevLinear c tp

delinear :: (IsNumeric c,Embed m e,Monad m) => Linear c e -> m (c e)
delinear lin = do
  const <- compositeFromValue $ _linConst lin
  ps <- mapM (\(c,x) -> do
                 c' <- compositeFromValue c
                 compositeMult c' x) $ _linear lin
  compositeSum $ const:ps

delinearType :: (IsNumeric c,GetType e) => Linear c e -> c Repr
delinearType lin = runIdentity $ delinear (compType lin)

newtype ByteArray arr (e :: Type -> *) = ByteArray { _byteArray :: arr e }

makeLenses ''ByteArray

instance Composite arr => Composite (ByteArray arr) where
  type RevComp (ByteArray arr) = RevComp arr
  foldExprs f (ByteArray arr) = do
    narr <- foldExprs f arr
    return $ ByteArray narr
  accessComposite r = maybeLens byteArray `composeMaybe`
                      accessComposite r
  compCombine f (ByteArray arr1) (ByteArray arr2) = do
    narr <- compCombine f arr1 arr2
    return $ fmap ByteArray narr
  revName (_::Proxy (ByteArray arr)) r = revName (Proxy::Proxy arr) r
  compCompare (ByteArray arr1) (ByteArray arr2) = compCompare arr1 arr2
  compShow p (ByteArray arr) = compShow p arr
  compInvariant (ByteArray arr) = compInvariant arr

instance Container arr => Container (ByteArray arr) where
  type ElementType (ByteArray arr) = ElementType arr
  elementType (ByteArray arr) = elementType arr

instance IsArray arr idx => IsArray (ByteArray arr) idx where
  newArray idx el = do
    arr <- newArray idx el
    return $ ByteArray arr
  select (ByteArray arr) idx = Comp.select arr idx
  store (ByteArray arr) idx el = do
    res <- Comp.store arr idx el
    case res of
      Nothing -> return Nothing
      Just narr -> return $ Just $ ByteArray narr

instance IsBounded arr idx => IsBounded (ByteArray arr) idx where
  checkIndex (ByteArray arr) = checkIndex arr

instance IsNumeric idx => IsNumeric (Linear idx) where
  compositeFromValue v = return $ Linear v []
  compositePlus (Linear c1 lin1) (Linear c2 lin2) = do
    lin <- addLin lin1 lin2
    return $ Linear (c1+c2) lin
    where
      addLin [] ys = return ys
      addLin xs [] = return xs
      addLin ((cx,x):xs) ((cy,y):ys) = case compare cx cy of
        EQ -> do
          z <- compositePlus x y
          zs <- addLin xs ys
          return $ (cx,z):zs
        LT -> do
          zs <- addLin xs ((cy,y):ys)
          return $ (cx,x):zs
        GT -> do
          zs <- addLin ((cx,x):xs) ys
          return $ (cy,y):zs
  compositeMinus (Linear c1 lin1) (Linear c2 lin2) = do
    lin <- subLin lin1 lin2
    return $ Linear (c1+c2) lin
    where
      subLin [] ys = return ys
      subLin xs [] = return xs
      subLin ((cx,x):xs) ((cy,y):ys) = case compare cx cy of
        EQ -> do
          z <- compositeMinus x y
          zs <- subLin xs ys
          return $ (cx,z):zs
        LT -> do
          zs <- subLin xs ((cy,y):ys)
          return $ (cx,x):zs
        GT -> do
          y' <- compositeNegate y
          zs <- subLin ((cx,x):xs) ys
          return $ (cy,y'):zs
  compositeNegate l = do
    nlins <- mapM (\(c,x) -> do
                      nx <- compositeNegate x
                      return (c,nx)) (_linear l)
    return $ Linear (negate $ _linConst l) nlins
  compositeMult l1 l2 = do
    let nconst = (_linConst l1)*(_linConst l2)
    nlin1 <- sequence [ do
                          z <- compositeMult x y
                          return (cx*cy,z)
                      | (cx,x) <- _linear l1
                      , (cy,y) <- _linear l2 ]
    let nlin2 = if _linConst l2==0
                then []
                else [ (cx*_linConst l2,x) | (cx,x) <- _linear l1 ]
        nlin3 = if _linConst l1==0
                then []
                else [ (cy*_linConst l1,y) | (cy,y) <- _linear l2 ]
    nlin <-  merge $ sortBy (comparing fst) $ nlin1++nlin2++nlin3
    return $ Linear nconst nlin
    where
      merge [] = return []
      merge [x] = return [x]
      merge ((cx,x):(cy,y):rest) = case compare cx cy of
        EQ -> do
          z <- compositePlus x y
          merge $ (cx,z):rest
        LT -> do
          zs <- merge $ (cy,y):rest
          return $ (cx,x):zs
  compositeGEQ (Linear c1 []) (Linear c2 []) = cbool $ c1 >= c2
  compositeGEQ l1 l2 = do
    e1 <- delinear l1
    e2 <- delinear l2
    compositeGEQ e1 e2
  compositeDiv l1 l2 = do
    e1 <- delinear l1
    e2 <- delinear l2
    res <- compositeDiv e1 e2
    return $ Linear 0 [(1,res)]
  compositeMod l1 l2 = do
    e1 <- delinear l1
    e2 <- delinear l2
    res <- compositeMod e1 e2
    return $ Linear 0 [(1,res)]

instance (IsBounded arr idx,StaticByteWidth (ElementType arr),IsNumeric idx)
         => ByteWidth (ByteArray arr) (Linear idx) where
  byteWidth (ByteArray arr) = do
    let elTp = elementType (compType arr)
        elSize = staticByteWidth elTp
    sz <- arraySize arr
    return $ Linear (fromInteger 0) [(fromInteger elSize,sz)]

instance (IsBounded arr idx,ByteAccess (ElementType arr) idx el,
           StaticByteWidth (ElementType arr),IsRanged idx,CanConcat (ElementType arr),
           StaticByteWidth el,ByteWidth el (Linear idx))
         => ByteAccess (ByteArray arr) (Linear idx) el where
  byteRead = linearByteRead
  byteWrite = linearByteWrite

linearByteRead :: (IsBounded arr idx,ByteAccess (ElementType arr) idx el,
                   StaticByteWidth (ElementType arr),IsRanged idx,CanConcat (ElementType arr),
                   Embed m e,Monad m,GetType e,GCompare e)
               => arr e -> Linear idx e -> Integer
               -> m [(Maybe (el e),e BoolType)]
linearByteRead arr off sz = do
  let offTp = delinearType off
      arrTp = compType arr
      elTp = elementType arrTp
      elWidth = staticByteWidth elTp
      elWidth' = fromInteger elWidth
      (constIdx,nconstIdx) = _linConst off `divMod` elWidth'
      linIdx = [ (c `div` elWidth',x) | (c,x) <- _linear off, c `mod` elWidth' == 0 ]
      nlinIdx = [ (c,x) | (c,x) <- _linear off, c `mod` elWidth' /= 0 ]
      sz' = fromInteger sz
  elWidth'' <- compositeFromValue elWidth'
  c1 <- delinear $ Linear constIdx linIdx
  c2 <- delinear $ Linear nconstIdx nlinIdx
  rc2 <- compositeDiv c2 elWidth''
  rest <- compositeMod c2 elWidth''
  restRange <- getRange rest
  case upperBound restRange of
    Just (Regular upper) -> do
      let loadElems = case (upper+sz') `divMod` elWidth' of
                        (num,0) -> num
                        (num,_) -> num+1
      elems <- mapM (\nidx -> do
                        nidx' <- compositeFromValue nidx
                        ridx <- compositeSum [c1,rc2,nidx']
                        Comp.select arr ridx) [0..loadElems-1]
      case sequence elems of
        Just relems -> do
          relem <- compConcat relems
          case relem of
            Nothing -> do
              cond <- true
              return [(Nothing,cond)]
            Just relem' -> byteRead relem' rest sz
    Nothing -> do
      cond <- true
      return [(Nothing,cond)]
  where
    arrTp = compType arr

linearByteWrite :: (IsBounded arr idx,ByteAccess (ElementType arr) idx el,
                    StaticByteWidth (ElementType arr),IsRanged idx,CanConcat (ElementType arr),
                    StaticByteWidth el,
                    Embed m e,Monad m,GetType e,GCompare e)
                => arr e -> Linear idx e -> el e -> m (Maybe (arr e,Maybe (e BoolType)))
linearByteWrite arr off el = do
  let offTp = delinearType off
      arrTp = compType arr
      elTp = elementType arrTp
      elWidth = staticByteWidth elTp
      elWidth' = fromInteger elWidth
      (constIdx,nconstIdx) = _linConst off `divMod` elWidth'
      linIdx = [ (c `div` elWidth',x) | (c,x) <- _linear off, c `mod` elWidth' == 0 ]
      nlinIdx = [ (c,x) | (c,x) <- _linear off, c `mod` elWidth' /= 0 ]
      sz = staticByteWidth el
      sz' = fromInteger sz
  elWidth'' <- compositeFromValue elWidth'
  c1 <- delinear $ Linear constIdx linIdx
  c2 <- delinear $ Linear nconstIdx nlinIdx
  rc2 <- compositeDiv c2 elWidth''
  rest <- compositeMod c2 elWidth''
  restRange <- getRange rest
  case upperBound restRange of
    Just (Regular upper) -> do
      let loadElems = case (upper+sz') `divMod` elWidth' of
                        (num,0) -> num
                        (num,_) -> num+1
      elems <- mapM (\nidx -> do
                        nidx' <- compositeFromValue nidx
                        ridx <- compositeSum [c1,rc2,nidx']
                        Comp.select arr ridx) [0..loadElems-1]
      case sequence elems of
        Just relems -> do
          res <- withConcat (\e -> do
                                res <- byteWrite e rest el
                                case res of
                                  Nothing -> do
                                    cond <- true
                                    return (Just cond,e)
                                  Just (ne,err) -> return (err,ne)
                            ) relems
          case res of
            Nothing -> return Nothing
            Just (err,nelems) -> do
              narr <- foldlM (\carr (nel,idx) -> do
                                 idx' <- compositeFromValue idx
                                 ridx <- compositeSum [c1,rc2,idx']
                                 res <- Comp.store carr ridx nel
                                 case res of
                                   Nothing -> return carr
                                   Just narr -> return narr
                             ) arr (zip nelems [0..])
              return $ Just (narr,err)

instance (IsNumeric c) => Composite (Linear c) where
  type RevComp (Linear c) = RevLinear c
  foldExprs f (Linear c facs) = do
    nfacs <- mapM (\(n,(c,v)) -> do
                      nv <- foldExprs (f . RevFactor n) v
                      return (c,nv)) $ zip [0..] facs
    return $ Linear c nfacs
  accessComposite (RevFactor i r)
    = maybeLens linear `composeMaybe`
      listElement' i `composeMaybe`
      maybeLens _2 `composeMaybe`
      accessComposite r
  compCombine f (Linear c1 lin1) (Linear c2 lin2)
    = case compare c1 c2 of
    EQ -> do
      nl <- mergeFactors f lin1 lin2
      case nl of
        Just nlin -> return $ Just $ Linear c1 nlin
        Nothing -> return Nothing
    LT -> do
      v <- compositeFromValue (fromInteger 1)
      nl2 <- mergeFactors f [(c2-c1,v)] lin2
      case nl2 of
        Just nlin2 -> do
          nl <- mergeFactors f lin1 nlin2
          case nl of
            Just nlin -> return $ Just $ Linear c1 nlin
            Nothing -> return Nothing
        Nothing -> return Nothing
    GT -> do
      v <- compositeFromValue (fromInteger 1)
      nl1 <- mergeFactors f [(c1-c2,v)] lin1
      case nl1 of
        Just nlin1 -> do
          nl <- mergeFactors f nlin1 lin2
          case nl of
            Just nlin -> return $ Just $ Linear c2 nlin
            Nothing -> return Nothing
        Nothing -> return Nothing
  compCompare (Linear c1 lin1) (Linear c2 lin2)
    = compare c1 c2 `mappend`
      comp lin1 lin2
    where
      comp [] [] = EQ
      comp [] _ = LT
      comp _ [] = GT
      comp ((cx,x):xs) ((cy,y):ys)
        = compare cx cy `mappend`
          compCompare x y `mappend`
          comp xs ys
  compShow p (Linear c lins) = showParen (p>10) $
    showString "Linear " .
    showsPrec 11 c . showChar ' ' .
    showListWith (\(c,v) -> showsPrec 10 c . showChar '*' . compShow 10 v) lins

instance (IsRanged c,IsNumeric c) => IsRanged (Linear c) where
  getRange (Linear c lin) = do
    let rc = rangedConst c
    rlin <- mapM (\(c,x) -> do
                     rx <- getRange x
                     return $ (rangedConst c) `rangeMult` rx) lin
    return $ foldl rangeAdd rc rlin

instance IsNumeric c => IsSingleton (Linear c) where
  type SingletonType (Linear c) = SingletonType c
  getSingleton (Linear c lin) = do
    ec <- compositeFromValue c
    elin <- mapM (\(c,x) -> do
                     rc <- compositeFromValue c
                     compositeMult rc x) lin
    res <- compositeSum $ ec:elin
    getSingleton res

instance (IsNumeric c,IsConstant c) => IsConstant (Linear c) where
  getConstant (Linear c lin) = do
    nlins <- mapM (\(c,x) -> do
                      rx <- getConstant x
                      return $ c*rx) lin
    return $ sum $ c:nlins

mergeFactors :: (Composite c,Embed m e,Monad m,GetType e,GCompare e)
             => (forall tp. e tp -> e tp -> m (e tp))
             -> [(Value tp,c e)]
             -> [(Value tp,c e)]
             -> m (Maybe [(Value tp,c e)])
mergeFactors _ [] ys = return $ Just ys
mergeFactors _ xs [] = return $ Just xs
mergeFactors f ((c1,x):xs) ((c2,y):ys) = case compare c1 c2 of
  EQ -> do
    z <- compCombine f x y
    case z of
      Just z' -> do
        zs <- mergeFactors f xs ys
        case zs of
          Just zs' -> return $ Just $ (c1,z'):zs'
          Nothing -> return Nothing
      Nothing -> return Nothing
  LT -> do
    rest <- mergeFactors f xs ((c2,y):ys)
    case rest of
      Just rest' -> return $ Just $ (c1,x):rest'
      Nothing -> return Nothing
  GT -> do
    rest <- mergeFactors f ((c1,x):xs) ys
    case rest of
      Just rest' -> return $ Just $ (c2,y):rest'
      Nothing -> return Nothing

instance Composite c => GEq (RevLinear c) where
  geq (RevFactor i1 r1) (RevFactor i2 r2)
    = if i1==i2
      then geq r1 r2
      else Nothing

instance Composite c => GCompare (RevLinear c) where
  gcompare (RevFactor i1 r1) (RevFactor i2 r2) = case compare i1 i2 of
    LT -> GLT
    GT -> GGT
    EQ -> gcompare r1 r2

instance Composite c => Show (RevLinear c tp) where
  showsPrec p (RevFactor i r) = showParen (p>10) $
    showString "RevFactor " .
    showsPrec 11 i . showChar ' ' .
    gshowsPrec 11 r

instance Composite c => GShow (RevLinear c) where
  gshowsPrec = showsPrec
