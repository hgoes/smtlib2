module Language.SMTLib2.Composite.Linear where

import Language.SMTLib2
import Language.SMTLib2.Composite.Class
import Language.SMTLib2.Composite.Domains as Comp
import Language.SMTLib2.Composite.List

import Data.GADT.Compare
import Data.GADT.Show
import Data.Monoid
import Text.Show
import Data.Foldable
import Data.Proxy
import Data.List (sortBy,unzip3)
import Data.Ord (comparing)
import qualified Data.Map as Map
import Data.Functor.Identity

data Linear c (e :: Type -> *) = Linear { linConst :: c Value
                                        , linear :: [(c Value,c e)] }

data RevLinear c tp where
  RevFactor :: Integer -> RevComp c tp -> RevLinear c tp

delinear :: (IsNumeric c,Embed m e,Monad m) => Linear c e -> m (c e)
delinear lin = do
  const' <- mapExprs constant (linConst lin)
  ps <- mapM (\(c,x) -> do
                 c' <- mapExprs constant c
                 Just r <- compositeMult c' x
                 return r
             ) $ linear lin
  Just res <- compositeSum $ const':ps
  return res

delinearType :: (IsNumeric c,GetType e) => Linear c e -> c Repr
delinearType lin = runIdentity $ delinear (compType lin)

newtype ByteArray arr (e :: Type -> *) = ByteArray { byteArray :: arr e }

instance Composite arr => Composite (ByteArray arr) where
  type RevComp (ByteArray arr) = RevComp arr
  foldExprs f (ByteArray arr) = do
    narr <- foldExprs f arr
    return $ ByteArray narr
  mapExprs f (ByteArray arr) = do
    narr <- mapExprs f arr
    return $ ByteArray narr
  getRev r (ByteArray arr) = getRev r arr
  setRev r x arr = fmap ByteArray $ setRev r x (fmap byteArray arr)
  compCombine f (ByteArray arr1) (ByteArray arr2) = do
    narr <- compCombine f arr1 arr2
    return $ fmap ByteArray narr
  revName (_::Proxy (ByteArray arr)) r = revName (Proxy::Proxy arr) r
  compCompare (ByteArray arr1) (ByteArray arr2) = compCompare arr1 arr2
  compShow p (ByteArray arr) = compShow p arr
  compInvariant (ByteArray arr) = compInvariant arr

instance Wrapper arr => Wrapper (ByteArray arr) where
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

instance IsStaticBounded arr => IsStaticBounded (ByteArray arr) where
  checkStaticIndex (ByteArray arr) = checkStaticIndex arr

instance IsBounded arr idx => IsBounded (ByteArray arr) idx where
  checkIndex (ByteArray arr) = checkIndex arr

instance IsNumeric idx => IsNumeric (Linear idx) where
  compositePlus (Linear c1 lin1) (Linear c2 lin2) = do
    lin <- addLin lin1 lin2
    case lin of
      Just lin' -> case runIdentity $ compositePlus c1 c2 of
        Just nc -> return $ Just $ Linear nc lin'
        Nothing -> return Nothing
      Nothing -> return Nothing
    where
      addLin [] ys = return $ Just ys
      addLin xs [] = return $ Just xs
      addLin ((cx,x):xs) ((cy,y):ys) = case compCompare cx cy of
        EQ -> do
          z <- compositePlus x y
          case z of
            Nothing -> return Nothing
            Just z' -> do
              zs <- addLin xs ys
              case zs of
                Nothing -> return Nothing
                Just zs' -> return $ Just $ (cx,z'):zs'
        LT -> do
          zs <- addLin xs ((cy,y):ys)
          case zs of
            Nothing -> return Nothing
            Just zs' -> return $ Just $ (cx,x):zs'
        GT -> do
          zs <- addLin ((cx,x):xs) ys
          case zs of
            Nothing -> return Nothing
            Just zs' -> return $ Just $ (cy,y):zs'
  compositeMinus (Linear c1 lin1) (Linear c2 lin2) = do
    lin <- subLin lin1 lin2
    case lin of
      Nothing -> return Nothing
      Just lin' -> case runIdentity $ compositeMinus c1 c2 of
        Nothing -> return Nothing
        Just nc -> return $ Just $ Linear nc lin'
    where
      subLin [] ys = return $ Just ys
      subLin xs [] = return $ Just xs
      subLin ((cx,x):xs) ((cy,y):ys) = case compCompare cx cy of
        EQ -> do
          z <- compositeMinus x y
          case z of
            Nothing -> return Nothing
            Just z' -> do
              zs <- subLin xs ys
              case zs of
                Nothing -> return Nothing
                Just zs' -> return $ Just $ (cx,z'):zs'
        LT -> do
          zs <- subLin xs ((cy,y):ys)
          case zs of
            Nothing -> return Nothing
            Just zs' -> return $ Just $ (cx,x):zs'
        GT -> do
          y' <- compositeNegate y
          case y' of
            Nothing -> return Nothing
            Just y'' -> do
              zs <- subLin ((cx,x):xs) ys
              case zs of
                Nothing -> return Nothing
                Just zs' -> return $ Just $ (cy,y''):zs'
  {-compositeNegate l = do
    nlins <- mapM (\(c,x) -> do
                      nx <- compositeNegate x
                      return (c,nx)) (_linear l)
    return $ Linear (runIdentity $ compositeNegate $ _linConst l) nlins
  compositeMult l1 l2 = do
    let nconst = runIdentity $ compositeMult (_linConst l1) (_linConst l2)
    nlin1 <- sequence [ do
                          z <- compositeMult x y
                          return (runIdentity $ compositeMult cx cy,z)
                      | (cx,x) <- _linear l1
                      , (cy,y) <- _linear l2 ]
    let nlin2 = case compCompare (_linConst l2)
                     (runIdentity $ foldExprs (const constant) $
                      compositeFromInteger 0 (compType $ _linConst l2)) of
                  EQ -> []
                  _ -> [ (runIdentity $ compositeMult cx (_linConst l2),x)
                       | (cx,x) <- _linear l1 ]
        nlin3 = case compCompare (_linConst l1)
                     (runIdentity $ foldExprs (const constant) $
                      compositeFromInteger 0 (compType $ _linConst l2)) of
                  EQ -> []
                  _ -> [ (runIdentity $ compositeMult cy (_linConst l1),y)
                       | (cy,y) <- _linear l2 ]
    nlin <-  merge $ sortBy (\(x,_) (y,_) -> compCompare x y) $ nlin1++nlin2++nlin3
    return $ Linear nconst nlin
    where
      merge [] = return []
      merge [x] = return [x]
      merge ((cx,x):(cy,y):rest) = case compCompare cx cy of
        EQ -> do
          z <- compositePlus x y
          merge $ (cx,z):rest
        LT -> do
          zs <- merge $ (cy,y):rest
          return $ (cx,x):zs
  compositeGEQ (Linear c1 []) (Linear c2 []) = constant $ runIdentity $ compositeGEQ c1 c2
  compositeGEQ l1 l2 = do
    e1 <- delinear l1
    e2 <- delinear l2
    compositeGEQ e1 e2
  compositeDiv l1 l2 = do
    e1 <- delinear l1
    e2 <- delinear l2
    res <- compositeDiv e1 e2
    return $ Linear (compositeFromInteger 0 (compType e1))
      [(compositeFromInteger 1 (compType e1),res)]
  compositeMod l1 l2 = do
    e1 <- delinear l1
    e2 <- delinear l2
    res <- compositeMod e1 e2
    return $ Linear (compositeFromInteger 0 (compType e1))
      [(compositeFromInteger 1 (compType e1),res)]-}

instance (IsBounded arr idx,StaticByteWidth (ElementType arr),IsNumeric idx)
         => ByteWidth (ByteArray arr) (Linear idx) where
  byteWidth (ByteArray arr) (Linear r _) = do
    let elTp = elementType (compType arr)
        elSize = staticByteWidth elTp
        Just zero = compositeFromInteger 0 (compType r)
        Just elSize' = compositeFromInteger elSize (compType r)
    sz <- arraySize arr
    return $ Linear zero [(elSize',sz)]

{-instance (IsStaticBounded arr,
          --StaticByteAccess (ElementType arr) el,
          StaticByteWidth (ElementType arr),
          CanConcat el,
          StaticByteWidth el)
         => StaticByteAccess (ByteArray arr) el where
  staticByteRead (ByteArray arr) off sz = do
    let arrTp = compType arr
        elTp = elementType arrTp
        elWidth = staticByteWidth elTp
        largestIdx = case (off+sz) `divMod` elWidth of
          (res,0) -> res-1
          (res,_) -> res
        (startIdx,off) = off `divMod` elWidth
    safety <- checkStaticIndex arr largestIdx
    safetyCond <- case safety of
      NoError -> return Nothing
      SometimesError c -> return $ Just c
      AlwaysError -> fmap Just true
    res <- read arr (indexType arr) startIdx off sz
    case res of
      Just el -> return $ Just (el,0)
      Nothing -> return Nothing
    where
      read arr tp idx off sz = do
        idx' <- foldExprs (const constant) $
                compositeFromInteger idx tp
        el <- Comp.select arr idx'
        case el of
          Nothing -> return Nothing
          Just el' -> do
            res <- staticByteRead el' off sz
            case res of
              Nothing -> return Nothing
              Just (el,0) -> return (Just el)
              Just (el,rest) -> do
                nel <- read arr tp (idx+1) 0 rest
                case nel of
                  Nothing -> return Nothing
                  Just nel' -> compConcat [el,nel']
  staticByteWrite (ByteArray arr) idx el = do
    wr <- staticByteWrite arr idx el
    let arrTp = compType arr
        elTp = elementType arrTp
        sz = staticByteWidth el
        elWidth = staticByteWidth elTp
        largestIdx = case (idx+sz) `divMod` elWidth of
          (res,0) -> res-1
          (res,_) -> res
    case wr of
      Nothing -> return Nothing
      Just (narr,outside) -> do
        safety <- checkStaticIndex arr largestIdx
        safetyCond <- case safety of
          NoError -> return Nothing
          SometimesError c -> return $ Just c
          AlwaysError -> fmap Just true
        noutside <- case outside of
          Nothing -> return safetyCond
          Just c1 -> case safetyCond of
            Nothing -> return $ Just c1
            Just c2 -> fmap Just $ c1 .&. c2
        return $ Just (ByteArray narr,noutside)-}

{-instance (StaticByteAccess arr el,
          IsBounded arr idx,ByteAccess (ElementType arr) idx el,
          StaticByteWidth (ElementType arr),IsRanged idx,IsNumSingleton idx,
          StaticByteAccess (ElementType arr) el,
          CanConcat el,
          StaticByteWidth el,ByteWidth el (Linear idx))
         => ByteAccess (ByteArray arr) (Linear idx) el where
  byteRead = linearByteRead
  byteWrite = linearByteWrite

linearByteRead :: (IsBounded arr idx,ByteAccess (ElementType arr) idx el,
                   StaticByteWidth (ElementType arr),IsRanged idx,IsNumSingleton idx,
                   StaticByteAccess (ElementType arr) el,
                   CanConcat el,
                   Embed m e,Monad m,GetType e,GCompare e)
               => arr e -> Linear idx e -> Integer
               -> m (ByteRead el e)
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
  (c2,rest) <- case nlinIdx of
    [] -> if nconstIdx==0
          then return (Nothing,Nothing)
          else do
      c <- compositeFromValue nconstIdx
      return (Nothing,Just c)
    _ -> do
      c <- delinear $ Linear nconstIdx nlinIdx
      rc2 <- compositeDiv c elWidth''
      rest <- compositeMod c elWidth''
      return (Just rc2,Just rest)
  (objs,imprec,largestIdx) <- read arr c1 c2 [0..] rest sz
  nobjs <- mapM (\(obj,cond) -> do
                    nobj <- compConcat obj
                    return (nobj,cond)) objs
  let nobjs' = [ (obj,cond) | (Just obj,cond) <- nobjs ]
  imprec' <- sequence [ case cond of
                          [] -> true
                          [c] -> return c
                          _ -> and' cond
                      | (Nothing,cond) <- nobjs ]
  nimprec <- case imprec' ++ imprec of
    [] -> return Nothing
    [x] -> return $ Just x
    xs -> fmap Just $ or' xs
  res <- ites nobjs'
  case res of
    Nothing -> do
      cond <- true
      return $ impreciseRead cond
    Just res -> do
      largestIdx' <- compositeFromValue largestIdx
      maxIdx <- compositeSum ([c1]++(case c2 of
                                       Nothing -> []
                                       Just c -> [c])++[largestIdx'])
      safety <- checkIndex arr maxIdx
      safetyCond <- case safety of
        NoError -> return Nothing
        SometimesError c -> return $ Just c
        AlwaysError -> fmap Just true
      return $ ByteRead Map.empty safetyCond res nimprec
  where
    ites [] = return $ Just Nothing
    ites [(x,_)] = return (Just (Just x))
    ites ((x,c):xs) = case c of
      [] -> return $ Just (Just x)
      _ -> do
        c' <- case c of
          [c] -> return c
          _ -> and' c
        rest <- ites xs
        case rest of
          Nothing -> return Nothing
          Just (Just rest') -> do
            result <- compITE c' x rest'
            case result of
              Nothing -> return Nothing
              Just res -> return $ Just $ Just res

    read :: (IsBounded arr idx,ByteAccess (ElementType arr) idx el,
             StaticByteWidth (ElementType arr),IsRanged idx,
             StaticByteAccess (ElementType arr) el,
             Embed m e,Monad m,GCompare e,GetType e
            ) => arr e -> idx e -> Maybe (idx e) -> [Value (SingletonType idx)] -> Maybe (idx e) -> Integer
         -> m ([([el e],[e BoolType])],[e BoolType],Value (SingletonType idx))
    read arr c1 c2 (i:is) rest sz = do
      idx <- compositeFromValue i
      idx' <- compositeSum ([c1]++(case c2 of
                                     Nothing -> []
                                     Just c -> [c])++[idx])
      el <- Comp.select arr idx'
      case el of
        Nothing -> do
          cond <- true
          return ([],[cond],i)
        Just el' -> do
          res <- case rest of
                   Just rest' -> byteRead el' rest' sz
                   Nothing -> staticByteRead el' 0 sz >>= toByteRead
          overs <- sequence [ do
                                (res,imprec,largestIdx) <- read arr c1 c2 is Nothing remaining
                                nres <- mapM (\(objs,conds) -> return (incompl:objs,cond:conds)) res
                                return (nres,imprec,largestIdx)
                            | (remaining,(incompl,cond)) <- Map.toList (overreads res) ]
          let (objs1,imprecs1,idxs) = unzip3 overs
              imprecs2 = case readImprecision res of
                Nothing -> []
                Just c -> [c]
          objs2 <- case fullRead res of
            Nothing -> return []
            Just obj -> do
              cond <- fullReadCond res
              return [([obj],cond)]
          case readOutside res of
            Nothing -> return (objs2++concat objs1,imprecs2++concat imprecs1,maximum (i:idxs))
            Just _ -> error "linearByteRead: Internal error."

linearByteWrite :: (IsBounded arr idx,ByteAccess (ElementType arr) idx el,
                    StaticByteWidth (ElementType arr),IsRanged idx,IsNumSingleton idx,
                    StaticByteWidth el,StaticByteAccess (ElementType arr) el,
                    Embed m e,Monad m,GetType e,GCompare e)
                => arr e -> Linear idx e -> el e -> m (ByteWrite arr el e)
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
  (c2,rest) <- case nlinIdx of
    [] -> if nconstIdx==0
          then return (Nothing,Nothing)
          else do
      c <- compositeFromValue nconstIdx
      return (Nothing,Just c)
    _ -> do
      c <- delinear $ Linear nconstIdx nlinIdx
      rc2 <- compositeDiv c elWidth''
      rest <- compositeMod c elWidth''
      return (Just rc2,Just rest)
  (narr,imprec,largestIdx) <- write arr c1 c2 [0..] rest el []
  nimprec <- case imprec of
    [] -> return Nothing
    [x] -> return $ Just x
    xs -> fmap Just $ or' xs
  largestIdx' <- compositeFromValue largestIdx
  maxIdx <- compositeSum ([c1]++(case c2 of
                                   Nothing -> []
                                   Just c -> [c])++[largestIdx'])
  safety <- checkIndex arr maxIdx
  safetyCond <- case safety of
    NoError -> return Nothing
    SometimesError c -> return $ Just c
    AlwaysError -> fmap Just true
  return $ ByteWrite [] safetyCond (Just narr) nimprec
  where
    write :: (IsBounded arr idx,ByteAccess (ElementType arr) idx el,
              StaticByteWidth (ElementType arr),IsRanged idx,
              StaticByteAccess (ElementType arr) el,
              Embed m e,Monad m,GCompare e,GetType e)
          => arr e -> idx e -> Maybe (idx e) -> [Value (SingletonType idx)] -> Maybe (idx e) -> el e
          -> [e BoolType]
          -> m (arr e,[e BoolType],Value (SingletonType idx))
    write arr c1 c2 (i:is) rest wr conds = do
      idx <- compositeFromValue i
      idx' <- compositeSum ([c1]++(case c2 of
                                     Nothing -> []
                                     Just c -> [c])++[idx])
      el <- Comp.select arr idx'
      case el of
        Nothing -> do
          cond <- true
          return (arr,[cond],i)
        Just el' -> do
          res <- case rest of
            Just rest' -> byteWrite el' rest' wr
            Nothing -> staticByteWrite el' 0 wr >>= toByteWrite
          arr1 <- case fullWrite res of
            Nothing -> return arr
            Just nel -> case conds of
              [] -> do
                res <- Comp.store arr idx' nel
                case res of
                  Just n -> return n
                  Nothing -> error "linearByteWrite: Internal error."
              [x] -> do
                res <- Comp.storeCond arr x idx' nel
                case res of
                  Just n -> return n
                  Nothing -> error "linearByteWrite: Internal error."
              _ -> do
                cond <- and' conds
                res <- Comp.storeCond arr cond idx' nel
                case res of
                  Just n -> return n
                  Nothing -> error "linearByteWrite: Internal error."
          (arr2,imprec1,max1) <- foldlM (\(carr,cimprec,cmax) (nwr,cond) -> do
                                            (narr,nimprec,nmax) <- write carr c1 c2 is Nothing nwr (cond:conds)
                                            return (narr,cimprec++nimprec,max cmax nmax)
                                        ) (arr1,[],i) (overwrite res)
          let imprec2 = case writeImprecision res of
                Nothing -> []
                Just c -> [c]
          return (arr2,imprec1++imprec2,max1)-}

instance (IsNumeric c) => Composite (Linear c) where
  type RevComp (Linear c) = RevLinear c
  foldExprs f (Linear c facs) = do
    nfacs <- mapM (\(n,(c,v)) -> do
                      nv <- foldExprs (f . RevFactor n) v
                      return (c,nv)) $ zip [0..] facs
    return $ Linear c nfacs
  mapExprs f (Linear c facs) = do
    nfacs <- mapM (\(c,v) -> do
                      nv <- mapExprs f v
                      return (c,nv)) facs
    return $ Linear c nfacs
  getRev (RevFactor i r) (Linear _ lst) = do
    (_,el) <- safeGenericIndex lst i
    getRev r el
  setRev (RevFactor i r) x (Just (Linear c lst)) = do
    nlst <- safeGenericUpdateAt Nothing i (\(cy,y) -> do
                                              ny <- setRev r x (Just y)
                                              return (cy,ny)) lst
    return $ Linear c nlst
  setRev _ _ Nothing = Nothing
  compCombine f (Linear c1 lin1) (Linear c2 lin2)
    = case compCompare c1 c2 of
    EQ -> do
      nl <- mergeFactors f lin1 lin2
      case nl of
        Just nlin -> return $ Just $ Linear c1 nlin
        Nothing -> return Nothing
    LT -> do
      let Just one = compositeFromInteger 1 (compType c1)
      v <- mapExprs constant one
      let Just nc = runIdentity $ compositeMinus c2 c1
      nl2 <- mergeFactors f [(nc,v)] lin2
      case nl2 of
        Just nlin2 -> do
          nl <- mergeFactors f lin1 nlin2
          case nl of
            Just nlin -> return $ Just $ Linear c1 nlin
            Nothing -> return Nothing
        Nothing -> return Nothing
    GT -> do
      let Just one = compositeFromInteger 1 (compType c1)
      v <- mapExprs constant one
      let Just nc = runIdentity $ compositeMinus c1 c2
      nl1 <- mergeFactors f [(nc,v)] lin1
      case nl1 of
        Just nlin1 -> do
          nl <- mergeFactors f nlin1 lin2
          case nl of
            Just nlin -> return $ Just $ Linear c2 nlin
            Nothing -> return Nothing
        Nothing -> return Nothing
  compCompare (Linear c1 lin1) (Linear c2 lin2)
    = compCompare c1 c2 `mappend`
      comp lin1 lin2
    where
      comp [] [] = EQ
      comp [] _ = LT
      comp _ [] = GT
      comp ((cx,x):xs) ((cy,y):ys)
        = compCompare cx cy `mappend`
          compCompare x y `mappend`
          comp xs ys
  compShow p (Linear c lins) = showParen (p>10) $
    showString "Linear " .
    compShow 11 c . showChar ' ' .
    showListWith (\(c,v) -> compShow 10 c . showChar '*' . compShow 10 v) lins
  compIsSubsetOf f (Linear c1 lin1) (Linear c2 lin2)
    = compIsSubsetOf (==) c1 c2 &&
      length lin1 == length lin2 &&
      all (\((c1,v1),(c2,v2))
           -> compIsSubsetOf (==) c1 c2 &&
              compIsSubsetOf f v1 v2
          ) (zip lin1 lin2)

{-instance (IsRanged c,IsNumSingleton c) => IsRanged (Linear c) where
  getRange (Linear c lin) = do
    let rc = rangedConst c
    rlin <- mapM (\(c,x) -> do
                     rx <- getRange x
                     case asFiniteRange rx of
                       Nothing -> return $ (rangedConst c) `rangeMult` rx
                       Just rxs -> return $ rangeFromList (getType c) (fmap (*c) rxs)
                 ) lin
    return $ foldl rangeAdd rc rlin

instance (IsNumeric c,IsSingleton c) => IsSingleton (Linear c) where
  type SingletonType (Linear c) = SingletonType c
  getSingleton (Linear c lin) = do
    ec <- compositeFromValue c
    elin <- mapM (\(c,x) -> do
                     rc <- compositeFromValue c
                     compositeMult rc x) lin
    res <- compositeSum $ ec:elin
    getSingleton res
  compositeFromValue v = return $ Linear v []

instance (IsNumSingleton c,IsConstant c) => IsConstant (Linear c) where
  getConstant (Linear c lin) = do
    nlins <- mapM (\(c,x) -> do
                      rx <- getConstant x
                      return $ c*rx) lin
    return $ sum $ c:nlins-}

mergeFactors :: (IsNumeric c,Embed m e,Monad m,GCompare e)
             => (forall tp. e tp -> e tp -> m (e tp))
             -> [(c Value,c e)]
             -> [(c Value,c e)]
             -> m (Maybe [(c Value,c e)])
mergeFactors _ [] ys = return $ Just ys
mergeFactors _ xs [] = return $ Just xs
mergeFactors f ((c1,x):xs) ((c2,y):ys) = case compCompare c1 c2 of
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
