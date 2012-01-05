{-# LANGUAGE FlexibleInstances,OverloadedStrings,MultiParamTypeClasses,TemplateHaskell,RankNTypes,TypeFamilies #-}
module Language.SMTLib2.Instances(lispToExprT,lispToExprU,getInterpolants,getProof) where

import Language.SMTLib2.Internals
import Language.SMTLib2.TH
import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.Array
import Data.Word
import Numeric
import Data.Char
import Data.Bits
import Data.Text as T
import Data.Ratio
import Data.Typeable
import Control.Monad.State (get)
import Data.Map as Map

-- Integer

instance SMTType Integer where
  type SMTAnnotation Integer = ()
  getSort _ = L.Symbol "Int"
  declareType u = [(typeOf u,return ())]

instance SMTValue Integer where
  unmangle (L.Number (L.I v)) _ = return $ Just v
  unmangle (L.List [L.Symbol "-"
                   ,L.Number (L.I v)]) _ = return $ Just $ - v
  unmangle e _ = return Nothing
  mangle v
    | v < 0 = L.List [L.Symbol "-"
                     ,L.toLisp (-v)]
    | otherwise = L.toLisp v

instance SMTArith Integer

instance Num (SMTExpr Integer) where
  fromInteger = constant
  (+) x y = plus [x,y]
  (-) = minus
  (*) x y = mult [x,y]
  negate = neg
  abs = abs'

instance SMTOrd Integer where
  (.<.) = Lt
  (.<=.) = Le
  (.>.) = Gt
  (.>=.) = Ge

-- Real

instance SMTType (Ratio Integer) where
  type SMTAnnotation (Ratio Integer) = ()
  getSort _ = L.Symbol "Real"
  declareType u = [(typeOf u,return ())]

instance SMTValue (Ratio Integer) where
  unmangle (L.Number (L.I v)) _ = return $ Just $ fromInteger v
  unmangle (L.Number (L.D v)) _ = return $ Just $ realToFrac v
  unmangle (L.List [L.Symbol "/"
                   ,x
                   ,y]) _ = do
                          q <- unmangle x Nothing
                          r <- unmangle y Nothing
                          return (do
                                     qq <- q
                                     rr <- r
                                     return $ qq / rr)
  unmangle (L.List [L.Symbol "-",r]) ann = do
    res <- unmangle r ann
    return (fmap (\x -> -x) res)
  unmangle _ _ = return Nothing
  mangle v = L.List [L.Symbol "/"
                    ,L.Symbol $ T.pack $ (show $ numerator v)++".0"
                    ,L.Symbol $ T.pack $ (show $ denominator v)++".0"]

instance SMTArith (Ratio Integer)

instance Num (SMTExpr (Ratio Integer)) where
  fromInteger = constant.fromInteger
  (+) x y = plus [x,y]
  (-) = minus
  (*) x y = mult [x,y]
  negate = neg
  abs = abs'

instance Fractional (SMTExpr (Ratio Integer)) where
  (/) = divide
  fromRational = constant

instance SMTOrd (Ratio Integer) where
  (.<.) = Lt
  (.<=.) = Le
  (.>.) = Gt
  (.>=.) = Ge

-- Arrays

instance (SMTType idx,SMTType val) => SMTType (Array idx val) where
  type SMTAnnotation (Array idx val) = ()
  getSort u = L.List [L.Symbol "Array"
                     ,getSort (getIdx u)
                     ,getSort (getVal u)]
    where
      getIdx :: Array i v -> i
      getIdx _ = undefined
      getVal :: Array i v -> v
      getVal _ = undefined
  declareType u = [(mkTyConApp (mkTyCon "Data.Array.Array") [],return ())] ++
                  declareType (getIdx u) ++
                  declareType (getVal u)
    where
      getIdx :: Array i v -> i
      getIdx _ = undefined
      getVal :: Array i v -> v
      getVal _ = undefined


-- BitVectors

bv :: Integer -> L.Lisp
bv n = L.List [L.Symbol "_"
              ,L.Symbol "BitVec"
              ,L.Number $ L.I n]

instance SMTType Word8 where
  type SMTAnnotation Word8 = ()
  getSort _ = bv 8
  declareType u = [(typeOf u,return ())]

withUndef1 :: (a -> g a) -> g a
withUndef1 f = f undefined

getBVValue :: (Num a,Bits a,Read a) => L.Lisp -> b -> SMT (Maybe a)
getBVValue (L.Number (L.I v)) _ = return $ Just (fromInteger v)
getBVValue (L.Symbol s) _ = return $ case T.unpack s of
  '#':'b':rest -> withUndef1 (\u -> if Prelude.length rest == bitSize u
                                    then (let [(v,_)] = readInt 2 (\x -> x=='0' || x=='1') (\x -> if x=='0' then 0 else 1) rest 
                                          in Just v)
                                    else Nothing)
  '#':'x':rest -> withUndef1 (\u -> if Prelude.length rest == ((bitSize u) `div` 4)
                                    then (let [(v,_)] = readHex rest
                                          in Just v)
                                    else Nothing)
  _ -> Nothing
getBVValue (L.List [L.Symbol "_",L.Symbol val,L.Number (L.I bits)]) _
  = return $ withUndef1 (\u -> if bits == (fromIntegral $ bitSize u)
                               then (case T.unpack val of
                                        'b':'v':num -> Just (read num)
                                        _ -> Nothing)
                               else Nothing)
getBVValue _ _ = return Nothing

putBVValue :: Bits a => a -> L.Lisp
putBVValue x = L.Symbol (T.pack ('#':'b':[ if testBit x i
                                           then '1'
                                           else '0' | i <- Prelude.reverse [0..((bitSize x)-1)] ]))

instance SMTValue Word8 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word8

instance SMTOrd Word8 where
  (.<.) = BVULT
  (.<=.) = BVULE
  (.>.) = BVUGT
  (.>=.) = BVUGE

instance SMTType Word16 where
  type SMTAnnotation Word16 = ()
  getSort _ = bv 16
  declareType u = [(typeOf u,return ())]

instance SMTValue Word16 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word16

instance SMTOrd Word16 where
  (.<.) = BVULT
  (.<=.) = BVULE
  (.>.) = BVUGT
  (.>=.) = BVUGE

instance SMTType Word32 where
  type SMTAnnotation Word32 = ()
  getSort _ = bv 32
  declareType u = [(typeOf u,return ())]

instance SMTValue Word32 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word32

instance SMTOrd Word32 where
  (.<.) = BVULT
  (.<=.) = BVULE
  (.>.) = BVUGT
  (.>=.) = BVUGE

instance SMTType Word64 where
  type SMTAnnotation Word64 = ()
  getSort _ = bv 64
  declareType u = [(typeOf u,return ())]
  
instance SMTValue Word64 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word64

instance SMTOrd Word64 where
  (.<.) = BVULT
  (.<=.) = BVULE
  (.>.) = BVUGT
  (.>=.) = BVUGE

instance Num (SMTExpr Word8) where
  fromInteger = constant.fromInteger
  (+) = bvadd
  (-) = bvsub
  (*) = bvmul

instance Num (SMTExpr Word16) where
  fromInteger = constant.fromInteger
  (+) = bvadd
  (-) = bvsub
  (*) = bvmul

instance Num (SMTExpr Word32) where
  fromInteger = constant.fromInteger
  (+) = bvadd
  (-) = bvsub
  (*) = bvmul

instance Num (SMTExpr Word64) where
  fromInteger = constant.fromInteger
  (+) = bvadd
  (-) = bvsub
  (*) = bvmul

-- Arguments

instance SMTType a => Args (SMTExpr a) a where
  createArgs c = let n1 = T.pack $ "f"++show c
                     v1 = Var n1 Nothing
                     t1 = getSort $ getUndef v1
                 in (v1,[(n1,t1)],c+1)
  unpackArgs e _ c = let (e',c') = exprToLisp e c
                     in ([e'],c)
  foldExprs f s x = f s x
  allOf x = x

instance (SMTType a,SMTType b) => Args (SMTExpr a,SMTExpr b) (a,b) where
  createArgs c = let n1 = T.pack $ "f"++show c
                     n2 = T.pack $ "f"++show (c+1)
                     v1 = Var n1 Nothing
                     v2 = Var n2 Nothing
                     t1 = getSort $ getUndef v1
                     t2 = getSort $ getUndef v2
                 in ((v1,v2),[(n1,t1),(n2,t2)],c+2)
  unpackArgs (e1,e2) _ c = let (r1,c1) = exprToLisp e1 c
                               (r2,c2) = exprToLisp e2 c1
                           in ([r1,r2],c2)
  foldExprs f s (e1,e2) = let (s1,e1') = f s e1
                              (s2,e2') = f s1 e2
                          in (s2,(e1',e2'))
  allOf x = (x,x)

instance (SMTType a,SMTType b,SMTType c) => Args (SMTExpr a,SMTExpr b,SMTExpr c) (a,b,c) where
  createArgs c = let n1 = T.pack $ "f"++show c
                     n2 = T.pack $ "f"++show (c+1)
                     n3 = T.pack $ "f"++show (c+2)
                     v1 = Var n1 Nothing
                     v2 = Var n2 Nothing
                     v3 = Var n3 Nothing
                     t1 = getSort $ getUndef v1
                     t2 = getSort $ getUndef v2
                     t3 = getSort $ getUndef v3
                 in ((v1,v2,v3),[(n1,t1),(n2,t2),(n3,t3)],c+3)
  unpackArgs (e1,e2,e3) _ c = let (r1,c1) = exprToLisp e1 c
                                  (r2,c2) = exprToLisp e2 c1
                                  (r3,c3) = exprToLisp e3 c2
                              in ([r1,r2,r3],c3)
  foldExprs f s (e1,e2,e3) = let (s1,e1') = f s e1
                                 (s2,e2') = f s1 e2
                                 (s3,e3') = f s2 e3
                             in (s3,(e1',e2',e3'))
  allOf x = (x,x,x)

instance SMTType a => SMTType (Maybe a) where
  type SMTAnnotation (Maybe a) = ()
  getSort u = L.List [L.Symbol "Maybe",getSort (undef u)]
    where
      undef :: Maybe a -> a
      undef _ = undefined
  declareType u = let rec = declareType (undef u)
                  in [(mkTyConApp (mkTyCon "Maybe") [],
                       declareDatatypes ["a"] [("Maybe",[("Nothing",[]),("Just",[("fromJust",L.Symbol "a")])])])] ++
                     rec
    where
      undef :: Maybe a -> a
      undef _ = undefined

instance SMTValue a => SMTValue (Maybe a) where
  unmangle (L.Symbol "Nothing") _ = return $ Just Nothing
  unmangle (L.List [L.Symbol "as"
                   ,L.Symbol "Nothing"
                   ,_]) _ = return $ Just Nothing
  unmangle (L.List [L.Symbol "Just"
                   ,res]) _ = do
    r <- unmangle res Nothing
    return (fmap Just r)
  unmangle _ _ = return Nothing
  mangle u@Nothing = L.List [L.Symbol "as"
                            ,L.Symbol "Nothing"
                            ,getSort u]
  mangle (Just x) = L.List [L.Symbol "Just"
                           ,mangle x]

undefArg :: b a -> a
undefArg _ = undefined

instance (Typeable a,SMTType a) => SMTType [a] where
  type SMTAnnotation [a] = ()
  getSort u = L.List [L.Symbol "List",getSort (undefArg u)]
  declareType u = (typeOf u,return ()):declareType (undefArg u)

instance (Typeable a,SMTValue a) => SMTValue [a] where
  unmangle (L.Symbol "nil") _ = return $ Just []
  unmangle (L.List [L.Symbol "insert",h,t]) _ = do
    h' <- unmangle h Nothing
    t' <- unmangle t Nothing
    return (do
               hh <- h'
               tt <- t'
               return $ hh:tt)
  unmangle _ _ = return Nothing
  mangle [] = L.Symbol "nil"
  mangle (x:xs) = L.List [L.Symbol "insert"
                         ,mangle x
                         ,mangle xs]

withUndef :: TypeRep -> (forall a. (SMTValue a,Typeable a) => a -> b) -> b
withUndef rep f
  | rep == typeOf (undefined :: Bool) = f (undefined::Bool)
  | rep == typeOf (undefined :: Integer) = f (undefined::Integer)
  | rep == typeOf (undefined :: Word8) = f (undefined::Word8)
  | rep == typeOf (undefined :: Word16) = f (undefined::Word16)
  | rep == typeOf (undefined :: Word32) = f (undefined::Word32)
  | rep == typeOf (undefined :: Word64) = f (undefined::Word64)
  | otherwise = error $ "Language.SMTLib2.Instances.withUndef not implemented for "++show rep

asType :: a -> g a -> g a
asType = const id

binT :: (SMTValue b1,Typeable b1,SMTValue b2,Typeable b2,SMTValue c,Typeable c) => (forall a. (SMTValue a,Typeable a) => SMTExpr a -> SMT d)
        -> (SMTExpr b1 -> SMTExpr b2 -> SMTExpr c) -> (T.Text -> TypeRep) -> L.Lisp -> L.Lisp -> SMT (Maybe d)
binT f con g lhs rhs = do
  lhs' <- lispToExprT g lhs
  rhs' <- lispToExprT g rhs
  res <- f (con lhs' rhs')
  return $ Just res

lispToExprU :: (forall a. (SMTValue a,Typeable a) => SMTExpr a -> SMT b)
               -> (T.Text -> TypeRep)
               -> L.Lisp -> SMT (Maybe b)
lispToExprU f g l
  = firstJust [(unmangle l Nothing :: SMT (Maybe Bool)) >>= maybe (return Nothing) (fmap Just . f . Const)
              ,(unmangle l Nothing :: SMT (Maybe Integer)) >>= maybe (return Nothing) (fmap Just . f . Const)
              ,(unmangle l Nothing :: SMT (Maybe Word8)) >>= maybe (return Nothing) (fmap Just . f . Const)
              ,(unmangle l Nothing :: SMT (Maybe Word16)) >>= maybe (return Nothing) (fmap Just . f . Const)
              ,(unmangle l Nothing :: SMT (Maybe Word32)) >>= maybe (return Nothing) (fmap Just . f . Const)
              ,(unmangle l Nothing :: SMT (Maybe Word64)) >>= maybe (return Nothing) (fmap Just . f . Const)
              ,case l of
                L.Symbol name -> withUndef (g name) $ \u -> fmap Just $ f $ asType u (Var name Nothing)
                L.List [L.Symbol "=",lhs,rhs] -> do
                  lhs' <- lispToExprU (\lhs' -> do
                                          rhs' <- lispToExprT g rhs
                                          f (Eq lhs' rhs')) g lhs
                  case lhs' of
                    Just r -> return $ Just r
                    Nothing -> lispToExprU (\rhs' -> do
                                               lhs' <- lispToExprT g lhs
                                               f (Eq lhs' rhs')) g rhs
                L.List [L.Symbol ">",lhs,rhs] -> binT f (Gt::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) g lhs rhs
                L.List [L.Symbol ">=",lhs,rhs] -> binT f (Ge::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) g lhs rhs
                L.List [L.Symbol "<",lhs,rhs] -> binT f (Lt::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) g lhs rhs
                L.List [L.Symbol "<=",lhs,rhs] -> binT f (Le::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool) g lhs rhs
                L.List (L.Symbol "+":args) -> fmap Just $ mapM (lispToExprT g) args >>= f . (Plus::[SMTExpr Integer] -> SMTExpr Integer)
                L.List [L.Symbol "-",lhs,rhs] -> binT f (Minus::SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer) g lhs rhs
                L.List (L.Symbol "*":args) -> fmap Just $ mapM (lispToExprT g) args >>= f . (Mult::[SMTExpr Integer] -> SMTExpr Integer)
                L.List [L.Symbol "/",lhs,rhs] -> binT f Div g lhs rhs
                L.List [L.Symbol "mod",lhs,rhs] -> binT f Mod g lhs rhs
                L.List (L.Symbol "and":args) -> fmap Just $ mapM (lispToExprT g) args >>= f . And
                L.List (L.Symbol "or":args) -> fmap Just $ mapM (lispToExprT g) args >>= f . Or
                L.List [L.Symbol "not",arg] -> fmap Just $ (lispToExprT g arg :: SMT (SMTExpr Bool)) >>= f
                L.List [L.Symbol "bvule",lhs,rhs] -> fmap Just $ binBV BVULE g lhs rhs >>= f
                L.List [L.Symbol "bvult",lhs,rhs] -> fmap Just $ binBV BVULT g lhs rhs >>= f
                L.List [L.Symbol "bvuge",lhs,rhs] -> fmap Just $ binBV BVUGE g lhs rhs >>= f
                L.List [L.Symbol "bvugt",lhs,rhs] -> fmap Just $ binBV BVUGT g lhs rhs >>= f
                L.List [L.Symbol "bvsle",lhs,rhs] -> fmap Just $ binBV BVSLE g lhs rhs >>= f
                L.List [L.Symbol "bvslt",lhs,rhs] -> fmap Just $ binBV BVSLT g lhs rhs >>= f
                L.List [L.Symbol "bvsge",lhs,rhs] -> fmap Just $ binBV BVSGE g lhs rhs >>= f
                L.List [L.Symbol "bvsgt",lhs,rhs] -> fmap Just $ binBV BVSGT g lhs rhs >>= f
                L.List (L.Symbol fn:args) -> fmap Just $ fnToExpr f g fn args
              ]

asBV :: Typeable a => (forall b. (SMTBV b,Typeable b) => SMTExpr b -> c) -> SMTExpr a -> c
asBV f e = case (gcast e :: Maybe (SMTExpr Word8)) of
  Just r -> f r
  Nothing -> case (gcast e :: Maybe (SMTExpr Word16)) of
    Just r -> f r
    Nothing -> case (gcast e :: Maybe (SMTExpr Word32)) of
      Just r -> f r
      Nothing -> case (gcast e :: Maybe (SMTExpr Word64)) of
        Just r -> f r
        Nothing -> error $ "Cannot treat expression of type "++show (typeOf e)++" as bitvector"

fnToExpr :: (forall a. (SMTValue a,Typeable a) => SMTExpr a -> SMT b)
            -> (T.Text -> TypeRep)
            -> Text -> [L.Lisp] -> SMT b
fnToExpr f g fn args = case splitTyConApp $ g fn of
  (_,[targs,res]) -> withUndef res $ \res' -> case splitTyConApp targs of
    (_,rargs) -> case rargs of
      [] -> let [a0] = args in withUndef targs $ \t0' -> do
        p0 <- lispToExprT g a0
        f $ asType res' $ App (Fun fn) (asType t0' p0)
      [t0,t1] -> let [a0,a1] = args in withUndef t0 $ \t0' ->
        withUndef t1 $ \t1' -> do
          p0 <- lispToExprT g a0
          p1 <- lispToExprT g a1
          f $ asType res' $ App (Fun fn) (asType t0' p0,
                                          asType t1' p1)
      [t0,t1,t2] -> let [a0,a1,a2] = args in withUndef t0 $ \t0' ->
        withUndef t1 $ \t1' -> 
        withUndef t2 $ \t2' -> do
          p0 <- lispToExprT g a0
          p1 <- lispToExprT g a1
          p2 <- lispToExprT g a2
          f $ asType res' $ App (Fun fn) (asType t0' p0,
                                          asType t1' p1,
                                          asType t2' p2)

fgcast :: (Typeable a,Typeable b) => L.Lisp -> c a -> c b
fgcast l x = case gcast x of
  Just r -> r
  Nothing -> error $ "Type error in expression "++show l

binBV :: (forall a. (SMTBV a,Typeable a) => SMTExpr a -> SMTExpr a -> SMTExpr b) -> (T.Text -> TypeRep) -> L.Lisp -> L.Lisp -> SMT (SMTExpr b)
binBV f g lhs rhs = do
  r0 <- lispToExprU (asBV (\lhs0 -> do
                              rhs0 <- lispToExprT g rhs
                              return $ f lhs0 rhs0
                          )) g lhs
  case r0 of
    Just r -> return r
    Nothing -> do
      r1 <- lispToExprU (asBV (\rhs1 -> do
                                  lhs1 <- lispToExprT g lhs
                                  return $ f lhs1 rhs1
                              )) g rhs
      case r1 of
        Just r -> return r
        Nothing -> error $ "Parsing bitvector expression failed"

lispToExprT :: (SMTValue a,Typeable a) => (T.Text -> TypeRep) -> L.Lisp -> SMT (SMTExpr a)
lispToExprT g l = do
  ll <- unmangle l Nothing
  case ll of
    Just v -> return $ Const v
    Nothing -> case l of
      L.Symbol name -> return $ Var name Nothing
      L.List [L.Symbol "=",lhs,rhs] -> do
        lhs' <- lispToExprU (\lhs' -> do
                                rhs' <- lispToExprT g rhs
                                return $ fgcast l $ Eq lhs' rhs') g lhs
        case lhs' of
          Just r -> return r
          Nothing -> do
            rhs' <- lispToExprU (\rhs' -> do
                                    lhs' <- lispToExprT g lhs
                                    return $ fgcast l $ Eq lhs' rhs') g rhs
            case rhs' of
              Just r -> return r
              Nothing -> error $ "Failed to parse expression "++show l
      L.List [L.Symbol ">",lhs,rhs] -> do
        l' <- lispToExprT g lhs
        r' <- lispToExprT g rhs
        return $ fgcast l $ Gt (l' :: SMTExpr Integer) r'
      L.List [L.Symbol ">=",lhs,rhs] -> do
        l' <- lispToExprT g lhs
        r' <- lispToExprT g rhs
        return $ fgcast l $ Ge (l' :: SMTExpr Integer) r'
      L.List [L.Symbol "<",lhs,rhs] -> do
        l' <- lispToExprT g lhs
        r' <- lispToExprT g rhs
        return $ fgcast l $ Lt (l' :: SMTExpr Integer) r'
      L.List [L.Symbol "<=",lhs,rhs] -> do
        l' <- lispToExprT g lhs
        r' <- lispToExprT g rhs
        return $ fgcast l $ Le (l' :: SMTExpr Integer) r'
      L.List (L.Symbol "+":args) -> do
        args' <- mapM (lispToExprT g) args
        return $ fgcast l $ Plus (args' :: [SMTExpr Integer])
      L.List [L.Symbol "-",lhs,rhs] -> do
        l' <- lispToExprT g lhs
        r' <- lispToExprT g rhs
        return $ fgcast l $ Minus (l' :: SMTExpr Integer) r'
      L.List (L.Symbol "*":args) -> do
        args' <- mapM (lispToExprT g) args
        return $ fgcast l $ Mult (args' :: [SMTExpr Integer])
      L.List [L.Symbol "/",lhs,rhs] -> do
        l' <- lispToExprT g lhs
        r' <- lispToExprT g rhs
        return $ fgcast l $ Div l' r'
      L.List [L.Symbol "mod",lhs,rhs] -> do
        l' <- lispToExprT g lhs
        r' <- lispToExprT g rhs
        return $ fgcast l $ Mod l' r'
      L.List (L.Symbol "and":args) -> do
        args' <- mapM (lispToExprT g) args
        return $ fgcast l $ And args'
      L.List (L.Symbol "or":args) -> do
        args' <- mapM (lispToExprT g) args
        return $ fgcast l $ Or args'
      L.List [L.Symbol "not",arg] -> lispToExprT g arg >>= return . fgcast l . Not
      L.List [L.Symbol "let",L.List syms,arg] -> letToExpr g syms arg
      L.List [L.Symbol "bvule",lhs,rhs] -> fgcast l $ binBV BVULE g lhs rhs
      L.List [L.Symbol "bvult",lhs,rhs] -> fgcast l $ binBV BVULT g lhs rhs
      L.List [L.Symbol "bvuge",lhs,rhs] -> fgcast l $ binBV BVUGE g lhs rhs
      L.List [L.Symbol "bvugt",lhs,rhs] -> fgcast l $ binBV BVUGT g lhs rhs
      L.List [L.Symbol "bvsle",lhs,rhs] -> fgcast l $ binBV BVSLE g lhs rhs
      L.List [L.Symbol "bvslt",lhs,rhs] -> fgcast l $ binBV BVSLT g lhs rhs
      L.List [L.Symbol "bvsge",lhs,rhs] -> fgcast l $ binBV BVSGE g lhs rhs
      L.List [L.Symbol "bvsgt",lhs,rhs] -> fgcast l $ binBV BVSGT g lhs rhs
      L.List (L.Symbol fn:args) -> fnToExpr (return . fgcast l) g fn args
      L.List [L.List (L.Symbol "_":args),expr] -> do
        expr' <- lispToExprT g expr
        return $ fgcast l $ App (InternalFun args) expr'
      _ -> error $ "Cannot parse "++show l
      where
        replSymbol name name' (L.Symbol x)
          | x == name = L.Symbol name'
          | otherwise = L.Symbol x
        replSymbol name name' (L.List xs) = L.List (fmap (replSymbol name name') xs)
        replSymbol _ _ x = x
      
        letToExpr g (L.List [L.Symbol name,expr]:rest) arg
          = do
            res <- lispToExprU (\expr' -> do
                                   rest' <- letToExpr (\txt -> if txt==name
                                                               then typeOf expr'
                                                               else g txt) rest arg
                                   return $ Let expr' (\var@(Var name' _) -> replaceName (\n -> if n==name 
                                                                                                then name' 
                                                                                                else n) rest')
                               ) g expr
            case res of
              Just r -> return r
        letToExpr g [] arg = lispToExprT g arg

-- | Perform craig interpolation (<http://en.wikipedia.org/wiki/Craig_interpolation>) on the given terms and returns interpolants for them.
--   Note that not all SMT solvers support this.
getInterpolants :: [SMTExpr Bool] -> SMT [SMTExpr Bool]
getInterpolants exprs = do
  (_,_,mp) <- get
  putRequest (L.List (L.Symbol "get-interpolants":fmap (\e -> let (r,_) = exprToLisp e 0 in r) exprs))
  L.List res <- parseResponse
  mapM (lispToExprT (\name -> mp Map.! name)) res
  
-- | After an unsuccessful 'checkSat' this method extracts a proof from the SMT solver that the instance is unsatisfiable.
getProof :: SMT (SMTExpr Bool)
getProof = do
  (_,_,mp) <- get
  let mp' = Map.union mp commonTheorems
  putRequest (L.List [L.Symbol "get-proof"])
  res <- parseResponse
  lispToExprT (\name -> case Map.lookup name mp' of
                  Nothing -> error $ "Failed to find a definition for "++show name
                  Just n -> n
              ) res

commonTheorems :: Map T.Text TypeRep
commonTheorems = Map.fromList
  [(T.pack "|unit-resolution|",typeOf (undefined :: (Bool,Bool,Bool) -> Bool))
  ,(T.pack "|and-elim|",typeOf (undefined :: (Bool,Bool) -> Bool))
  ,(T.pack "asserted",typeOf (undefined :: Bool -> Bool))
  ,(T.pack "monotonicity",typeOf (undefined :: (Bool,Bool) -> Bool))
  ,(T.pack "trans",typeOf (undefined :: (Bool,Bool,Bool) -> Bool))
  ,(T.pack "rewrite",typeOf (undefined :: Bool -> Bool))
  ,(T.pack "mp",typeOf (undefined :: (Bool,Bool,Bool) -> Bool))
  ]