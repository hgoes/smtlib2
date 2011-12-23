{-# LANGUAGE FlexibleInstances,OverloadedStrings,MultiParamTypeClasses,TemplateHaskell,RankNTypes #-}
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
  getSort _ = L.Symbol "Int"
  declareType u = [(typeOf u,return ())]

instance SMTValue Integer where
  unmangle (L.Number (L.I v)) = Just v
  unmangle (L.List [L.Symbol "-"
                   ,L.Number (L.I v)]) = Just $ - v
  unmangle e = Nothing
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

-- Real

instance SMTType (Ratio Integer) where
  getSort _ = L.Symbol "Real"
  declareType u = [(typeOf u,return ())]

instance SMTValue (Ratio Integer) where
  unmangle (L.Number (L.I v)) = Just $ fromInteger v
  unmangle (L.Number (L.D v)) = Just $ realToFrac v
  unmangle (L.List [L.Symbol "/"
                   ,x
                   ,y]) = do
                          q <- unmangle x
                          r <- unmangle y
                          return $ q / r
  unmangle (L.List [L.Symbol "-",r]) = do
    res <- unmangle r
    return (-res)
  unmangle _ = Nothing
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

-- Arrays

instance (SMTType idx,SMTType val) => SMTType (Array idx val) where
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
  getSort _ = bv 8
  declareType u = [(typeOf u,return ())]

withUndef1 :: (a -> g a) -> g a
withUndef1 f = f undefined

getBVValue :: (Num a,Bits a,Read a) => L.Lisp -> Maybe a
getBVValue (L.Number (L.I v)) = Just (fromInteger v)
getBVValue (L.Symbol s) = case T.unpack s of
  '#':'b':rest -> withUndef1 (\u -> if Prelude.length rest == bitSize u
                                    then (let [(v,_)] = readInt 2 (\x -> x=='0' || x=='1') (\x -> if x=='0' then 0 else 1) rest 
                                          in Just v)
                                    else Nothing)
  '#':'x':rest -> withUndef1 (\u -> if Prelude.length rest == ((bitSize u) `div` 4)
                                    then (let [(v,_)] = readHex rest
                                          in Just v)
                                    else Nothing)
  _ -> Nothing
getBVValue (L.List [L.Symbol "_",L.Symbol val,L.Number (L.I bits)])
  = withUndef1 (\u -> if bits == (fromIntegral $ bitSize u)
                      then (case T.unpack val of
                               'b':'v':num -> Just (read num)
                               _ -> Nothing)
                      else Nothing)
getBVValue _ = Nothing

putBVValue :: Bits a => a -> L.Lisp
putBVValue x = L.Symbol (T.pack ('#':'b':[ if testBit x i
                                           then '1'
                                           else '0' | i <- Prelude.reverse [0..((bitSize x)-1)] ]))

instance SMTValue Word8 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word8

instance SMTType Word16 where
  getSort _ = bv 16
  declareType u = [(typeOf u,return ())]

instance SMTValue Word16 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word16

instance SMTType Word32 where
  getSort _ = bv 32
  declareType u = [(typeOf u,return ())]

instance SMTValue Word32 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word32

instance SMTType Word64 where
  getSort _ = bv 64
  declareType u = [(typeOf u,return ())]
  
instance SMTValue Word64 where
  unmangle = getBVValue
  mangle = putBVValue

instance SMTBV Word64

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
                     v1 = Var n1
                     t1 = getSort $ getUndef v1
                 in (v1,[(n1,t1)],c+1)
  unpackArgs e _ c = let (e',c') = exprToLisp e c
                     in ([e'],c)
  foldExprs f s x = f s x
  allOf x = x

instance (SMTType a,SMTType b) => Args (SMTExpr a,SMTExpr b) (a,b) where
  createArgs c = let n1 = T.pack $ "f"++show c
                     n2 = T.pack $ "f"++show (c+1)
                     v1 = Var n1
                     v2 = Var n2
                     t1 = getSort $ getUndef v1
                     t2 = getSort $ getUndef v2
                 in ((v1,v2),[(n1,t1),(n2,t2)],c+2)
  unpackArgs (e1,e2) _ c = let (r1,c1) = exprToLisp e1 c
                               (r2,c2) = exprToLisp e2 c1
                           in ([r1,r2],c2)
  foldExprs f s (e1,e2) = f (f s e1) e2
  allOf x = (x,x)

instance (SMTType a,SMTType b,SMTType c) => Args (SMTExpr a,SMTExpr b,SMTExpr c) (a,b,c) where
  createArgs c = let n1 = T.pack $ "f"++show c
                     n2 = T.pack $ "f"++show (c+1)
                     n3 = T.pack $ "f"++show (c+2)
                     v1 = Var n1
                     v2 = Var n2
                     v3 = Var n3
                     t1 = getSort $ getUndef v1
                     t2 = getSort $ getUndef v2
                     t3 = getSort $ getUndef v3
                 in ((v1,v2,v3),[(n1,t1),(n2,t2),(n3,t3)],c+3)
  unpackArgs (e1,e2,e3) _ c = let (r1,c1) = exprToLisp e1 c
                                  (r2,c2) = exprToLisp e2 c1
                                  (r3,c3) = exprToLisp e3 c2
                              in ([r1,r2,r3],c3)
  foldExprs f s (e1,e2,e3) = f (f (f s e1) e2) e3
  allOf x = (x,x,x)

instance SMTType a => SMTType (Maybe a) where
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
  unmangle (L.Symbol "Nothing") = Just Nothing
  unmangle (L.List [L.Symbol "as"
                   ,L.Symbol "Nothing"
                   ,_]) = Just Nothing
  unmangle (L.List [L.Symbol "Just"
                   ,res]) = do
    r <- unmangle res
    return $ Just r
  unmangle _ = Nothing
  mangle u@Nothing = L.List [L.Symbol "as"
                            ,L.Symbol "Nothing"
                            ,getSort u]
  mangle (Just x) = L.List [L.Symbol "Just"
                           ,mangle x]

undefArg :: b a -> a
undefArg _ = undefined

instance (Typeable a,SMTType a) => SMTType [a] where
  getSort u = L.List [L.Symbol "List",getSort (undefArg u)]
  declareType u = (typeOf u,return ()):declareType (undefArg u)

instance (Typeable a,SMTValue a) => SMTValue [a] where
  unmangle (L.Symbol "nil") = Just []
  unmangle (L.List [L.Symbol "insert",h,t]) = do
    h' <- unmangle h
    t' <- unmangle t
    return $ h':t'
  unmangle _ = Nothing
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

lispToExprU :: (forall a. (SMTValue a,Typeable a) => SMTExpr a -> b)
               -> (T.Text -> TypeRep)
               -> L.Lisp -> Maybe b
lispToExprU f g l
  = firstJust [(unmangle l :: Maybe Bool) >>= return.f.Const
              ,(unmangle l :: Maybe Integer) >>= return.f.Const
              ,(unmangle l :: Maybe Word8) >>= return.f.Const
              ,(unmangle l :: Maybe Word16) >>= return.f.Const
              ,(unmangle l :: Maybe Word32) >>= return.f.Const
              ,(unmangle l :: Maybe Word64) >>= return.f.Const
              ,case l of
                L.Symbol name -> withUndef (g name) $ \u -> Just $ f $ asType u (Var name)
                L.List [L.Symbol "=",lhs,rhs] -> case lispToExprU (\lhs' -> f (Eq lhs' (lispToExprT g rhs))) g lhs of
                  Just r -> Just r
                  Nothing -> lispToExprU (\rhs' -> f (Eq (lispToExprT g lhs) rhs')) g rhs
                L.List [L.Symbol ">",lhs,rhs] -> Just $ f (Gt (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs))
                L.List [L.Symbol ">=",lhs,rhs] -> Just $ f (Ge (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs))
                L.List [L.Symbol "<",lhs,rhs] -> Just $ f (Lt (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs))
                L.List [L.Symbol "<=",lhs,rhs] -> Just $ f (Le (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs))
                L.List (L.Symbol "+":args) -> Just $ f (Plus $ fmap (\arg -> (lispToExprT g arg :: SMTExpr Integer)) args)
                L.List [L.Symbol "-",lhs,rhs] -> Just $ f (Minus (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs))
                L.List (L.Symbol "*":args) -> Just $ f (Mult $ fmap (\arg -> (lispToExprT g arg :: SMTExpr Integer)) args)
                L.List [L.Symbol "/",lhs,rhs] -> Just $ f (Div (lispToExprT g lhs) (lispToExprT g rhs))
                L.List [L.Symbol "mod",lhs,rhs] -> Just $ f (Mod (lispToExprT g lhs) (lispToExprT g rhs))
                L.List (L.Symbol "and":exprs) -> Just $ f $ And $ fmap (lispToExprT g) exprs
                L.List (L.Symbol "or":exprs) -> Just $ f $ Or $ fmap (lispToExprT g) exprs
                L.List [L.Symbol "not",arg] -> Just $ f $ Not $ lispToExprT g arg
                L.List [L.Symbol "bvule",lhs,rhs] -> Just $ f $ binBV BVULE g lhs rhs
                L.List [L.Symbol "bvult",lhs,rhs] -> Just $ f $ binBV BVULT g lhs rhs
                L.List [L.Symbol "bvuge",lhs,rhs] -> Just $ f $ binBV BVUGE g lhs rhs
                L.List [L.Symbol "bvugt",lhs,rhs] -> Just $ f $ binBV BVUGT g lhs rhs
                L.List [L.Symbol "bvsle",lhs,rhs] -> Just $ f $ binBV BVSLE g lhs rhs
                L.List [L.Symbol "bvslt",lhs,rhs] -> Just $ f $ binBV BVSLT g lhs rhs
                L.List [L.Symbol "bvsge",lhs,rhs] -> Just $ f $ binBV BVSGE g lhs rhs
                L.List [L.Symbol "bvsgt",lhs,rhs] -> Just $ f $ binBV BVSGT g lhs rhs
                L.List (L.Symbol fn:args) -> Just $ fnToExpr f g fn args
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

fnToExpr :: (forall a. (SMTValue a,Typeable a) => SMTExpr a -> b)
            -> (T.Text -> TypeRep)
            -> Text -> [L.Lisp] -> b
fnToExpr f g fn args = case splitTyConApp $ g fn of
  (_,[targs,res]) -> withUndef res $ \res' -> case splitTyConApp targs of
    (_,rargs) -> case rargs of
      [] -> let [a0] = args in withUndef targs $ \t0' -> f $ asType res' $ App (Fun fn) (asType t0' $ lispToExprT g a0)
      [t0,t1] -> let [a0,a1] = args in withUndef t0 $ \t0' ->
        withUndef t1 $ \t1' -> f $ asType res' $ App (Fun fn) (asType t0' $ lispToExprT g a0,
                                                               asType t1' $ lispToExprT g a1)
      [t0,t1,t2] -> let [a0,a1,a2] = args in withUndef t0 $ \t0' ->
        withUndef t1 $ \t1' -> 
        withUndef t2 $ \t2' -> f $ asType res' $ App (Fun fn) (asType t0' $ lispToExprT g a0,
                                                               asType t1' $ lispToExprT g a1,
                                                               asType t2' $ lispToExprT g a2)

fgcast :: (Typeable a,Typeable b) => L.Lisp -> c a -> c b
fgcast l x = case gcast x of
  Just r -> r
  Nothing -> error $ "Type error in expression "++show l

binBV :: (forall a. (SMTBV a,Typeable a) => SMTExpr a -> SMTExpr a -> SMTExpr b) -> (T.Text -> TypeRep) -> L.Lisp -> L.Lisp -> SMTExpr b
binBV f g lhs rhs = case lispToExprU (asBV $ \lhs' -> f lhs' (lispToExprT g rhs)) g lhs of
  Just r -> r
  Nothing -> case lispToExprU (asBV $ \rhs' -> f (lispToExprT g lhs) rhs') g rhs of
    Just r -> r
    Nothing -> error $ "Parsing bitvector expression failed"

lispToExprT :: (SMTValue a,Typeable a) => (T.Text -> TypeRep) -> L.Lisp -> SMTExpr a
lispToExprT g l = case unmangle l of
  Just v -> Const v
  Nothing -> case l of
    L.Symbol name -> Var name
    L.List [L.Symbol "=",lhs,rhs] -> case lispToExprU (\lhs' -> Eq lhs' (lispToExprT g rhs)) g lhs >>= gcast of
      Just r -> r
      Nothing -> case lispToExprU (\rhs' -> Eq (lispToExprT g lhs) rhs') g rhs >>= gcast of
        Just r -> r
        Nothing -> error $ "Failed to parse expression "++show l
    L.List [L.Symbol ">",lhs,rhs] -> fgcast l $ Gt (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs)
    L.List [L.Symbol ">=",lhs,rhs] -> fgcast l $ Ge (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs)
    L.List [L.Symbol "<",lhs,rhs] -> fgcast l $ Lt (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs)
    L.List [L.Symbol "<=",lhs,rhs] -> fgcast l $ Le (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs)
    L.List (L.Symbol "+":args) -> fgcast l $ Plus (fmap (\arg -> (lispToExprT g arg :: SMTExpr Integer)) args)
    L.List [L.Symbol "-",lhs,rhs] -> fgcast l $ Minus (lispToExprT g lhs :: SMTExpr Integer) (lispToExprT g rhs)
    L.List (L.Symbol "*":args) -> fgcast l $ Mult (fmap (\arg -> (lispToExprT g arg :: SMTExpr Integer)) args)
    L.List [L.Symbol "/",lhs,rhs] -> fgcast l $ Div (lispToExprT g lhs) (lispToExprT g rhs)
    L.List [L.Symbol "mod",lhs,rhs] -> fgcast l $ Mod (lispToExprT g lhs) (lispToExprT g rhs)
    L.List (L.Symbol "and":args) -> fgcast l $ And (fmap (lispToExprT g) args)
    L.List (L.Symbol "or":args) -> fgcast l $ Or (fmap (lispToExprT g) args)
    L.List [L.Symbol "not",arg] -> fgcast l $ Not $ lispToExprT g arg
    L.List [L.Symbol "let",L.List syms,arg] -> letToExpr g syms arg
    L.List [L.Symbol "bvule",lhs,rhs] -> fgcast l $ binBV BVULE g lhs rhs
    L.List [L.Symbol "bvult",lhs,rhs] -> fgcast l $ binBV BVULT g lhs rhs
    L.List [L.Symbol "bvuge",lhs,rhs] -> fgcast l $ binBV BVUGE g lhs rhs
    L.List [L.Symbol "bvugt",lhs,rhs] -> fgcast l $ binBV BVUGT g lhs rhs
    L.List [L.Symbol "bvsle",lhs,rhs] -> fgcast l $ binBV BVSLE g lhs rhs
    L.List [L.Symbol "bvslt",lhs,rhs] -> fgcast l $ binBV BVSLT g lhs rhs
    L.List [L.Symbol "bvsge",lhs,rhs] -> fgcast l $ binBV BVSGE g lhs rhs
    L.List [L.Symbol "bvsgt",lhs,rhs] -> fgcast l $ binBV BVSGT g lhs rhs
    L.List (L.Symbol fn:args) -> fnToExpr (fgcast l) g fn args
    L.List [L.List (L.Symbol "_":args),expr] -> fgcast l $ App (InternalFun args) (lispToExprT g expr)
    _ -> error $ "Cannot parse "++show l
    where
      replSymbol name name' (L.Symbol x)
        | x == name = L.Symbol name'
        | otherwise = L.Symbol x
      replSymbol name name' (L.List xs) = L.List (fmap (replSymbol name name') xs)
      replSymbol _ _ x = x
      
      letToExpr g (L.List [L.Symbol name,expr]:rest) arg
        = case lispToExprU (\expr' -> Let expr' (\var@(Var name') -> letToExpr (\txt -> if txt==name'
                                                                                        then typeOf (undefArg var)
                                                                                        else g txt)
                                                                     rest (replSymbol name name' arg))) g expr of
          Just r -> r
      letToExpr g [] arg = lispToExprT g arg

getInterpolants :: [SMTExpr Bool] -> SMT [SMTExpr Bool]
getInterpolants exprs = do
  (_,_,mp) <- get
  putRequest (L.List (L.Symbol "get-interpolants":fmap (\e -> let (r,_) = exprToLisp e 0 in r) exprs))
  L.List res <- parseResponse
  return $ fmap (\l -> lispToExprT (\name -> mp Map.! name) l) res

getProof :: SMT (SMTExpr Bool)
getProof = do
  (_,_,mp) <- get
  let mp' = Map.union mp commonTheorems
  putRequest (L.List [L.Symbol "get-proof"])
  res <- parseResponse
  return $ lispToExprT (\name -> case Map.lookup name mp' of
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