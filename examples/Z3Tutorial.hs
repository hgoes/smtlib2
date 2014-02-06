{-# LANGUAGE FlexibleContexts,ScopedTypeVariables,TemplateHaskell,TypeFamilies,OverloadedStrings,DeriveDataTypeable #-}
module Main where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Data.Fix
import Language.SMTLib2.Solver
import Language.SMTLib2.TH
import Data.Ratio
import Data.Unit
import Data.Word
import Data.Array
import Data.Typeable

query :: (LiftArgs a,Unit (ArgAnnotation a)) => (a -> [SMTExpr Bool]) -> SMT (Maybe (Unpacked a))
query f = do
  vec <- argVars
  mapM_ assert (f vec)
  r <- checkSat
  if r
    then fmap Just $ getValues vec
    else return Nothing

example1 :: SMT (Maybe Integer)
example1 = do
  a <- var
  f <- fun
  assert $ a .>. 10
  assert $ (f `app` (a,constant True)) .<. (constant (100::Integer))
  res <- checkSat
  if res
    then (do
             ra <- getValue a
             return (Just ra))
    else return Nothing

example2 :: SMT (Maybe (Integer,Integer,Integer),Maybe (Integer,Integer,Integer))
example2 = do
  vs@(x,y,z::SMTExpr Integer) <- argVars
  q1 <- stack $ do
    assert $ x + y .==. 10
    assert $ x + 2*y .==. 20
    r1 <- checkSat
    if r1
      then fmap Just (getValues vs)
      else return Nothing
  q2 <- stack $ do
    assert $ 3*x+y .==. 10
    assert $ 2*x+2*y .==. 21
    r2 <- checkSat
    if r2
      then fmap Just (getValues vs)
      else return Nothing
  return (q1,q2)

example3 :: SMT Bool
example3 = do
  (p,q,r) <- argVars
  conjecture <- defConst (((p .=>. q) .&&. (q .=>. r)) .=>. (p .=>. r))
  assert $ not' conjecture
  checkSat

example4 :: SMT Bool
example4 = do
  a <- var
  b <- var
  demorgan <- defConst ((a .&&. b) .==. not' ((not' a) .||. (not' b)))
  assert $ not' demorgan
  checkSat

example5 :: SMT (Maybe (Integer,Integer))
example5 = do
  f <- fun :: SMT (SMTFunction (SMTExpr Integer) Integer)
  a <- var
  b <- var
  assert $ a .>. 20
  assert $ b .>. a
  assert $ (f `app` 10) .==. 1
  r <- checkSat
  if r
    then (do
             ra <- getValue a
             rb <- getValue b
             return $ Just (ra,rb))
    else return Nothing

example6 :: SMT (Maybe (Integer,Integer,Integer,Rational,Rational))
example6 = query (\(a,b,c,d,e) -> [a .>. b + 2
                                  ,a .==. 2*c + 10
                                  ,c+b .<=. 1000
                                  ,d .>=. e])

example7 :: SMT (Maybe (Integer,Integer,Integer,Rational,Rational))
example7 = query (\(a,b,c,d,e) -> [e .>. (toReal $ a + b) + 2
                                  ,d .==. (toReal c) + 0.5
                                  ,a .>. b])

example8 :: SMT (Maybe (Rational,Rational))
example8 = query (\(b,c) -> [b*b*b + b*c .==. 3])

example9 :: SMT (Maybe (Rational,Rational,Rational))
example9 = query (\(x,y,z) -> [x*x .==. x + 2
                              ,x*y .==. x
                              ,(y-1)*z .==. 1])

example10 :: SMT (Maybe (Integer,(Integer,Integer,Integer,Integer,Integer,Integer),(Rational,Rational)))
example10 = query (\(a,(r1,r2,r3,r4,r5,r6),(b,c)) -> [a .==. 10
                                                   ,r1 .==. a `div'` 4
                                                   ,r2 .==. a `mod'` 4
                                                   ,r3 .==. a `rem'` 4
                                                   ,r4 .==. a `div'` (-4)
                                                   ,r5 .==. a `mod'` (-4)
                                                   ,r6 .==. a `rem'` (-4)
                                                   ,b .>=. c / 3
                                                   ,c .>=. 20])

example11 :: SMT (Maybe (BV64,BV64))
example11 = query (\(x,y) -> [not' $ bvand (bvnot x) (bvnot y) .==. bvnot (bvor x y)])

example13 :: SMT Bool
example13 = do
  isPowerOfTwo <- defFun $ \x -> 0 .==. bvand (x::SMTExpr BV8) (bvsub x 1)
  a <- var
  assert $ not' $ (isPowerOfTwo `app` a) .==. foldl1 (.||.) ((a.==. 0):[a .==. (fromInteger $ 2^i) | i <- [0..7] ])
  checkSat

example14 :: SMT (Maybe (BV8,BV8))
example14 = query $ \(a,b) -> [not' $ (bvule a b) .==. (bvsle a b)]

example15 :: SMT (Integer,Integer)
example15 = do
  (x,y,a1) <- argVars
  assert $ select a1 x .==. x
  assert $ store a1 x y .==. a1
  checkSat
  getValues (x,y)

example16 :: SMT ((Integer,Integer),Bool)
example16 = do
  (all1,a,i) <- argVars
  assert $ all1 .==. constArray 1 ()
  assert $ a .==. select all1 (i::SMTExpr Integer)
  checkSat
  r1 <- getValues (a,i)
  assert $ not' $ a .==. 1
  r2 <- checkSat
  return (r1,r2)

example17 :: SMT ([(Bool,Bool,Bool)],Bool)
example17 = do
  (arr1,arr2,arr3) <- argVars :: SMT (SMTExpr (SMTArray (SMTExpr Integer) Bool),SMTExpr (SMTArray (SMTExpr Integer) Bool),SMTExpr (SMTArray (SMTExpr Integer) Bool))
  f <- fun :: SMT (SMTFunction (SMTExpr Bool,SMTExpr Bool) Bool)
  assert $ arr3 .==. ((map' f) `app` (arr1,arr2))
  
  let results = [(0,False,False,True)
                ,(1,False,True,False)
                ,(2,True,False,False)
                ,(3,True,True,True)]
  
  mapM_ (\(i,a1,a2,r) -> do
            assert $ select arr1 (constant i) .==. (constant a1)
            assert $ select arr2 (constant i) .==. (constant a2)
            assert $ select arr3 (constant i) .==. (constant r)) results
  
  test <- var
  assert $ test .==. (f `app` (constant True,constant False))
  
  checkSat
  r1 <- unmangleArray (0,9) arr1
  r2 <- unmangleArray (0,9) arr2
  r3 <- unmangleArray (0,9) arr3
  r4 <- getValue test
  return (zip3 (elems r1) (elems r2) (elems r3),r4)

example18 :: SMT (Bool,Bool,Maybe ([Bool],[Bool]))
example18 = do
  (a,b,c) <- argVars :: SMT (SMTExpr (SMTArray (SMTExpr Integer) Bool)
                            ,SMTExpr (SMTArray (SMTExpr Integer) Bool)
                            ,SMTExpr (SMTArray (SMTExpr Integer) Bool))
  x <- var
  r1 <- stack $ do
    assert $ not' $ ((map' and') `app` [a,b]) .==. 
      ((map' not'') `app` ((map' or') `app` [(map' not'') `app` b,(map' not'') `app` a]))
    checkSat
  r2 <- stack $ do
    assert $ (select ((map' and') `app` [a,b]) x) .&&. (not' (select a x))
    checkSat
  r3 <- stack $ do
    assert $ (select ((map' or') `app` [a,b]) x) .&&. (not' (select a x))
    r <- checkSat
    if r then (do
                  ra <- unmangleArray (0,2) a
                  rb <- unmangleArray (0,2) b
                  return $ Just (elems ra,elems rb))
      else return Nothing
  return (r1,r2,r3)

example19 :: SMT (Array (Integer,Integer) Integer,
                  Array (Integer,Integer) Integer,
                  Array (Integer,Integer) Integer)
example19 = do
  bagUnion <- defFun (\(x::SMTExpr (SMTArray (SMTExpr Integer,SMTExpr Integer) Integer),y) -> app (map' plus) [x,y])
  (s1,s2,s3) <- argVars
  assert $ s3 .==. (app bagUnion (s1,s2))
  assert $ select s1 (0,0) .==. 5
  assert $ select s2 (0,0) .==. 3
  assert $ select s2 (1,2) .==. 4
  checkSat
  r1 <- unmangleArray ((0,0),(1,2)) s1
  r2 <- unmangleArray ((0,0),(1,2)) s2
  r3 <- unmangleArray ((0,0),(1,2)) s3
  return (r1,r2,r3)

data Pair a b = Pair { first :: a
                     , second :: b 
                     } deriving (Show,Eq,Ord,Typeable)

-- $(deriveSMT ''Pair)

instance (SMTType a,SMTType b) => SMTType (Pair a b) where
  type SMTAnnotation (Pair a b) = (SMTAnnotation a,SMTAnnotation b)
  getSort (_::Pair a b) (ann1,ann2) = let s1 = getSort (undefined::a) ann1
                                          s2 = getSort (undefined::b) ann2
                                      in Fix (NamedSort "Pair" [s1,s2])
  asDataType _ = Just ("Pair",TypeCollection { argCount = 2
                                             , dataTypes = [dtPair] })
    where
      dtPair = DataType { dataTypeName = "Pair"
                        , dataTypeConstructors = [conPair]
                        , dataTypeGetUndefined = \[p1,p2] f
                                                 -> withProxyArg p1 $
                                                    \(_::a1) ann1
                                                    -> withProxyArg p2 $
                                                       \(_::b1) ann2
                                                       -> f (undefined :: Pair a1 b1) (ann1,ann2)
                        }
      conPair = Constr { conName = "Pair"
                       , conFields = [fieldFst,fieldSnd]
                       , construct = \_ [v1,v2] f
                                     -> withAnyValue v1 $
                                        \_ (v1'::a') ann1 -> withAnyValue v2 $
                                                     \_ (v2'::b') ann2 -> f [ProxyArg (undefined::a') ann1,
                                                                             ProxyArg (undefined::b') ann2] (Pair v1' v2') (ann1,ann2)
                       , conTest = \_ _ -> True }
      fieldFst = DataField { fieldName = "first"
                           , fieldSort = Fix (ArgumentSort 0)
                           , fieldGet = \[p1,p2] x f
                                        -> withProxyArg p1 $
                                           \(_::a1) ann1
                                            -> withProxyArg p2 $
                                               \(_::b1) ann2
                                                -> case cast x of
                                                 Just ~(Pair x _::Pair a1 b1)
                                                   -> f x ann1
                           }
      fieldSnd = DataField { fieldName = "second"
                           , fieldSort = Fix (ArgumentSort 1)
                           , fieldGet = \[p1,p2] x f
                                        -> withProxyArg p1 $
                                           \(_::a1) ann1
                                            -> withProxyArg p2 $
                                               \(_::b1) ann2
                                                -> case cast x of
                                                 Just ~(Pair _ y::Pair a1 b1)
                                                   -> f y ann2
                           }
  asValueType (_::Pair a b) (ann1,ann2) f
    = case asValueType (undefined::a) ann1 $
           \(_::a') ann1'
           -> asValueType (undefined::b) ann2 $
              \(_::b') ann2'
              -> f (undefined::Pair a' b') (ann1',ann2') of
        Just (Just r) -> Just r
        _ -> Nothing
  getProxyArgs (_::Pair a b) (ann1,ann2) = [ProxyArg (undefined::a) ann1,
                                            ProxyArg (undefined::b) ann2]
  annotationFromSort (_::Pair a b) (Fix (NamedSort "Pair" [x,y]))
    = (annotationFromSort (undefined::a) x,
       annotationFromSort (undefined::b) y)

instance (SMTValue a,SMTValue b) => SMTValue (Pair a b) where
  unmangle (ConstrValue "Pair" [x,y] _) (ann1,ann2) = do
      vx <- unmangle x ann1
      vy <- unmangle y ann2
      return $ Pair vx vy
  mangle (Pair x y) (ann1,ann2) = ConstrValue "Pair" [mangle x ann1,mangle y ann2] Nothing

instance (SMTType a,SMTType b) => SMTRecordType (Pair a b) where
  getFieldAnn (Field "first") (ann1,_) = case cast ann1 of
    Just r -> r
  getFieldAnn (Field "second") (_,ann2) = case cast ann2 of
    Just r -> r

example20 :: SMT (Pair Integer Integer,Pair Integer Integer)
example20 = do
  (p1,p2) <- argVars
  assert $ p1 .==. p2
  assert $ (p2 .# $(field 'second)) .>. 20
  checkSat
  r1 <- getValue p1
  r2 <- getValue p2
  return (r1,r2)

data S = A | B | C deriving (Show,Eq,Ord,Typeable)

-- $(deriveSMT ''Main.S)

instance SMTType Main.S where
  type SMTAnnotation Main.S = ()
  getSort _ _ = Fix (NamedSort "S" [])
  asDataType _ = Just ("S",TypeCollection { argCount = 0
                                          , dataTypes = [dtS] })
    where
      dtS = DataType { dataTypeName = "S"
                     , dataTypeConstructors = [ Constr { conName = show con
                                                       , conFields = []
                                                       , construct = \_ [] f -> f [] con ()
                                                       , conTest = \[] x -> cast x==Just con }
                                              | con <- [A,B,C]]
                     , dataTypeGetUndefined = \_ f -> f (undefined::Main.S) () }
  asValueType x ann f = Just $ f x ann
  getProxyArgs _ _ = []
  annotationFromSort _ _ = ()

instance SMTValue Main.S where
  unmangle (ConstrValue "A" [] _) _ = Just A
  unmangle (ConstrValue "B" [] _) _ = Just B
  unmangle (ConstrValue "C" [] _) _ = Just C
  mangle con _ = ConstrValue (show con) [] Nothing

example21 :: SMT (Bool,Bool)
example21 = do
  (x::SMTExpr Main.S,y,z,u) <- argVars
  assert $ distinct [x,y,z]
  r1 <- checkSat
  assert $ distinct [x,y,z,u]
  r2 <- checkSat
  return (r1,r2)

data Lst a = Nil
           | Cons { hd :: a
                  , tl :: Lst a }
           deriving (Show,Eq,Ord,Typeable)

instance SMTType a => SMTType (Lst a) where
  type SMTAnnotation (Lst a) = SMTAnnotation a
  getSort (_::Lst a) ann = Fix (NamedSort "Lst" [getSort (undefined::a) ann])
  asDataType _ = Just ("Lst",TypeCollection { argCount = 1
                                            , dataTypes = [dtLst] })
    where
      dtLst = DataType { dataTypeName = "Lst"
                       , dataTypeConstructors = [conNil,conCons]
                       , dataTypeGetUndefined = \[p] f
                                                -> withProxyArg p $
                                                   \(_::a') ann -> f (undefined::Lst a') ann
                       }
      conNil = Constr { conName = "Nil"
                      , conFields = []
                      , construct = \[Just p] [] f
                                     -> withProxyArg p $
                                        \(_::a') ann
                                        -> f [p] (Nil::Lst a') ann
                      , conTest = \[p] x
                                  -> withProxyArg p $
                                     \(_::a') ann
                                      -> case cast x of
                                       Just (Nil::Lst a') -> True
                                       Just _ -> False }
      conCons = Constr { conName = "Cons"
                       , conFields = [fieldHd,fieldTl]
                       , construct = \_ [v1,v2] f
                                      -> withAnyValue v1 $
                                         \_ (v1'::a') ann1
                                         -> case castAnyValue v2 of
                                           Just (v2',ann2) -> f [ProxyArg (undefined::a') ann1] (Cons v1' v2') ann1
                       , conTest = \[p] x
                                    -> withProxyArg p $
                                       \(_::a') ann
                                        -> case cast x of
                                         Just (Cons _ _::Lst a') -> True
                                         Just _ -> False }
      fieldHd = DataField { fieldName = "hd"
                          , fieldSort = Fix (ArgumentSort 0)
                          , fieldGet = \[p] x f
                                        -> withProxyArg p $
                                           \(_::a') ann
                                            -> case cast x of
                                             Just ~(Cons h _::Lst a') -> f h ann }
      fieldTl = DataField { fieldName = "tl"
                          , fieldSort = Fix (NormalSort $ NamedSort "Lst" [Fix (ArgumentSort 0)])
                          , fieldGet = \[p] x f
                                        -> withProxyArg p $
                                           \(_::a') ann
                                            -> case cast x of
                                             Just ~(Cons _ t::Lst a') -> f t ann }
  asValueType (_::Lst a) ann f
    = asValueType (undefined::a) ann $
      \(_::a') ann' -> f (undefined::a') ann'
  getProxyArgs (_::Lst a) ann = [ProxyArg (undefined::a) ann]
  annotationFromSort (_::Lst a) (Fix (NamedSort "Lst" [x]))
    = annotationFromSort (undefined::a) x

instance (SMTValue a) => SMTValue (Lst a) where
  unmangle (ConstrValue "Nil" [] _) _ = return Nil
  unmangle (ConstrValue "Cons" [h,t] _) ann = do
    x <- unmangle h ann
    xs <- unmangle t ann
    return (Cons x xs)
  mangle (Nil::Lst a) ann = ConstrValue "Nil" [] (Just ("Lst",[getSort (undefined::a) ann]))
  mangle p@(Cons x xs) ann = ConstrValue "Cons" [mangle x ann,mangle xs ann] Nothing

instance (SMTType a) => SMTRecordType (Lst a) where
  getFieldAnn (Field "hd") ann = case cast ann of
    Just r -> r
  getFieldAnn (Field "tl") ann = case cast ann of
    Just r -> r

example22 :: SMT ((Lst Integer,Lst Integer,Lst Integer,Integer),Bool)
example22 = do
  l1 <- var
  l2 <- var
  l3 <- var
  x <- var
  assert $ not' $ l1 .==. constant Nil
  assert $ not' $ l2 .==. constant Nil
  assert $ (l1 .# $(field 'hd)) .==. (l2 .# $(field 'hd))
  assert $ not' $ l1 .==. l2
  assert $ l3 .==. (app (SMTConstructor $(constructor 'Cons)) (x,l2))
  assert $ x .>. 100
  checkSat
  vs <- getValues (l1,l2,l3,x)
  assert $ (l1 .# $(field 'tl)) .==. (l2 .# $(field 'tl))
  r <- checkSat
  return (vs,r)

data Tree t = Leaf
            | Node { value :: t
                   , children :: TreeList t }
            deriving (Eq,Ord,Show,Typeable)

data TreeList t = TNil
                | TCons { car :: Tree t
                        , cdr :: TreeList t }
                deriving (Eq,Ord,Show,Typeable)

instance SMTType t => SMTType (Tree t) where
  type SMTAnnotation (Tree t) = SMTAnnotation t
  getSort (_::Tree a) ann = Fix (NamedSort "Tree" [getSort (undefined::a) ann])
  asDataType _ = Just ("Tree",tcTree)
  asValueType (_::Tree t) ann f
    = asValueType (undefined::t) ann $
      \(_::t') ann' -> f (undefined::Tree t') ann'
  getProxyArgs (_::Tree t) ann = [ProxyArg (undefined::t) ann]
  annotationFromSort (_::Tree t) (Fix (NamedSort "Tree" [s]))
    = annotationFromSort (undefined::t) s

instance SMTType t => SMTType (TreeList t) where
  type SMTAnnotation (TreeList t) = SMTAnnotation t
  getSort (_::TreeList a) ann = Fix (NamedSort "TreeList" [getSort (undefined::a) ann])
  asDataType _ = Just ("TreeList",tcTree)
  asValueType (_::TreeList t) ann f
    = asValueType (undefined::t) ann $
      \(_::t') ann' -> f (undefined::TreeList t') ann'
  getProxyArgs (_::TreeList t) ann = [ProxyArg (undefined::t) ann]
  annotationFromSort (_::TreeList t) (Fix (NamedSort "TreeList" [s]))
    = annotationFromSort (undefined::t) s

instance SMTValue t => SMTValue (Tree t) where
  unmangle (ConstrValue "Leaf" [] _) _ = Just Leaf
  unmangle (ConstrValue "Node" [v,c] _) ann = do
    val <- unmangle v ann
    childs <- unmangle c ann
    return $ Node val childs
  unmangle _ _ = Nothing
  mangle (Leaf::Tree t) ann = ConstrValue "Leaf" []
                              (Just ("Tree",[getSort (undefined::t) ann]))
  mangle (Node v c) ann = ConstrValue "Node"
                          [mangle v ann,
                           mangle c ann] Nothing

instance SMTValue t => SMTValue (TreeList t) where
  unmangle (ConstrValue "TNil" [] _) _ = Just TNil
  unmangle (ConstrValue "TCons" [v,c] _) ann = do
    x <- unmangle v ann
    xs <- unmangle c ann
    return $ TCons x xs
  unmangle _ _ = Nothing
  mangle (TNil::TreeList t) ann = ConstrValue "TNil" []
                                  (Just ("TreeList",[getSort (undefined::t) ann]))
  mangle (TCons x xs) ann = ConstrValue "TCons"
                            [mangle x ann,
                             mangle xs ann] Nothing

tcTree :: TypeCollection
tcTree = TypeCollection { argCount = 1
                        , dataTypes = [dtTree,dtTreeList] }
  where
    dtTree = DataType { dataTypeName = "Tree"
                      , dataTypeConstructors = [conLeaf,conNode]
                      , dataTypeGetUndefined = \[p] f
                                                -> withProxyArg p $
                                                   \(_::a) ann
                                                   -> f (undefined::Tree a) ann }
    dtTreeList = DataType { dataTypeName = "TreeList"
                          , dataTypeConstructors = [conNil,conCons]
                          , dataTypeGetUndefined = \[p] f
                                                   -> withProxyArg p $
                                                      \(_::a) ann
                                                       -> f (undefined::TreeList a) ann }
    conLeaf = Constr { conName = "Leaf"
                     , conFields = []
                     , construct = \[Just p] [] f
                                    -> withProxyArg p $
                                       \(_::a) ann
                                       -> f [p] (Leaf::Tree a) ann
                     , conTest = \[p] x
                                 -> withProxyArg p $
                                    \(_::a) ann
                                    -> case cast x of
                                      Just (Leaf::Tree a) -> True
                                      Just _ -> False }
    conNode = Constr { conName = "Node"
                     , conFields = [fieldVal,fieldChild]
                     , construct = \_ [v,c] f
                                   -> withAnyValue v $
                                      \_ (v'::a) ann
                                      -> case castAnyValue c of
                                        Just (c',_) -> f [ProxyArg (undefined::a) ann] (Node v' c') ann
                     , conTest = \[p] x
                                 -> withProxyArg p $
                                    \(_::a) ann
                                    -> case cast x of
                                      Just (Node _ _::Tree a) -> True
                                      Just _ -> False }
    conNil = Constr { conName = "TNil"
                    , conFields = []
                    , construct = \[Just p] [] f
                                   -> withProxyArg p $
                                      \(_::a) ann
                                       -> f [p] (TNil::TreeList a) ann
                    , conTest = \[p] x
                                -> withProxyArg p $
                                   \(_::a) ann
                                   -> case cast x of
                                     Just (TNil::TreeList a) -> True
                                     Just _ -> False }
    conCons = Constr { conName = "TCons"
                     , conFields = [fieldCar,fieldCdr]
                     , construct = \_ [x,xs] f
                                    -> withAnyValue x $
                                       \[p] x' _
                                       -> withProxyArg p $
                                          \(_::a) ann
                                          -> case cast x' of
                                            Just (x''::Tree a) -> case castAnyValue xs of
                                              Just (xs',_) -> f [p] (TCons x'' xs') ann
                     , conTest = \[p] x
                                 -> withProxyArg p $
                                    \(_::a) ann
                                    -> case cast x of
                                      Just (TCons _ _::TreeList a) -> True
                                      Just _ -> False }
    fieldVal = DataField { fieldName = "value"
                         , fieldSort = Fix (ArgumentSort 0)
                         , fieldGet = \[p] x f
                                      -> withProxyArg p $
                                         \(_::a) ann
                                         -> case cast x of
                                           Just (x'::Tree a) -> f (value x') ann }
    fieldChild = DataField { fieldName = "children"
                           , fieldSort = Fix (NormalSort $ NamedSort "TreeList" [Fix (ArgumentSort 0)])
                           , fieldGet = \[p] x f
                                        -> withProxyArg p $
                                           \(_::a) ann
                                           -> case cast x of
                                             Just (x'::Tree a) -> f (children x') ann }
    fieldCar = DataField { fieldName = "car"
                         , fieldSort = Fix (NormalSort $ NamedSort "Tree" [Fix (ArgumentSort 0)])
                         , fieldGet = \[p] x f
                                      -> withProxyArg p $
                                         \(_::a) ann
                                         -> case cast x of
                                           Just (x'::TreeList a) -> f (car x') ann }
    fieldCdr = DataField { fieldName = "cdr"
                         , fieldSort = Fix (NormalSort $ NamedSort "TreeList" [Fix (ArgumentSort 0)])
                         , fieldGet = \[p] x f
                                      -> withProxyArg p $
                                         \(_::a) ann
                                         -> case cast x of
                                           Just (x'::TreeList a) -> f (cdr x') ann }

instance SMTType a => SMTRecordType (Tree a) where
  getFieldAnn (Field "value") ann = case cast ann of
    Just ann' -> ann'
  getFieldAnn (Field "children") ann = case cast ann of
    Just ann' -> ann'

example23 :: SMT (Tree Integer,Tree Bool)
example23 = do
  (t1,t2) <- argVars
  assert $ not' $ t1 .==. constant Leaf
  assert $ (t1 .# $(field 'value)) .>. 20
  assert $ not' $ app (SMTConTest $(constructor 'Leaf)) t2
  assert $ not' $ t2 .# $(field 'value)
  checkSat
  getValues (t1,t2)
