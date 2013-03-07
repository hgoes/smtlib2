{-# LANGUAGE FlexibleContexts,ScopedTypeVariables,TemplateHaskell,TypeFamilies,OverloadedStrings,DeriveDataTypeable #-}
module Main where

import Language.SMTLib2
import Language.SMTLib2.Functions
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
    then fmap Just $ unliftArgs vec
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
  x <- var
  y <- var
  z <- var
  q1 <- stack $ do
    assert $ x + y .==. 10
    assert $ x + 2*y .==. 20
    r1 <- checkSat
    if r1
      then (do
               rx <- getValue x
               ry <- getValue y
               rz <- getValue z
               return $ Just (rx,ry,rz))
      else return Nothing
  q2 <- stack $ do
    assert $ 3*x+y .==. 10
    assert $ 2*x+2*y .==. 21
    r2 <- checkSat
    if r2
      then (do
               rx <- getValue x
               ry <- getValue y
               rz <- getValue z
               return $ Just (rx,ry,rz))
      else return Nothing
  return (q1,q2)

example3 :: SMT Bool
example3 = do
  p <- var
  q <- var
  r <- var
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
  f <- fun :: SMT (SMTFun (SMTExpr Integer) Integer)
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
  unliftArgs (x,y)

example16 :: SMT ((Integer,Integer),Bool)
example16 = do
  (all1,a,i) <- argVars
  assert $ all1 .==. constArray 1 ()
  assert $ a .==. select all1 (i::SMTExpr Integer)
  checkSat
  r1 <- unliftArgs (a,i)
  assert $ not' $ a .==. 1
  r2 <- checkSat
  return (r1,r2)

example17 :: SMT ([(Bool,Bool,Bool)],Bool)
example17 = do
  (arr1,arr2,arr3) <- argVars :: SMT (SMTExpr (SMTArray (SMTExpr Integer) Bool),SMTExpr (SMTArray (SMTExpr Integer) Bool),SMTExpr (SMTArray (SMTExpr Integer) Bool))
  f <- fun :: SMT (SMTFun (SMTExpr Bool,SMTExpr Bool) Bool)
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
  bagUnion <- defFun (\(x::SMTExpr (SMTArray (SMTExpr Integer,SMTExpr Integer) Integer),y) -> app (map' Plus) [x,y])
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

$(deriveSMT ''Pair)

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

$(deriveSMT ''S)

example21 :: SMT (Bool,Bool)
example21 = do
  (x::SMTExpr S,y,z,u) <- argVars
  assert $ distinct [x,y,z]
  r1 <- checkSat
  assert $ distinct [x,y,z,u]
  r2 <- checkSat
  return (r1,r2)