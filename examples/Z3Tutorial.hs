{-# LANGUAGE QuasiQuotes,DataKinds,GADTs,RankNTypes,ScopedTypeVariables,KindSignatures #-}
module Main where

import Language.SMTLib2
import Language.SMTLib2.Pipe (createPipe)
import Language.SMTLib2.Debug (debugBackend)
import Language.SMTLib2.Internals.Type (Args(..),GetTypes,withArgs,mapArgs)
import Language.SMTLib2.Internals.TH (args)
import Language.SMTLib2.Internals.Expression (allEqFromList)

runExample :: (forall b. Backend b => SMT b r) -> IO r
runExample ex = withBackend (fmap debugBackend $ createPipe "z3" ["-in","-smt2"]) ex

query :: (Backend b,GetTypes tps)
      => (Args (Expr b) tps -> SMT b ()) -> SMT b (Maybe (Args ConcreteValue tps))
query f = do
  args <- withArgs declareVar
  f args
  res <- checkSat
  case res of
    Sat -> do
      vals <- mapArgs getValue args
      return $ Just vals
    _ -> return Nothing

example1 :: Backend b => SMT b (Maybe Integer)
example1 = do
  a <- [declare| Int |]
  f <- [declare| (Int Bool) Int |]
  [expr| (> a 10) |] >>= assert
  [expr| (< (f a true) 100) |] >>= assert
  res <- checkSat
  case res of
    Sat -> do
      IntValueC v <- getValue a
      return $ Just v
    _ -> return Nothing

example2 :: Backend b => SMT b (Maybe (Integer,Integer,Integer),Maybe (Integer,Integer,Integer))
example2 = do
  x <- [declare| Int |]
  y <- [declare| Int |]
  z <- [declare| Int |]
  q1 <- stack $ do
    [expr| (= (+ x y) 10) |] >>= assert
    [expr| (= (+ x (* 2 y)) 20) |] >>= assert
    r1 <- checkSat
    case r1 of
      Sat -> do
        IntValueC vx <- getValue x
        IntValueC vy <- getValue y
        IntValueC vz <- getValue z
        return (Just (vx,vy,vz))
      _ -> return Nothing
  q2 <- stack $ do
    [expr| (= (+ (* 3 x) y) 10) |] >>= assert
    [expr| (= (+ (* 2 x) (* 2 y)) 21) |] >>= assert
    r2 <- checkSat
    case r2 of
      Sat -> do
        IntValueC vx <- getValue x
        IntValueC vy <- getValue y
        IntValueC vz <- getValue z
        return (Just (vx,vy,vz))
      _ -> return Nothing
  return (q1,q2)

example3 :: Backend b => SMT b CheckSatResult
example3 = do
  p <- [declare| Bool |]
  q <- [declare| Bool |]
  r <- [declare| Bool |]
  conjecture <- [define| (=> (and (=> p q) (=> q r)) (=> p r)) |]
  [expr| (not conjecture) |] >>= assert
  checkSat

example4 :: Backend b => SMT b CheckSatResult
example4 = do
  a <- [declare| Bool |]
  b <- [declare| Bool |]
  demorgan <- [define| (= (and a b) (not (or (not a) (not b)))) |]
  [expr| (not demorgan) |] >>= assert
  checkSat

example5 :: Backend b => SMT b (Maybe (Integer,Integer))
example5 = do
  f <- [declare| (Int) Int |]
  a <- [declare| Int |]
  b <- [declare| Int |]
  [expr| (> a 20) |] >>= assert
  [expr| (> b a) |] >>= assert
  [expr| (= (f 10) 1) |] >>= assert
  r <- checkSat
  case r of
    Sat -> do
      IntValueC ra <- getValue a
      IntValueC rb <- getValue b
      return $ Just (ra,rb)
    _ -> return Nothing

example6 :: Backend b => SMT b (Maybe (Args ConcreteValue [args| Int Int Int Real Real |]))
example6 = query (\[args| a b c d e |] -> do
                    [expr| (> a (+ b 2)) |] >>= assert
                    [expr| (= a (+ (* 2 c) 10)) |] >>= assert
                    [expr| (<= (+ c b) 1000) |] >>= assert
                    [expr| (>= d e) |] >>= assert)

example7 :: Backend b => SMT b (Maybe (Args ConcreteValue [args| Int Int Int Real Real |]))
example7 = query (\[args| a b c d e |] -> do
                    [expr| (> e (+ (to_real (+ a b)) 2.0)) |] >>= assert
                    [expr| (= d (+ (to_real c) 0.5)) |] >>= assert
                    [expr| (> a b) |] >>= assert)

example8 :: Backend b => SMT b (Maybe (Args ConcreteValue [args| Real Real |]))
example8 = query (\[args| b c |] -> do
                    [expr| (= (+ (* b b b) (* b c)) 3.0) |] >>= assert)

example9 :: Backend b => SMT b (Maybe (Args ConcreteValue [args| Real Real Real |]))
example9 = query (\[args| x y z |] -> do
                    [expr| (= (* x x) (+ x 2.0)) |] >>= assert
                    [expr| (= (* x y) x) |] >>= assert
                    [expr| (= (* (- y 1.0) z) 1.0) |] >>= assert)

example10 :: Backend b => SMT b (Maybe (Args ConcreteValue [args| Int Int Int Int Int Int Int Real Real |]))
example10 = query (\[args| a r1 r2 r3 r4 r5 r6 b c |] -> do
                      [expr| (= a 10) |] >>= assert
                      [expr| (= r1 (div a 4)) |] >>= assert
                      [expr| (= r2 (mod a 4)) |] >>= assert
                      [expr| (= r3 (rem a 4)) |] >>= assert
                      [expr| (= r4 (div a (- 4))) |] >>= assert
                      [expr| (= r5 (mod a (- 4))) |] >>= assert
                      [expr| (= r6 (rem a (- 4))) |] >>= assert
                      [expr| (>= b (/ c 3.0)) |] >>= assert
                      [expr| (>= c 20.0) |] >>= assert)

example11 :: Backend b => SMT b (Maybe (Args ConcreteValue [args| (_ BitVec 64) (_ BitVec 64) |]))
example11 = query (\[args| x y |] -> do
                     [expr| (not (= (bvand (bvnot x) (bvnot y)) (bvnot (bvor x y)))) |] >>= assert)


example13 :: Backend b => SMT b CheckSatResult
example13 = do
  isPowerOfTwo <- [define| ((x (_ BitVec 4))) (= #x0 (bvand x (bvsub x #x1))) |]
  a <- [declare| (_ BitVec 4) |]
  args <- sequence [ do
                        rn <- n
                        [expr| (= a rn) |]
                   | n <- [[expr| #x0 |]
                          ,[expr| #x1 |]
                          ,[expr| #x2 |]
                          ,[expr| #x4 |]
                          ,[expr| #x8 |]] ]
  [expr| (not (= (isPowerOfTwo a) (or # args))) |] >>= assert
  checkSat

example14 :: Backend b => SMT b (Maybe (Args ConcreteValue [args| (_ BitVec 8) (_ BitVec 8) |]))
example14 = query $ \[args| a b |] -> do
              [expr| (not (= (bvule a b) (bvsle a b))) |] >>= assert

example15 :: Backend b => SMT b (Integer,Integer)
example15 = do
  x <- [declare| Int |]
  y <- [declare| Int |]
  a1 <- [declare| (Array (Int) Int) |]
  [expr| (= (select a1 x) x) |] >>= assert
  [expr| (= (store a1 x y) a1) |] >>= assert
  [expr| (not (= x y)) |] >>= assert
  checkSat
  IntValueC vx <- getValue x
  IntValueC vy <- getValue y
  return (vx,vy)

example16 :: Backend b => SMT b (Integer,Integer,CheckSatResult)
example16 = do
  all1 <- [declare| (Array (Int) Int) |]
  a <- [declare| Int |]
  i <- [declare| Int |]
  [expr| (= all1 ((as const (Array (Int) Int)) 1)) |] >>= assert
  [expr| (= a (select all1 i)) |] >>= assert
  checkSat
  IntValueC va <- getValue a
  IntValueC vi <- getValue i
  [expr| (not (= a 1)) |] >>= assert
  r <- checkSat
  return (va,vi,r)

{- example17 :: Backend b => SMT b (CheckSatResult,CheckSatResult,CheckSatResult,CheckSatResult)
example17 = do
  a <- [declare| (Array (Int) Bool) |]
  b <- [declare| (Array (Int) Bool) |]
  c <- [declare| (Array (Int) Bool) |]
  x <- [declare| Int |]
  r1 <- stack $ do
    --[expr| (not (= ((_ map and) a b) ((_ map not) ((_ map or) ((_ map not) b) ((_ map not) a))))) |] >>= assert
    [expr| (= ((_ map not) a) b) |] >>= assert
    checkSat
  r2 <- stack $ do
    --[expr| (and (select ((_ map and) a b) x) (not (select a x))) |] >>= assert
    checkSat
  (r3,r4) <- stack $ do
    --[expr| (and (select ((_ map or) a b) x) (not (select a x))) |] >>= assert
    p <- checkSat
    --[expr| (and (not (select b x))) |] >>= assert
    q <- checkSat
    return (p,q)
  return (r1,r2,r3,r4) -}
