{-# LANGUAGE OverloadedStrings #-}
module Language.SMTLib2.Examples where

import Control.Monad
import Control.Monad.Trans
import Language.SMTLib2
import Data.Array
import Data.Word

funTest :: SMT Integer
funTest = do
  f <- fun :: SMT (SMTExpr (SMTFun (SMTExpr Integer,SMTExpr Integer) (Integer,Integer) Integer))
  g <- defFun (\x -> f `app` (x,x))
  q <- var
  assert $ forAll $ \x -> g `app` x .==. 2
  assert $ q .==. (f `app` (3,3))
  checkSat
  vq <- getValue q
  return vq

quantifierTest :: SMT (Integer,Integer)
quantifierTest = do
  setOption (PrintSuccess False)
  setOption (ProduceModels True)
  v1 <- var :: SMT (SMTExpr Integer)
  v2 <- var
  assert $ forAll $ \(x,y) -> v1 + x .==. v2 + x + y
  checkSat
  r1 <- getValue v1
  r2 <- getValue v2
  return (r1,r2)

bvTest :: SMT Word8
bvTest = do
  v1 <- var
  v2 <- var
  v3 <- var
  assert $ v1 .==. (constant (16::Word8))
  assert $ v2 .==. 35
  assert $ v3 .==. v1 + v2
  checkSat
  getValue v3

transposeTest :: SMT ([Integer],Bool)
transposeTest = do
  let c1 = listArray (0,9) [6,2,4,5,1,9,0,3,8,7]
      c2 = listArray (0,9) [2,9,3,6,1,8,7,0,5,4]
  v1 <- var :: SMT (SMTExpr (Array Integer Integer))
  v2 <- var :: SMT (SMTExpr (Array Integer Integer))
  v3 <- var :: SMT (SMTExpr (Array Integer Integer))
  assert $ arrayConst v1 c1
  assert $ arrayConst v2 c2
  mapM_ (\i -> assert $ (select v3 (constant i)) .<. 10) [0..9]
  mapM_ (\i -> assert $ (select v3 (constant i)) .>=. 0) [0..9]
  mapM_ (\i -> assert $ (select v1 (constant i)) .==. (select v2 (select v3 (constant i)))) [0..9]
  checkSat >>= liftIO.print
  res <- unmangleArray (0,9) v3
  return (elems res,all (\i -> c2!(res!i) == c1!i) [0..9])

{- SEND
  +MORE
  -----
  MONEY -}

add x y c r rc = assert (ite 
                         ((plus [x,y,c]) .>=. 10)
                         (and'
                          [r .==. ((plus [x,y,c]) - 10)
                          ,rc .==. 1])
                         (and'
                          [r .==. (plus [x,y,c])
                          ,rc .==. 0]
                         )
                        )

sendMoreMoney :: SMT (Integer,Integer,Integer,Integer,Integer,Integer,Integer,Integer,(Integer,Integer,Integer),Integer,Integer,Integer,Bool)
sendMoreMoney = do
  setOption (PrintSuccess False)
  setOption (ProduceModels True)
  setLogic "QF_LIA"
  [s,e,n,d,m,o,r,y,c0,c1,c2] <- replicateM 11 (var :: SMT (SMTExpr Integer))
  let alls = [s,e,n,d,m,o,r,y]
  assert (distinct alls)
  assert (and' [v .>=. 0
               | v <- alls
               ])
  assert (and' [v .<. 10
               | v <- alls
               ])
  assert (not' (m .==. 0))
  add d e 0 y c0
  add n r c0 e c1
  add e o c1 n c2
  add s m c2 o m
  res <- checkSat
  liftIO $ print res
  vs <- getValue s
  ve <- getValue e
  vn <- getValue n
  vd <- getValue d
  vm <- getValue m
  vo <- getValue o
  vr <- getValue r
  vy <- getValue y
  vc0 <- getValue c0
  vc1 <- getValue c1
  vc2 <- getValue c2
  let send = vs*1000 + ve*100 + vn*10 + vd
      more = vm*1000 + vo*100 + vr*10 + ve
      money = vm*10000+vo*1000+vn*100+ve*10+vy
  return (vs,ve,vn,vd,vm,vo,vr,vy,(vc0,vc1,vc2),send,more,money,send+more==money)

--soduko :: 