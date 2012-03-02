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

quantifierTest :: SMT Integer
quantifierTest = do
  setOption (PrintSuccess False)
  setOption (ProduceModels True)
  v1 <- var :: SMT (SMTExpr Integer)
  assert $ forAll $ \(x,y) -> v1 * x .==. v1 * y
  checkSat
  r1 <- getValue v1
  return r1

bvTest :: SMT Word8
bvTest = do
  v1 <- var
  v2 <- var
  v3 <- var
  assert $ v1 .==. 16
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

sudoko :: SMT [[Integer]]
sudoko = do
  setOption (PrintSuccess False)
  setOption (ProduceModels True)
  field <- mapM (\line -> mapM (\col -> var) [0..8]) [0..8]
  mapM_ (mapM_ (\v -> assert $ and' [ v .<. 10, v .>=. 0])) field
  mapM_ (\line -> assert $ distinct line) field
  mapM_ (\i -> assert $ distinct [ line!!i | line <- field ]) [0..8]
  assert $ distinct [ field!!i!!j | i <- [0..2],j <- [0..2] ]
  assert $ distinct [ field!!i!!j | i <- [0..2],j <- [3..5] ]
  assert $ distinct [ field!!i!!j | i <- [0..2],j <- [6..8] ]

  assert $ distinct [ field!!i!!j | i <- [3..5],j <- [0..2] ]
  assert $ distinct [ field!!i!!j | i <- [3..5],j <- [3..5] ]
  assert $ distinct [ field!!i!!j | i <- [3..5],j <- [6..8] ]

  assert $ distinct [ field!!i!!j | i <- [6..8],j <- [0..2] ]
  assert $ distinct [ field!!i!!j | i <- [6..8],j <- [3..5] ]
  assert $ distinct [ field!!i!!j | i <- [6..8],j <- [6..8] ]

  
  assert $ field!!0!!1 .==. 6
  assert $ field!!0!!7 .==. 1
  assert $ field!!1!!3 .==. 6
  assert $ field!!1!!4 .==. 5
  assert $ field!!1!!5 .==. 1
  assert $ field!!2!!0 .==. 1
  assert $ field!!2!!2 .==. 7
  assert $ field!!2!!6 .==. 6
  assert $ field!!2!!8 .==. 2
  assert $ field!!3!!0 .==. 6
  assert $ field!!3!!1 .==. 2

  checkSat
  mapM (mapM getValue) field