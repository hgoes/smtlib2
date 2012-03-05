{-# LANGUAGE OverloadedStrings #-}
module Language.SMTLib2.Examples where

import Control.Monad
import Control.Monad.Trans
import Language.SMTLib2
import Data.Array
import Data.Word
import Data.Int
import qualified Data.ByteString as BS

funTest :: SMT Integer
funTest = do
  f <- fun :: SMT (SMTExpr (SMTFun (SMTExpr Integer,SMTExpr Integer) Integer))
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

type Problem = [[Maybe Int8]]

emptyProblem :: Problem
emptyProblem = [ [ Nothing | i <- [0..8] ] | j <- [0..8] ]

puzzle1 :: Problem
puzzle1 = [ [ Nothing, Just 6 , Nothing, Nothing, Nothing, Nothing, Nothing, Just 1 , Nothing ]
          , [ Nothing, Nothing, Nothing, Just 6 , Just 5 , Just  1, Nothing, Nothing, Nothing ]
          , [ Just 1 , Nothing, Just 7 , Nothing, Nothing, Nothing, Just 6 , Nothing, Just 2  ]
          , [ Just 6 , Just 2 , Nothing, Just 3 , Nothing, Just 5 , Nothing, Just 9 , Just 4  ]
          , [ Nothing, Nothing, Just 3 , Nothing, Nothing, Nothing, Just 2 , Nothing, Nothing ]
          , [ Just 4 , Just 8 , Nothing, Just 9 , Nothing, Just 7 , Nothing, Just 3 , Just 6  ]
          , [ Just 9 , Nothing, Just 6 , Nothing, Nothing, Nothing, Just 4 , Nothing, Just 8  ]
          , [ Nothing, Nothing, Nothing, Just 7 , Just 9 , Just 4 , Nothing, Nothing, Nothing ]
          , [ Nothing, Just 5 , Nothing, Nothing, Nothing, Nothing, Nothing, Just 7 , Nothing ] ]

sudoku :: Problem -> SMT [[Int8]]
sudoku prob = do
  setOption (PrintSuccess False)
  setOption (ProduceModels True)
  field <- mapM (\line -> mapM (\col -> var) [0..8]) [0..8]
  mapM_ (mapM_ (\v -> assert $ and' [ v .<. 10, v .>. 0])) field
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

  sequence_ [ sequence_ [ case el of
                            Nothing -> return ()
                            Just n -> assert $ field!!i!!j .==. (constant n)
                          | (el,j) <- zip line [0..8]
                        ] 
              | (line,i) <- zip prob [0..8] ]

  checkSat
  mapM (mapM getValue) field

displaySolution :: [[Int8]] -> String
displaySolution = displayLines . fmap displayLine
    where
      displayLines [a,b,c,d,e,f,g,h,i] = unlines [a,b,c,"",d,e,f,"",g,h,i]
      displayLine [a,b,c,d,e,f,g,h,i] = show a ++ show b ++ show c ++ " " ++ show d ++ show e ++ show f ++ " " ++ show g ++ show h ++ show i

-- Bitvector concat example
concatExample :: SMT Word16
concatExample = do
  x1 <- var :: SMT (SMTExpr Word8)
  x2 <- var :: SMT (SMTExpr Word8)
  res <- var
  assert $ res .==. bvconcat x1 x2
  assert $ x1 .>. 2
  assert $ x2 .>. 8
  checkSat
  getValue res

concatExample2 :: SMT BS.ByteString
concatExample2 = do
  v1 <- varAnn 2
  v2 <- varAnn 1
  res <- varAnn 3
  assert $ v1 .==. (constantAnn (BS.pack [0xAA,0xBB]) 2)
  assert $ v2 .==. (constantAnn (BS.pack [0x01]) 1)
  assert $ res .==. bvconcat v1 v2
  checkSat
  getValue res