{-# LANGUAGE OverloadedStrings,TemplateHaskell,TypeFamilies,DeriveDataTypeable,ScopedTypeVariables #-}
module Examples where

import Control.Monad
import Control.Monad.Trans
import Language.SMTLib2
import Language.SMTLib2.TH
import Language.SMTLib2.Internals (declareType)
import Data.Typeable
import Data.Array
import Data.Word
import Data.Int
import qualified Data.ByteString as BS

funTest :: SMT (Maybe Integer)
funTest = do
  f <- fun :: SMT (SMTFun (SMTExpr Integer,SMTExpr Integer) Integer)
  g <- defFun (\x -> f `app` (x,x))
  q <- var
  assert $ forAll $ \x -> g `app` x .==. 2
  assert $ q .==. (f `app` (3,3))
  r <- checkSat
  if r
    then (do
             vq <- getValue q
             return $ Just vq)
    else return Nothing

quantifierTest :: SMT (Maybe Integer)
quantifierTest = do
  setOption (PrintSuccess False)
  setOption (ProduceModels True)
  v1 <- var :: SMT (SMTExpr Integer)
  assert $ forAll $ \(x,y) -> v1 * x .==. v1 * y
  r <- checkSat
  if r
    then (do
             r1 <- getValue v1
             return $ Just r1)
    else return Nothing

bvTest :: SMT (Maybe BV8)
bvTest = do
  v1 <- var
  v2 <- var
  v3 <- var
  assert $ v1 .==. 16
  assert $ v2 .==. 35
  assert $ v3 .==. v1 + v2
  r <- checkSat
  if r
    then fmap Just $ getValue v3
    else return Nothing

bvTest2 :: SMT (Maybe (BV8,BV8,BV8,BitVector (BVTyped N24)))
bvTest2 = do
  v1 <- var :: SMT (SMTExpr BV8)
  v2 <- var :: SMT (SMTExpr BV8)
  v3 <- var :: SMT (SMTExpr BV8)
  res <- var
  assert $ not' $ v1 .==. 0
  assert $ not' $ v2 .==. 0
  assert $ v3 .==. bvadd v1 v2
  assert $ res .==. bvconcat v1 (bvconcat v2 v3)
  r <- checkSat
  if r
    then (do
             r1 <- getValue v1
             r2 <- getValue v2
             r3 <- getValue v3
             rr <- getValue res
             return $ Just (r1,r2,r3,rr))
    else return Nothing

transposeTest :: SMT ([Integer],Bool)
transposeTest = do
  let c1 = listArray (0,9) [6,2,4,5,1,9,0,3,8,7]
      c2 = listArray (0,9) [2,9,3,6,1,8,7,0,5,4]
  v1 <- var :: SMT (SMTExpr (SMTArray (SMTExpr Integer) Integer))
  v2 <- var :: SMT (SMTExpr (SMTArray (SMTExpr Integer) Integer))
  v3 <- var :: SMT (SMTExpr (SMTArray (SMTExpr Integer) Integer))
  assert $ arrayEquals v1 c1
  assert $ arrayEquals v2 c2
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

add :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer -> SMT ()
add x y c r rc = assert (ite 
                         ((app plus [x,y,c]) .>=. 10)
                         ((r .==. ((app plus [x,y,c]) - 10)) .&&.
                          (rc .==. 1))
                         ((r .==. (app plus [x,y,c])) .&&.
                          (rc .==. 0)
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
  assert (app and' [v .>=. 0
                   | v <- alls
                   ])
  assert (app and' [v .<. 10
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

type Problem = [[Maybe Word8]]

emptyProblem :: Problem
emptyProblem = replicate 9 (replicate 9 Nothing)

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

sudoku :: Problem -> SMT (Maybe [[BV8]])
sudoku prob = do
  setOption (PrintSuccess False)
  setOption (ProduceModels True)
  myfield <- mapM (\_ -> mapM (\_ -> var) [0..8]) [0..8]
  mapM_ (mapM_ (\v -> assert $ app and' [ bvult v 10, bvugt v 0])) myfield
  mapM_ (\line -> assert $ distinct line) myfield
  mapM_ (\i -> assert $ distinct [ line!!i | line <- myfield ]) [0..8]
  assert $ distinct [ myfield!!i!!j | i <- [0..2],j <- [0..2] ]
  assert $ distinct [ myfield!!i!!j | i <- [0..2],j <- [3..5] ]
  assert $ distinct [ myfield!!i!!j | i <- [0..2],j <- [6..8] ]

  assert $ distinct [ myfield!!i!!j | i <- [3..5],j <- [0..2] ]
  assert $ distinct [ myfield!!i!!j | i <- [3..5],j <- [3..5] ]
  assert $ distinct [ myfield!!i!!j | i <- [3..5],j <- [6..8] ]

  assert $ distinct [ myfield!!i!!j | i <- [6..8],j <- [0..2] ]
  assert $ distinct [ myfield!!i!!j | i <- [6..8],j <- [3..5] ]
  assert $ distinct [ myfield!!i!!j | i <- [6..8],j <- [6..8] ]

  sequence_ [ sequence_ [ case el of
                            Nothing -> return ()
                            Just n -> assert $ myfield!!i!!j .==. (constant $ BitVector $ fromIntegral n)
                          | (el,j) <- zip line [0..8]
                        ] 
              | (line,i) <- zip prob [0..8] ]

  res <- checkSat
  if res 
    then fmap Just $ mapM (mapM getValue) myfield
    else return Nothing

displaySolution :: [[BV8]] -> String
displaySolution = displayLines . fmap displayLine
    where
      displayLines [a,b,c,d,e,f,g,h,i] = unlines [a,b,c,"",d,e,f,"",g,h,i]
      displayLine [a,b,c,d,e,f,g,h,i] = show a ++ show b ++ show c ++ " " ++ show d ++ show e ++ show f ++ " " ++ show g ++ show h ++ show i

-- Bitvector concat example
concatExample :: SMT (Maybe BV16)
concatExample = do
  x1 <- var :: SMT (SMTExpr BV8)
  x2 <- var :: SMT (SMTExpr BV8)
  res <- var
  assert $ res .==. bvconcat x1 x2
  assert $ bvugt x1 2
  assert $ bvugt x2 8
  r <- checkSat
  if r
    then fmap Just $ getValue res
    else return Nothing

arrayExample :: SMT (Maybe Integer)
arrayExample = do
  f <- fun
  v <- var
  assert $ forAll $ \i -> (f `app` i) .==. (i*2)
  assert $ v .==. select (asArray f) 4
  r <- checkSat
  if r
    then fmap Just $ getValue v
    else return Nothing

arrayExample2 :: SMT (Maybe [[Integer]])
arrayExample2 = do
  arr <- var :: SMT (SMTExpr (SMTArray (SMTExpr Integer,SMTExpr Integer) Integer))
  assert $ select arr (0,1) .==. 9
  assert $ select arr (2,4) .==. 7
  assert $ select arr (3,5) .==. 2
  assert $ forAll $ \(i,j) -> select arr (i,j) .==. select arr (j,i)
  r <- checkSat
  if r
    then fmap Just $ sequence [ sequence [ getValue (select arr (constant i,constant j)) | j <- [0..9] ] | i <- [0..9] ]
    else return Nothing

data Coordinate = Position { posX :: Integer
                           , posY :: Integer
                           }
                | Unknown
                deriving (Eq,Typeable,Show)

$(deriveSMT ''Coordinate)

main = print "Blubb"


datatypeTest :: SMT (Maybe (Coordinate,Coordinate))
datatypeTest = do
  v1 <- var
  v2 <- var
  assert $ ((v1 .# $(field 'posX)) + (v2 .# $(field 'posX))) .==. 5
  assert $ ((v1 .# $(field 'posY)) * (v2 .# $(field 'posY))) .==. 12
  r <- checkSat
  if r
    then (do
             r1 <- getValue v1
             r2 <- getValue v2
             return $ Just (r1,r2))
    else return Nothing

data BinNode a = BinNode { nodeVal :: a, subTree :: BinTree a }
               | TerminalBinNode
               deriving (Eq, Show, Typeable)

data BinTree a = BinTree
                 { leftBranch :: BinNode a
                 , rightBranch :: BinNode a
                 }
               deriving (Eq, Show, Typeable)

-- $(deriveSMT ''BinNode)
$(deriveSMT ''BinTree)

datatypeTest2 :: SMT (BinNode Integer)
datatypeTest2 = do
  v <- var
  assert $ v .==. (constant tree)
  checkSat
  getValue v
  where
    tree :: BinNode Integer
    tree = BinNode 1 $ BinTree
           (BinNode 2 $ BinTree
            (BinNode 3 $ BinTree
             (BinNode 4 $ BinTree TerminalBinNode TerminalBinNode)
             TerminalBinNode)
            (BinNode 5 $ BinTree TerminalBinNode TerminalBinNode))
           (BinNode 6 $ BinTree TerminalBinNode TerminalBinNode)

data MyTuple a b = MyTuple { myFst :: a, mySnd :: b } deriving (Eq, Show, Typeable)
data ReusingRecord a = ReusingRecord { someF :: MyTuple (Maybe a) Integer } deriving (Eq, Show, Typeable)

-- $(deriveSMT ''MyTuple)
$(deriveSMT ''ReusingRecord)

datatypeTest3 :: SMT (ReusingRecord Integer)
datatypeTest3 = do
  v <- var
  assert $ v .==. (constant r)
  checkSat
  getValue v
  where r = ReusingRecord $ MyTuple (Just 1) 2

unsatCoreTest :: SMT [String]
unsatCoreTest = do
  setOption (ProduceUnsatCores True)
  x <- var :: SMT (SMTExpr Integer)
  y1 <- var
  y2 <- var
  z <- var
  (a1,_) <- named "First" (x .==. y1)
  (a2,_) <- named "Second" (not' $ z .<. 0)
  (a3,_) <- named "Third" (y1 .==. z)
  b <- defConst (app and' [x.==.y2,not' $ y2 .==. z])
  
  assert a1
  assert a2
  assert a3
  assert b
  
  checkSat
  getUnsatCore

interpolationTest :: SMT (SMTExpr Bool)
interpolationTest = do
  setOption (ProduceInterpolants True)
  (x,y1,y2,z::SMTExpr Integer) <- argVars
  g1 <- interpolationGroup
  g2 <- interpolationGroup
  g3 <- interpolationGroup
  a1 <- defConst $ x .==. y1
  a2 <- defConst $ y1 .==. z
  b <- defConst $ (x .==. y2) .&&. (not' $ y2 .==. z)
  assertInterp a1 g1
  assertInterp a2 g2
  assertInterp b g3
  checkSat
  getInterpolant [g1,g2]