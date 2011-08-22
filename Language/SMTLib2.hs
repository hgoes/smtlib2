{-# LANGUAGE OverloadedStrings,GADTs,FlexibleInstances #-}
module Language.SMTLib2 where

import Data.Attoparsec
import qualified Data.AttoLisp as L
import qualified Data.Attoparsec.Number as L
import Data.ByteString as BS
import Blaze.ByteString.Builder
import System.Process
import System.IO
import Data.Monoid
import Control.Monad.Reader
import Control.Monad.State
import Data.Text as T

type SMT = ReaderT (Handle,Handle) (StateT Integer IO)

class SMTType t where
  getSort :: t -> L.Lisp
  unmangle :: L.Lisp -> t
  mangle :: t -> L.Lisp

instance SMTType Integer where
  getSort _ = L.Symbol "Int"
  unmangle (L.Number (L.I v)) = v
  unmangle (L.List [L.Symbol "-"
                   ,L.Number (L.I v)]) = - v
  unmangle e = error $ "can't unmangle "++show e++" to Integer"
  mangle v = L.toLisp v

instance SMTType Bool where
  getSort _ = L.Symbol "Bool"
  unmangle (L.Symbol "true") = True
  unmangle (L.Symbol "false") = False
  mangle True = L.Symbol "true"
  mangle False = L.Symbol "false"

data SMTExpr t where
  Var :: Text -> SMTExpr t
  Const :: t -> SMTExpr t
  Eq :: SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Ge :: (Num a,SMTType a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Lt :: (Num a,SMTType a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
  Distinct :: SMTType a => [SMTExpr a] -> SMTExpr Bool
  Plus :: Num t => [SMTExpr t] -> SMTExpr t
  Minus :: Num t => SMTExpr t -> SMTExpr t -> SMTExpr t
  Mult :: Num t => [SMTExpr t] -> SMTExpr t
  ITE :: SMTExpr Bool -> SMTExpr t -> SMTExpr t -> SMTExpr t
  And :: [SMTExpr Bool] -> SMTExpr Bool
  Not :: SMTExpr Bool -> SMTExpr Bool

instance SMTType t => Eq (SMTExpr t) where
  (==) x y = (L.toLisp x) == (L.toLisp y)

instance SMTType t => Show (SMTExpr t) where
  show x = show (L.toLisp x)

instance Num (SMTExpr Integer) where
  fromInteger = constant
  (+) x y = plus [x,y]
  (-) = minus
  (*) x y = mult [x,y]

instance SMTType t => L.ToLisp (SMTExpr t) where
  toLisp (Var name) = L.Symbol name
  toLisp (Const x) = mangle x
  toLisp (Eq l r) = L.List [L.Symbol "="
                           ,L.toLisp l
                           ,L.toLisp r]
  toLisp (Distinct lst) = L.List $ [L.Symbol "distinct"]
                          ++ [L.toLisp x | x <- lst ]
  toLisp (Plus lst) = L.List $ [L.Symbol "+"]
                      ++ [L.toLisp x | x <- lst ]
  toLisp (Mult lst) = L.List $ [L.Symbol "*"]
                      ++ [L.toLisp x | x <- lst ]
  toLisp (Minus l r) = L.List $ [L.Symbol "-"
                                ,L.toLisp l
                                ,L.toLisp r]
  toLisp (ITE cond tt ff) = L.List [L.Symbol "ite"
                                   ,L.toLisp cond
                                   ,L.toLisp tt
                                   ,L.toLisp ff]
  toLisp (Ge l r) = L.List [L.Symbol ">="
                           ,L.toLisp l
                           ,L.toLisp r]
  toLisp (Lt l r) = L.List [L.Symbol "<"
                           ,L.toLisp l
                           ,L.toLisp r]
  toLisp (And lst) = L.List $ [L.Symbol "and"]
                     ++ [L.toLisp x | x <- lst ]
  toLisp (Not expr) = L.List $ [L.Symbol "not",L.toLisp expr]

getUndef :: SMTExpr t -> t
getUndef _ = undefined

var :: SMTType t => SMT (SMTExpr t)
var = do
  c <- get
  put (c+1)
  let name = T.pack $ "var"++show c
      res = Var name
      sort = getSort $ getUndef res
  declareFun name [] sort
  return res

constant :: SMTType t => t -> SMTExpr t
constant = Const

eq :: SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool
eq = Eq

geq,lt :: (SMTType a,Num a) => SMTExpr a -> SMTExpr a -> SMTExpr Bool
geq = Ge
lt = Lt

distinct :: SMTType a => [SMTExpr a] -> SMTExpr Bool
distinct = Distinct

plus,mult :: (SMTType a,Num a) => [SMTExpr a] -> SMTExpr a
plus = Plus
mult = Mult

minus :: (SMTType a,Num a) => SMTExpr a -> SMTExpr a -> SMTExpr a
minus = Minus

ite :: (SMTType a) => SMTExpr Bool -> SMTExpr a -> SMTExpr a -> SMTExpr a
ite = ITE

and' :: [SMTExpr Bool] -> SMTExpr Bool
and' = And

not' :: SMTExpr Bool -> SMTExpr Bool
not' = Not

getValue :: SMTType t => SMTExpr t -> SMT t
getValue expr = do
  putRequest $ L.List [L.Symbol "get-value"
                      ,L.List [L.toLisp expr]]
  val <- parseResponse
  case val of
    L.List [L.List [_,res]] -> return $ unmangle res
    _ -> error $ "unknown response to get-value: "++show val

assert :: SMTExpr Bool -> SMT ()
assert expr 
  = putRequest $ L.List [L.Symbol "assert"
                        ,L.toLisp expr]

{- SEND
  +MORE
  -----
  MONEY -}

add x y c r rc = assert (ite 
                         (geq (plus [x,y,c]) 10)
                         (and'
                          [eq r ((plus [x,y,c]) - 10)
                          ,eq rc 1])
                         (and'
                          [eq r (plus [x,y,c])
                          ,eq rc 0]
                         )
                        )

test = withSMTSolver "z3" ["-smt2","-in","-m"] $ do
  [s,e,n,d,m,o,r,y,c0,c1,c2] <- replicateM 11 (var :: SMT (SMTExpr Integer))
  let alls = [s,e,n,d,m,o,r,y]
  assert (distinct alls)
  assert (and' [geq v 0
               | v <- alls
               ])
  assert (and' [lt v 10
               | v <- alls
               ])
  assert (not' (eq m 0))
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

declareFun :: Text -> [Text] -> L.Lisp -> SMT ()
declareFun name tps rtp
  = putRequest $ L.List [L.Symbol "declare-fun"
                        ,L.Symbol name
                        ,args [L.Symbol tp | tp <- tps]
                        ,rtp
                        ]

args :: [L.Lisp] -> L.Lisp
args [] = L.Symbol "()"
args xs = L.List xs

checkSat :: SMT Bool
checkSat = do
  (_,hout) <- ask
  clearInput
  putRequest (L.List [L.Symbol "check-sat"])
  res <- liftIO $ BS.hGetLine hout
  case res of
    "sat" -> return True
    "unsat" -> return False
    _ -> error $ "unknown check-sat response: "++show res
  
stack :: SMT a -> SMT a
stack act = do
  putRequest (L.List [L.Symbol "push"])
  res <- act
  putRequest (L.List [L.Symbol "pop"])
  return res

withSMTSolver :: FilePath -> [String] -> SMT a -> IO a
withSMTSolver solver args f = do
  let cmd = CreateProcess { cmdspec = RawCommand solver args
                          , cwd = Nothing
                          , env = Nothing
                          , std_in = CreatePipe
                          , std_out = CreatePipe
                          , std_err = Inherit
                          , close_fds = False
                          }
  (Just hin,Just hout,_,handle) <- createProcess cmd
  res <- evalStateT (runReaderT (do
                                 res <- f
                                 putRequest (L.List [L.Symbol "exit"])
                                 return res
                                ) (hin,hout)) 0
  hClose hin
  hClose hout
  terminateProcess handle
  waitForProcess handle
  return res

clearInput :: SMT ()
clearInput = do
  (_,hout) <- ask
  r <- liftIO $ hReady hout
  if r
    then (do
             liftIO $ BS.hGetLine hout
             clearInput)
    else return ()

putRequest :: L.Lisp -> SMT ()
putRequest e = do
  (hin,_) <- ask
  liftIO $ toByteStringIO (BS.hPutStr hin) (mappend (L.fromLisp e) flush)
  liftIO $ BS.hPutStrLn hin ""
  liftIO $ hFlush hin

parseResponse :: SMT L.Lisp
parseResponse = do
  (_,hout) <- ask
  str <- liftIO $ BS.hGetLine hout
  let continue (Done _ r) = return r
      continue res@(Partial _) = do
        str <- BS.hGetLine hout
        continue (feed res str)
      continue (Fail _ ctx msg) = error $ "Error parsing response in "++show ctx++": "++msg
  liftIO $ continue $ parse L.lisp str
      