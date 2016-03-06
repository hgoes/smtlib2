{-# LANGUAGE QuasiQuotes,DataKinds,GADTs,RankNTypes,ScopedTypeVariables,KindSignatures,TemplateHaskell, FlexibleInstances,TypeFamilies #-}
module Main where

import Language.SMTLib2 hiding (nil)
import Language.SMTLib2.Pipe (createPipe)
import Language.SMTLib2.Debug (debugBackend)
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Interface
import qualified Language.SMTLib2.Internals.Expression as SMT
import qualified Language.SMTLib2.Internals.Type as Type

import Data.Proxy

runExample :: (forall b. Backend b => SMT b r) -> IO r
runExample ex = withBackend (fmap debugBackend $ createPipe "z3" ["-in","-smt2"]) ex

query :: (Backend b)
      => List Repr tps
      -> (List (Expr b) tps -> SMT b ())
      -> SMT b (Maybe (List ConcreteValue tps))
query tps f = do
  args <- List.mapM declareVar tps
  f args
  res <- checkSat
  case res of
    Sat -> do
      vals <- List.mapM getValue args
      return $ Just vals
    _ -> return Nothing

-- | Basic commands
example1 :: Backend b => SMT b (Maybe Integer)
example1 = do
  a <- declareVar int
  f <- declareFun (int ::: bool ::: Nil) int
  a .>. cint 10 >>= assert
  fun f (a <:> true <:> nil) .<. cint 100 >>= assert
  res <- checkSat
  case res of
    Sat -> do
      IntValueC v <- getValue a
      return $ Just v
    _ -> return Nothing

-- | Using scopes
example2 :: Backend b => SMT b (Maybe (Integer,Integer,Integer),Maybe (Integer,Integer,Integer))
example2 = do
  x <- declareVar int
  y <- declareVar int
  z <- declareVar int
  q1 <- stack $ do
    x .+. y .==. cint 10 >>= assert
    x .+. (cint 2 .*. y) .==. cint 20 >>= assert
    r1 <- checkSat
    case r1 of
      Sat -> do
        IntValueC vx <- getValue x
        IntValueC vy <- getValue y
        IntValueC vz <- getValue z
        return (Just (vx,vy,vz))
      _ -> return Nothing
  q2 <- stack $ do
    (cint 3 .*. x) .+. y .==. cint 10 >>= assert
    (cint 2 .*. x) .+. (cint 2 .*. y) .==. cint 21 >>= assert
    r2 <- checkSat
    case r2 of
      Sat -> do
        IntValueC vx <- getValue x
        IntValueC vy <- getValue y
        IntValueC vz <- getValue z
        return (Just (vx,vy,vz))
      _ -> return Nothing
  return (q1,q2)

-- | Propositional Logic
example3 :: Backend b => SMT b CheckSatResult
example3 = do
  p <- declareVar bool
  q <- declareVar bool
  r <- declareVar bool
  conjecture <- ((p .=>. q) .&. (q .=>. r)) .=>. (p .=>. r) >>= defineVar
  not' conjecture >>= assert
  checkSat

-- | Satisfiability and Validity
example4 :: Backend b => SMT b CheckSatResult
example4 = do
  a <- declareVarNamed bool "a"
  b <- declareVarNamed bool "b"
  demorgan <- (a .&. b) .==. (not' $ (not' a) .|. (not' b)) >>= defineVarNamed "demorgan"
  not' demorgan >>= assert
  checkSat

-- | Uninterpreted functions and constants
example5 :: Backend b => SMT b (Maybe (Integer,Integer))
example5 = do
  f <- declareFun (int ::: Nil) int
  a <- declareVar int
  b <- declareVar int
  a .>. cint 20 >>= assert
  b .>. a >>= assert
  (fun f (cint 10 <:> nil)) .==. cint 1 >>= assert
  r <- checkSat
  case r of
    Sat -> do
      IntValueC ra <- getValue a
      IntValueC rb <- getValue b
      return $ Just (ra,rb)
    _ -> return Nothing

example6 :: Backend b => SMT b (Maybe (List ConcreteValue '[IntType,IntType,IntType,RealType,RealType]))
example6 = query (int ::: int ::: int ::: real ::: real ::: Nil)
           (\(a ::: b ::: c ::: d ::: e ::: Nil) -> do
               a .>. b .+. cint 2 >>= assert
               a .==. (cint 2 .*. c) .+. cint 10 >>= assert
               c .+. b .<=. cint 1000 >>= assert
               d .>=. e >>= assert)

example7 :: Backend b => SMT b (Maybe (List ConcreteValue [IntType,IntType,IntType,RealType,RealType]))
example7 = query (int ::: int ::: int ::: real ::: real ::: Nil)
           (\(a ::: b ::: c ::: d ::: e ::: Nil) -> do
               e .>. toReal (a .+. b) .+. creal 2 >>= assert
               d .==. toReal c .+. creal 0.5 >>= assert
               a .>. b >>= assert)

example8 :: Backend b => SMT b (Maybe (List ConcreteValue [RealType,RealType]))
example8 = query (real ::: real ::: Nil)
           (\(b ::: c ::: Nil) -> do
               mult [b,b,b] .+. (b .*. c) .==. creal 3.0 >>= assert)

example9 :: Backend b => SMT b (Maybe (List ConcreteValue [RealType,RealType,RealType]))
example9 = query (real ::: real ::: real ::: Nil)
           (\(x ::: y ::: z ::: Nil) -> do
               x .*. x .==. x .*. creal 2 >>= assert
               x .*. y .==. x >>= assert
               (y .-. creal 1) .*. z .==. creal 1 >>= assert)

example10 :: Backend b => SMT b (Maybe (List ConcreteValue [IntType,IntType,IntType,IntType,IntType,IntType,IntType,RealType,RealType]))
example10 = query (int ::: int ::: int ::: int ::: int ::: int ::: int ::: real ::: real ::: Nil)
            (\(a ::: r1 ::: r2 ::: r3 ::: r4 ::: r5 ::: r6 ::: b ::: c ::: Nil) -> do
                a .==. cint 10 >>= assert
                r1 .==. a `div'` cint 4 >>= assert
                r2 .==. a `mod'` cint 4 >>= assert
                r3 .==. a `rem'` cint 4 >>= assert
                r4 .==. a `div'` cint (-4) >>= assert
                r5 .==. a `mod'` cint (-4) >>= assert
                r6 .==. a `rem'` cint (-4) >>= assert
                b .>=. c ./. creal 3 >>= assert
                c .>=. creal 20 >>= assert)

example11 :: Backend b => SMT b (Maybe (List ConcreteValue '[BitVecType $(natT 64),BitVecType $(natT 64)]))
example11 = query (bitvec $(nat 64) ::: bitvec $(nat 64) ::: Nil)
            (\(x ::: y ::: Nil) -> do
                not' (bvand (bvnot x) (bvnot y) .==. bvnot (bvor x y)) >>= assert)

example13 :: Backend b => SMT b CheckSatResult
example13 = do
  let bw = $(nat 4)
  isPowerOfTwo <- defineFunNamed "isPowerOfTwo" (bitvec bw ::: Nil) $
                  \(x ::: Nil) -> cbv 0 bw .==. bvand x (bvsub x (cbv 1 bw))
  a <- declareVarNamed (bitvec bw) "a"
  args <- sequence [ a .==. cbv n bw | n <- [0,1,2,4,8]]
  not' (fun isPowerOfTwo (a <:> nil) .==. or' args) >>= assert
  checkSat

example14 :: Backend b => SMT b (Maybe (List ConcreteValue [BitVecType $(natT 8),BitVecType $(natT 8)]))
example14 = query (bitvec $(nat 8) ::: bitvec $(nat 8) ::: Nil)
            $ \(a ::: b ::: Nil) -> do
  not' (bvule a b .==. bvsle a b) >>= assert

example15 :: Backend b => SMT b (Integer,Integer)
example15 = do
  x <- declareVar int
  y <- declareVar int
  a1 <- declareVar (array (int ::: Nil) int)
  select1 a1 x .==. x >>= assert
  store1 a1 x y .==. a1 >>= assert
  --not' (x .==. y) >>= assert
  checkSat
  IntValueC vx <- getValue x
  IntValueC vy <- getValue y
  return (vx,vy)

example16 :: Backend b => SMT b (Integer,Integer,CheckSatResult)
example16 = do
  all1 <- declareVar (array (int ::: Nil) int)
  a <- declareVar int
  i <- declareVar int
  all1 .==. constArray (int ::: Nil) (cint 1) >>= assert
  a .==. select1 all1 i >>= assert
  checkSat
  IntValueC va <- getValue a
  IntValueC vi <- getValue i
  [expr| (not (= a 1)) |] >>= assert
  r <- checkSat
  return (va,vi,r)

-- | Mapping Functions on Arrays
example17 :: Backend b => SMT b (CheckSatResult,CheckSatResult,String,CheckSatResult)
example17 = do
  a <- declareVar (array (int ::: Nil) bool)
  b <- declareVar (array (int ::: Nil) bool)
  c <- declareVar (array (int ::: Nil) bool)
  x <- declareVar int
  r1 <- stack $ do
    not' (map' (SMT.Logic SMT.And $(nat 2)) (a <:> b <:> nil) .==.
          (map' SMT.Not ((map' (SMT.Logic SMT.Or $(nat 2))
                          ((map' SMT.Not (b <:> nil)) <:>
                           (map' SMT.Not (a <:> nil)) <:> nil)) <:> nil))) >>= assert
    map' SMT.Not (a <:> nil) .==. b >>= assert
    checkSat
  r2 <- stack $ do
    select (map' (SMT.Logic SMT.And $(nat 2)) (a <:> b <:> nil)) (x <:> nil) .&.
      not' (select a (x <:> nil)) >>= assert
    checkSat
  (r3,r4) <- stack $ do
    select (map' (SMT.Logic SMT.Or $(nat 2)) (a <:> b <:> nil)) (x <:> nil) .&.
      not' (select a (x <:> nil)) >>= assert
    p <- checkSat
    mdl <- getModel
    not' (select b (x <:> nil)) >>= assert
    q <- checkSat
    return (mdl,q)
  return (r1,r2,show r3,r4)

-- | Bags as Arrays
example18 :: Backend b => SMT b String
example18 = do
  let a = array (int ::: int ::: Nil) int
  bagUnion <- defineFunNamed "bag-union" (a ::: a ::: Nil) $
    \(x ::: y ::: Nil) -> map' (SMT.Arith Type.NumInt SMT.Plus $(nat 2)) (x <:> y <:> nil)
  s1 <- declareVarNamed a "s1"
  s2 <- declareVarNamed a "s2"
  s3 <- declareVarNamed a "s3"
  s3 .==. fun bagUnion (s1 <:> s2 <:> nil) >>= assert
  select s1 (cint 0 <:> cint 0 <:> nil) .==. cint 5 >>= assert
  select s2 (cint 0 <:> cint 0 <:> nil) .==. cint 3 >>= assert
  select s2 (cint 1 <:> cint 2 <:> nil) .==. cint 4 >>= assert
  checkSat
  fmap show getModel
  
-- Datatypes

{-data Pair t1 t2 = MkPair { first :: t1
                         , second :: t2 } deriving (Eq,Ord,Show)

pairDt = Type.Datatype { Type.datatypeName = "Pair"
                       , Type.constructors = Type.ConsCon mkPair Type.NoCon
                       }
  where
    mkPair = Type.Constr { Type.conName = "MkPair"
                         , Type.conFields = Type.Field { Type.fieldName = "first"
                                                       , Type.fieldType = int
                                                       , Type.fieldGet = IntValueC . first }
                                            :::
                                            Type.Field { Type.fieldName = "second"
                                                       , Type.fieldType = int
                                                       , Type.fieldGet = IntValueC . second }
                                            ::: Nil
                         , Type.construct = \(IntValueC x ::: IntValueC y ::: Nil)
                                            -> MkPair x y
                         , Type.conTest = \_ -> True }

instance Type.IsDatatype (Pair Integer Integer) where
  type DatatypeSig (Pair Integer Integer) = '[ '[IntType,IntType]]
  type TypeCollectionSig (Pair Integer Integer) = '[ '( '[ '[IntType,IntType]],Pair Integer Integer)]
  getDatatype _ = pairDt
  getTypeCollection _ = Type.ConsDts pairDt Type.NoDts
  getConstructor (MkPair x y) (Type.ConsCon mkPair Type.NoCon) f
    = f mkPair (IntValueC x ::: IntValueC y ::: Nil)
  
example19 :: Backend b => SMT b (Pair Integer Integer,Pair Integer Integer)
example19 = do
  registerDatatype (Proxy::Proxy (Pair Integer Integer)) -}
