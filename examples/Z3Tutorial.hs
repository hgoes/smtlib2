{-# LANGUAGE QuasiQuotes,DataKinds,GADTs,RankNTypes,ScopedTypeVariables,KindSignatures,TemplateHaskell, FlexibleInstances,TypeFamilies #-}
module Z3Tutorial where

import Language.SMTLib2
import Language.SMTLib2.Pipe (createPipe)
import Language.SMTLib2.Debug (debugBackend)
import qualified Language.SMTLib2.Internals.Type.List as List
import qualified Language.SMTLib2.Internals.Expression as SMT
import qualified Language.SMTLib2.Internals.Type as Type

import Data.Proxy
import Data.GADT.Compare
import Data.GADT.Show
import Data.Typeable

runExample :: (forall b. Backend b => SMT b r) -> IO r
runExample ex = withBackend (fmap debugBackend $ createPipe "z3" ["-in","-smt2"]) ex

query :: (Backend b)
      => List Repr tps
      -> (List (Expr b) tps -> SMT b ())
      -> SMT b (Maybe (List Value tps))
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
  assert $ a .>. cint 10
  assert $ fun f (a .:. true .:. nil) .<. cint 100
  res <- checkSat
  case res of
    Sat -> do
      IntValue v <- getValue a
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
        IntValue vx <- getValue x
        IntValue vy <- getValue y
        IntValue vz <- getValue z
        return (Just (vx,vy,vz))
      _ -> return Nothing
  q2 <- stack $ do
    (cint 3 .*. x) .+. y .==. cint 10 >>= assert
    (cint 2 .*. x) .+. (cint 2 .*. y) .==. cint 21 >>= assert
    r2 <- checkSat
    case r2 of
      Sat -> do
        IntValue vx <- getValue x
        IntValue vy <- getValue y
        IntValue vz <- getValue z
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
  assert $ (fun f (cint 10 .:. nil)) .==. cint 1
  r <- checkSat
  case r of
    Sat -> do
      IntValue ra <- getValue a
      IntValue rb <- getValue b
      return $ Just (ra,rb)
    _ -> return Nothing

example6 :: Backend b => SMT b (Maybe (List Value '[IntType,IntType,IntType,RealType,RealType]))
example6 = query (int ::: int ::: int ::: real ::: real ::: Nil)
           (\(a ::: b ::: c ::: d ::: e ::: Nil) -> do
               a .>. b .+. cint 2 >>= assert
               a .==. (cint 2 .*. c) .+. cint 10 >>= assert
               c .+. b .<=. cint 1000 >>= assert
               d .>=. e >>= assert)

example7 :: Backend b => SMT b (Maybe (List Value [IntType,IntType,IntType,RealType,RealType]))
example7 = query (int ::: int ::: int ::: real ::: real ::: Nil)
           (\(a ::: b ::: c ::: d ::: e ::: Nil) -> do
               e .>. toReal (a .+. b) .+. creal 2 >>= assert
               d .==. toReal c .+. creal 0.5 >>= assert
               a .>. b >>= assert)

example8 :: Backend b => SMT b (Maybe (List Value [RealType,RealType]))
example8 = query (real ::: real ::: Nil)
           (\(b ::: c ::: Nil) -> do
               mult [b,b,b] .+. (b .*. c) .==. creal 3.0 >>= assert)

example9 :: Backend b => SMT b (Maybe (List Value [RealType,RealType,RealType]))
example9 = query (real ::: real ::: real ::: Nil)
           (\(x ::: y ::: z ::: Nil) -> do
               x .*. x .==. x .*. creal 2 >>= assert
               x .*. y .==. x >>= assert
               (y .-. creal 1) .*. z .==. creal 1 >>= assert)

example10 :: Backend b => SMT b (Maybe (List Value [IntType,IntType,IntType,IntType,IntType,IntType,IntType,RealType,RealType]))
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

example11 :: Backend b => SMT b (Maybe (List Value '[BitVecType 64,BitVecType 64]))
example11 = query (bitvec (bw Proxy) ::: bitvec (bw Proxy) ::: Nil)
            (\(x ::: y ::: Nil) -> do
                not' (bvand (bvnot x) (bvnot y) .==. bvnot (bvor x y)) >>= assert)

example13 :: Backend b => SMT b CheckSatResult
example13 = do
  let w = bw (Proxy::Proxy 4)
  isPowerOfTwo <- defineFunNamed "isPowerOfTwo" (bitvec w ::: Nil) $
                  \(x ::: Nil) -> cbv 0 w .==. bvand x (bvsub x (cbv 1 w))
  a <- declareVarNamed (bitvec w) "a"
  args <- sequence [ a .==. cbv n w | n <- [0,1,2,4,8]]
  assert $ not' (fun isPowerOfTwo (a .:. nil) .==. or' args)
  checkSat

example14 :: Backend b => SMT b (Maybe (List Value [BitVecType 8,BitVecType 8]))
example14 = query (bitvec (bw Proxy) ::: bitvec (bw Proxy) ::: Nil)
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
  IntValue vx <- getValue x
  IntValue vy <- getValue y
  return (vx,vy)

example16 :: Backend b => SMT b (Integer,Integer,CheckSatResult)
example16 = do
  all1 <- declareVar (array (int ::: Nil) int)
  a <- declareVar int
  i <- declareVar int
  all1 .==. constArray (int ::: Nil) (cint 1) >>= assert
  a .==. select1 all1 i >>= assert
  checkSat
  IntValue va <- getValue a
  IntValue vi <- getValue i
  assert $ not' (a .==. cint 1)
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
    not' (map' (SMT.Logic SMT.And $(nat 2)) (a .:. b .:. nil) .==.
          (map' SMT.Not ((map' (SMT.Logic SMT.Or $(nat 2))
                          ((map' SMT.Not (b .:. nil)) .:.
                           (map' SMT.Not (a .:. nil)) .:. nil)) .:. nil))) >>= assert
    map' SMT.Not (a .:. nil) .==. b >>= assert
    checkSat
  r2 <- stack $ do
    select (map' (SMT.Logic SMT.And $(nat 2)) (a .:. b .:. nil)) (x .:. nil) .&.
      not' (select a (x .:. nil)) >>= assert
    checkSat
  (r3,r4) <- stack $ do
    select (map' (SMT.Logic SMT.Or $(nat 2)) (a .:. b .:. nil)) (x .:. nil) .&.
      not' (select a (x .:. nil)) >>= assert
    p <- checkSat
    mdl <- getModel
    not' (select b (x .:. nil)) >>= assert
    q <- checkSat
    return (mdl,q)
  return (r1,r2,show r3,r4)

-- | Bags as Arrays
example18 :: Backend b => SMT b String
example18 = do
  let a = array (int ::: int ::: Nil) int
  bagUnion <- defineFunNamed "bag-union" (a ::: a ::: Nil) $
    \(x ::: y ::: Nil) -> map' (SMT.Arith Type.NumInt SMT.Plus $(nat 2)) (x .:. y .:. nil)
  s1 <- declareVarNamed a "s1"
  s2 <- declareVarNamed a "s2"
  s3 <- declareVarNamed a "s3"
  s3 .==. fun bagUnion (s1 .:. s2 .:. nil) >>= assert
  select s1 (cint 0 .:. cint 0 .:. nil) .==. cint 5 >>= assert
  select s2 (cint 0 .:. cint 0 .:. nil) .==. cint 3 >>= assert
  select s2 (cint 1 .:. cint 2 .:. nil) .==. cint 4 >>= assert
  checkSat
  fmap show getModel
  
-- Datatypes

data Pair par (e :: Type -> *) where
  MkPair :: e t1 -> e t2 -> Pair '[t1,t2] e

instance Type.IsDatatype Pair where
  type Parameters Pair = 'S ('S 'Z)
  type Signature Pair = '[ '[ ParameterType Z, ParameterType (S Z) ] ]
  data Datatype Pair = Pair deriving (Eq,Ord)
  data Constr Pair sig where
    ConMkPair :: Type.Constr Pair '[ ParameterType Z, ParameterType (S Z) ]
  data Field Pair sig where
    First :: Type.Field Pair (ParameterType Z)
    Second :: Type.Field Pair (ParameterType (S Z))
  datatypeGet (MkPair x y) = (Pair,getType x ::: getType y ::: Nil)
  parameters _ = Succ (Succ Zero)
  datatypeName _ = "Pair"
  constructors Pair = ConMkPair ::: Nil
  constrName ConMkPair = "MkPair"
  test _ _ = True
  fields ConMkPair = First ::: Second ::: Nil
  construct (_ ::: _ ::: Nil) ConMkPair (x ::: y ::: Nil) = MkPair x y
  deconstruct (MkPair x y)
    = Type.ConApp
      (getType x ::: getType y ::: Nil)
      ConMkPair
      (x ::: y ::: Nil)
  fieldType First = ParameterRepr Zero
  fieldType Second = ParameterRepr (Succ Zero)
  fieldName First = "first"
  fieldName Second = "second"
  fieldGet (MkPair x _) First = x
  fieldGet (MkPair _ y) Second = y

instance GEq (Type.Constr Pair) where
  geq ConMkPair ConMkPair = Just Refl

instance GCompare (Type.Constr Pair) where
  gcompare ConMkPair ConMkPair = GEQ

instance GEq (Type.Field Pair) where
  geq First First = Just Refl
  geq Second Second = Just Refl
  geq _ _ = Nothing

instance GCompare (Type.Field Pair) where
  gcompare First First = GEQ
  gcompare First _ = GLT
  gcompare _ First = GGT
  gcompare Second Second = GEQ

-- | Records
example19 :: Backend b => SMT b (Pair '[IntType,IntType] Value,Pair '[IntType,IntType] Value,CheckSatResult)
example19 = do
  let dt = Pair
  registerDatatype dt
  p1 <- declareVar (DataRepr dt (int ::: int ::: Nil))
  p2 <- declareVar (DataRepr dt (int ::: int ::: Nil))
  assert $ p1 .==. p2
  assert $ (p1 .#. Second) .>. cint 20
  checkSat
  DataValue v1 <- getValue p1
  DataValue v2 <- getValue p2
  assert $ not' $ (p1 .#. First) .==. (p2 .#. First)
  r <- checkSat
  return (v1,v2,r)

data S' (par :: [Type]) (e :: Type -> *) where
  A :: S' '[] e
  B :: S' '[] e
  C :: S' '[] e

instance Type.IsDatatype S' where
  type Parameters S' = 'Z
  type Signature S' = '[ '[], '[], '[] ]
  data Datatype S' = S' deriving (Eq,Ord)
  data Constr S' sig where
    MkA :: Type.Constr S' '[]
    MkB :: Type.Constr S' '[]
    MkC :: Type.Constr S' '[]
  data Field S' sig
  datatypeGet A = (S',Nil)
  datatypeGet B = (S',Nil)
  datatypeGet C = (S',Nil)
  parameters _ = Zero
  datatypeName _ = "S"
  constructors S' = MkA ::: MkB ::: MkC ::: Nil
  constrName MkA = "A"
  constrName MkB = "B"
  constrName MkC = "C"
  test A MkA = True
  test B MkB = True
  test C MkC = True
  test _ _ = False
  fields MkA = Nil
  fields MkB = Nil
  fields MkC = Nil
  construct Nil MkA Nil = A
  construct Nil MkB Nil = B
  construct Nil MkC Nil = C
  deconstruct A = Type.ConApp Nil MkA Nil
  deconstruct B = Type.ConApp Nil MkB Nil
  deconstruct C = Type.ConApp Nil MkC Nil
  fieldName = undefined
  fieldType = undefined
  fieldGet = undefined

instance GEq (Type.Constr S') where
  geq MkA MkA = Just Refl
  geq MkB MkB = Just Refl
  geq MkC MkC = Just Refl
  geq _ _ = Nothing

instance GCompare (Type.Constr S') where
  gcompare MkA MkA = GEQ
  gcompare MkA _ = GLT
  gcompare _ MkA = GGT
  gcompare MkB MkB = GEQ
  gcompare MkB _ = GLT
  gcompare _ MkB = GGT
  gcompare MkC MkC = GEQ

instance GEq (Type.Field S') where
  geq = undefined
instance GCompare (Type.Field S') where
  gcompare = undefined

-- | Scalars
example20 :: Backend b => SMT b (CheckSatResult,CheckSatResult)
example20 = do
  registerDatatype S'
  x <- declareVarNamed (dt S') "x"
  y <- declareVarNamed (dt S') "y"
  z <- declareVarNamed (dt S') "z"
  u <- declareVarNamed (dt S') "u"
  assert $ distinct [x,y,z]
  r1 <- checkSat
  assert $ distinct [x,y,z,u]
  r2 <- checkSat
  return (r1,r2)

data Lst (par :: [Type]) e where
  Nil' :: Repr t -> Lst '[t] e
  Cons' :: e t -> e (DataType Lst '[t]) -> Lst '[t] e

instance Type.IsDatatype Lst where
  type Parameters Lst = 'S 'Z
  type Signature Lst = '[ '[], '[ParameterType 'Z,DataType Lst '[ParameterType 'Z] ] ]
  data Datatype Lst = Lst deriving (Eq,Ord)
  data Constr Lst sig where
    MkNil :: Type.Constr Lst '[]
    MkCons :: Type.Constr Lst '[ParameterType 'Z,DataType Lst '[ParameterType 'Z] ]
  data Field Lst tp where
    Hd :: Type.Field Lst (ParameterType 'Z)
    Tl :: Type.Field Lst (DataType Lst '[ParameterType 'Z])
  datatypeGet (Nil' tp) = (Lst,tp ::: Nil)
  datatypeGet (Cons' e _) = (Lst,getType e ::: Nil)
  parameters _ = Succ Zero
  datatypeName _ = "Lst"
  constructors _ = MkNil ::: MkCons ::: Nil
  constrName MkNil = "nil"
  constrName MkCons = "cons"
  test (Nil' _) MkNil = True
  test (Cons' _ _) MkCons = True
  test _ _ = False
  fields MkNil = Nil
  fields MkCons = Hd ::: Tl ::: Nil
  construct (tp ::: Nil) MkNil Nil = Nil' tp
  construct (tp ::: Nil) MkCons (hd ::: tl ::: Nil) = Cons' hd tl
  deconstruct (Nil' tp) = Type.ConApp (tp ::: Nil) MkNil Nil
  deconstruct (Cons' x xs) = Type.ConApp (getType x ::: Nil) MkCons
                             (x ::: xs ::: Nil)
  fieldName Hd = "hd"
  fieldName Tl = "tl"
  fieldType Hd = ParameterRepr Zero
  fieldType Tl = DataRepr Lst (ParameterRepr Zero ::: Nil)
  fieldGet (Cons' hd _) Hd = hd
  fieldGet (Cons' _ tl) Tl = tl

instance GEq (Type.Constr Lst) where
  geq MkNil MkNil = Just Refl
  geq MkCons MkCons = Just Refl
  geq _ _ = Nothing

instance GCompare (Type.Constr Lst) where
  gcompare MkNil MkNil = GEQ
  gcompare MkNil _ = GLT
  gcompare _ MkNil = GGT
  gcompare MkCons MkCons = GEQ

instance GEq (Type.Field Lst) where
  geq Hd Hd = Just Refl
  geq Tl Tl = Just Refl
  geq _ _ = Nothing

instance GCompare (Type.Field Lst) where
  gcompare Hd Hd = GEQ
  gcompare Hd _ = GLT
  gcompare _ Hd = GGT
  gcompare Tl Tl = GEQ

-- | Recursive datatypes
example21 :: Backend b => SMT b (CheckSatResult,CheckSatResult)
example21 = do
  registerDatatype Lst
  l1 <- declareVarNamed (dt' Lst (int ::: Nil)) "l1"
  l2 <- declareVarNamed (dt' Lst (int ::: Nil)) "l2"
  l3 <- declareVarNamed (dt' Lst (int ::: Nil)) "l3"
  x <- declareVarNamed int "x"
  assert $ not' $ l1 .==. cdt (Nil' int)
  assert $ not' $ l2 .==. cdt (Nil' int)
  assert $ (l1 .#. Hd) .==. (l2 .#. Hd)
  assert $ not' $ l1 .==. l2
  assert $ l3 .==. (mk Lst (int ::: Nil) MkCons (x ::: l2 ::: Nil))
  assert $ x .>. cint 100
  r1 <- checkSat
  getModel
  assert $ (l1 .#. Tl) .==. (l2 .#. Tl)
  r2 <- checkSat
  return (r1,r2)

data Tree par e where
  Leaf :: Repr t -> Tree '[t] e
  Node :: e t -> e (DataType TreeList '[t]) -> Tree '[t] e

data TreeList par e where
  TLNil :: Repr t -> TreeList '[t] e
  TLCons :: e (DataType Tree '[t]) -> e (DataType TreeList '[t])
         -> TreeList '[t] e

instance Type.IsDatatype Tree where
  type Parameters Tree = 'S 'Z
  type Signature Tree = '[ '[], '[ParameterType 'Z,DataType TreeList '[ParameterType 'Z]] ]
  data Datatype Tree = Tree deriving (Eq,Ord)
  data Constr Tree sig where
    MkLeaf :: Type.Constr Tree '[]
    MkNode :: Type.Constr Tree '[ParameterType 'Z,DataType TreeList '[ParameterType 'Z]]
  data Field Tree tp where
    TValue :: Type.Field Tree (ParameterType 'Z)
    TChildren :: Type.Field Tree (DataType TreeList '[ParameterType 'Z])
  datatypeGet (Leaf tp) = (Tree,tp ::: Nil)
  datatypeGet (Node v _) = (Tree,getType v:::Nil)
  parameters _ = Succ Zero
  datatypeName _ = "Tree"
  constructors _ = MkLeaf ::: MkNode ::: Nil
  constrName MkLeaf = "leaf"
  constrName MkNode = "node"
  test (Leaf _) MkLeaf = True
  test (Node _ _) MkNode = True
  test _ _ = False
  fields MkLeaf = Nil
  fields MkNode = TValue ::: TChildren ::: Nil
  construct (tp ::: Nil) MkLeaf Nil = Leaf tp
  construct (tp ::: Nil) MkNode (v ::: ch ::: Nil) = Node v ch
  deconstruct (Leaf tp) = Type.ConApp (tp ::: Nil) MkLeaf Nil
  deconstruct (Node x xs) = Type.ConApp (getType x ::: Nil) MkNode (x:::xs:::Nil)
  fieldName TValue = "value"
  fieldName TChildren = "children"
  fieldType TValue = ParameterRepr Zero
  fieldType TChildren = DataRepr TreeList (ParameterRepr Zero ::: Nil)
  fieldGet (Node x _) TValue = x
  fieldGet (Node _ xs) TChildren = xs

instance Type.IsDatatype TreeList where
  type Parameters TreeList = 'S 'Z
  type Signature TreeList = '[ '[], '[ DataType Tree '[ParameterType 'Z]
                                     , DataType TreeList '[ParameterType 'Z]] ]
  data Datatype TreeList = TreeList deriving (Eq,Ord)
  data Constr TreeList sig where
    MkTLNil :: Type.Constr TreeList '[]
    MkTLCons :: Type.Constr TreeList '[ DataType Tree '[ParameterType 'Z]
                                      , DataType TreeList '[ParameterType 'Z]]
  data Field TreeList sig where
    Car :: Type.Field TreeList (DataType Tree '[ParameterType 'Z])
    Cdr :: Type.Field TreeList (DataType TreeList '[ParameterType 'Z])
  datatypeGet (TLNil tp) = (TreeList,tp:::Nil)
  datatypeGet (TLCons x _) = case getType x of
    DataRepr _ (tp:::Nil) -> (TreeList,tp:::Nil)
  parameters _ = Succ Zero
  datatypeName _ = "TreeList"
  constructors _ = MkTLNil ::: MkTLCons ::: Nil
  constrName MkTLNil = "nil"
  constrName MkTLCons = "cons"
  test (TLNil _) MkTLNil = True
  test (TLCons _ _) MkTLCons = True
  test _ _ = False
  fields MkTLNil = Nil
  fields MkTLCons = Car ::: Cdr ::: Nil
  construct (tp ::: Nil) MkTLNil Nil = TLNil tp
  construct (tp ::: Nil) MkTLCons (x:::xs:::Nil) = TLCons x xs
  deconstruct (TLNil tp) = Type.ConApp (tp:::Nil) MkTLNil Nil
  deconstruct (TLCons x xs) = case getType x of
    DataRepr _ (tp:::Nil) -> Type.ConApp (tp:::Nil) MkTLCons (x:::xs:::Nil)
  fieldName Car = "car"
  fieldName Cdr = "cdr"
  fieldType Car = DataRepr Tree (ParameterRepr Zero:::Nil)
  fieldType Cdr = DataRepr TreeList (ParameterRepr Zero:::Nil)
  fieldGet (TLCons x _) Car = x
  fieldGet (TLCons _ xs) Cdr = xs

instance GEq (Type.Constr Tree) where
  geq MkLeaf MkLeaf = Just Refl
  geq MkNode MkNode = Just Refl
  geq _ _ = Nothing

instance GEq (Type.Constr TreeList) where
  geq MkTLNil MkTLNil = Just Refl
  geq MkTLCons MkTLCons = Just Refl
  geq _ _ = Nothing

instance GCompare (Type.Constr Tree) where
  gcompare MkLeaf MkLeaf = GEQ
  gcompare MkLeaf _ = GLT
  gcompare _ MkLeaf = GGT
  gcompare MkNode MkNode = GEQ

instance GCompare (Type.Constr TreeList) where
  gcompare MkTLNil MkTLNil = GEQ
  gcompare MkTLNil _ = GLT
  gcompare _ MkTLNil = GGT
  gcompare MkTLCons MkTLCons = GEQ

instance GEq (Type.Field Tree) where
  geq TValue TValue = Just Refl
  geq TChildren TChildren = Just Refl
  geq _ _ = Nothing

instance GEq (Type.Field TreeList) where
  geq Car Car = Just Refl
  geq Cdr Cdr = Just Refl
  geq _ _ = Nothing

instance GCompare (Type.Field Tree) where
  gcompare TValue TValue = GEQ
  gcompare TValue _ = GLT
  gcompare _ TValue = GGT
  gcompare TChildren TChildren = GEQ

instance GCompare (Type.Field TreeList) where
  gcompare Car Car = GEQ
  gcompare Car _ = GLT
  gcompare _ Car = GGT
  gcompare Cdr Cdr = GEQ

-- | Mutually recursive datatypes
example22 :: Backend b => SMT b (CheckSatResult)
example22 = do
  registerDatatype Tree
  t1 <- declareVarNamed (dt' Tree (int:::Nil)) "t1"
  t2 <- declareVarNamed (dt' Tree (bool:::Nil)) "t2"
  assert $ not' $ t1 .==. cdt (Leaf int)
  assert $ (t1 .#. TValue) .>. cint 20
  assert $ not' $ is t2 MkLeaf
  assert $ not' $ t2 .#. TValue
  r <- checkSat
  getModel
  return r
