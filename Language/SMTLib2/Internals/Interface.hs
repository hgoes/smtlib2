{-# LANGUAGE TypeFamilies,OverloadedStrings,FlexibleContexts #-}
module Language.SMTLib2.Internals.Interface where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances ()
import Language.SMTLib2.Internals.Translation

import Control.Monad.State
import Data.Typeable
import Data.Text as T
import Data.Map as Map hiding (assocs)
import Data.Array
import qualified Data.AttoLisp as L
import Data.Unit
import Data.Word

-- | Create a new named variable
varNamed :: (SMTType t,Typeable t,Unit (SMTAnnotation t)) => Text -> SMT (SMTExpr t)
varNamed name = varNamedAnn name unit

varNamedAnn :: (SMTType t,Typeable t) => Text -> SMTAnnotation t -> SMT (SMTExpr t)
varNamedAnn name ann = mfix (\e -> varNamed' (getUndef e) name ann)

varNamed' :: (SMTType t,Typeable t) => t -> Text -> SMTAnnotation t -> SMT (SMTExpr t)
varNamed' u name ann = do
  let sort = getSort u ann
      tps = declareType u ann
  modify $ \(c,decl,mp) -> (c,decl,Map.insert name (typeOf u) mp)
  mapM_ (\(tp,act) -> do
            (c,decl,_) <- get
            if Prelude.elem tp decl
              then return ()
              else (do
                       act
                       modify (\(c',decl',mp') -> (c',tp:decl',mp'))
                   )
        ) (Prelude.reverse tps)
  declareFun name [] sort
  mapM_ assert $ additionalConstraints u ann (Var name ann)
  return (Var name ann)

-- | Create a annotated variable
varAnn :: (SMTType t,Typeable t) => SMTAnnotation t -> SMT (SMTExpr t)
varAnn ann = do
  (c,decl,mp) <- get
  put (c+1,decl,mp)
  let name = T.pack $ "var"++show c
  varNamedAnn name ann

-- | Create a fresh new variable
var :: (SMTType t,Typeable t,Unit (SMTAnnotation t)) => SMT (SMTExpr t)
var = do
  (c,decl,mp) <- get
  put (c+1,decl,mp)
  let name = T.pack $ "var"++show c
  varNamed name

argVarsAnn :: Args a => ArgAnnotation a -> SMT a
argVarsAnn ann = do
  (c,decl,mp) <- get
  let ((nc,act),res) = foldExprs 
                       (\(cc,act) u ann' 
                            -> let name = T.pack $ "var"++show cc
                               in ((cc+1,act >> varNamed' (getUndef u) name ann' >> return ())
                                  ,Var name ann')) (c,return ()) undefined ann
  put (nc,decl,mp)
  act
  return res

argVars :: (Args a,Unit (ArgAnnotation a)) => SMT a
argVars = argVarsAnn unit

-- | A constant expression
constant :: (SMTValue t,Unit (SMTAnnotation t)) => t -> SMTExpr t
constant x = Const x unit

constantAnn :: SMTValue t => t -> SMTAnnotation t -> SMTExpr t
constantAnn x ann = Const x ann

-- | Boolean conjunction
and' :: [SMTExpr Bool] -> SMTExpr Bool
and' [] = Const True ()
and' [x] = x
and' xs = And xs

-- | Boolean disjunction
or' :: [SMTExpr Bool] -> SMTExpr Bool
or' [] = Const False ()
or' [x] = x
or' xs = Or xs

-- | Create a boolean expression that encodes that the array is equal to the supplied constant array.
arrayConst :: (LiftArgs i,SMTValue v,Ix (Unpacked i),Unit (ArgAnnotation i),Unit (SMTAnnotation v)) => SMTExpr (SMTArray i v) -> Array (Unpacked i) v -> SMTExpr Bool
arrayConst expr arr = and' [(select expr (liftArgs i unit)) .==. (constant v)
                           | (i,v) <- assocs arr ]

-- | Asserts that a boolean expression is true
assert :: SMTExpr Bool -> SMT ()
assert expr = putRequest $ L.List [L.Symbol "assert"
                                  ,L.toLisp expr]

-- | Set an option for the underlying SMT solver
setOption :: SMTOption -> SMT ()
setOption opt = putRequest $ L.List $ [L.Symbol "set-option"]
                ++(case opt of
                      PrintSuccess v -> [L.Symbol ":print-success"
                                        ,L.Symbol $ if v then "true" else "false"]
                      ProduceModels v -> [L.Symbol ":produce-models"
                                         ,L.Symbol $ if v then "true" else "false"]
                      ProduceProofs v -> [L.Symbol ":produce-proofs"
                                         ,L.Symbol $ if v then "true" else "false"])

-- | Create a new interpolation group
interpolationGroup :: SMT InterpolationGroup
interpolationGroup = do
  (c,decl,mp) <- get
  put (c+1,decl,mp)
  let name = T.pack $ "interp"++show c
  return (InterpolationGroup name)

-- | Create a new uninterpreted function
fun :: (Args a,SMTType r,SMTAnnotation r ~ ()) => SMT (SMTExpr (SMTFun a r))
fun = do
  (c,decl,mp) <- get
  put (c+1,decl,mp)
  let name = T.pack $ "fun"++show c
      res = Fun name
      
      (au,bu,rtp) = getFunUndef res
      
      assertEq :: x -> x -> y -> y
      assertEq _ _ p = p
      
      (au2,tps,_) = createArgs 0
      
  assertEq au au2 $ return ()
  declareFun name [ l | (_,l) <- tps ] (getSort rtp ())
  return res
    
-- | Apply a function to an argument
app :: (Args a,SMTType r) => SMTExpr (SMTFun a r) -> a -> SMTExpr r
app = App

-- | Two expressions shall be equal
(.==.) :: SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.==.) = Eq

infix 4 .==.

-- | Declares all arguments to be distinct
distinct :: SMTType a => [SMTExpr a] -> SMTExpr Bool
distinct = Distinct

-- | Calculate the sum of arithmetic expressions
plus :: (SMTArith a) => [SMTExpr a] -> SMTExpr a
plus = Plus

-- | Calculate the product of arithmetic expressions
mult :: (SMTArith a) => [SMTExpr a] -> SMTExpr a
mult = Mult

-- | Subtracts two expressions
minus :: (SMTArith a) => SMTExpr a -> SMTExpr a -> SMTExpr a
minus = Minus

-- | Divide an arithmetic expression by another
div' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
div' = Div

-- | Perform a modulo operation on an arithmetic expression
mod' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
mod' = Mod

-- | Divide a rational expression by another one
divide :: SMTExpr Rational -> SMTExpr Rational -> SMTExpr Rational
divide = Divide

-- | For an expression @x@, this returns the expression @-x@.
neg :: SMTArith a => SMTExpr a -> SMTExpr a
neg = Neg

-- | If-then-else construct
ite :: (SMTType a) => SMTExpr Bool -- ^ If this expression is true
       -> SMTExpr a -- ^ Then return this expression
       -> SMTExpr a -- ^ Else this one
       -> SMTExpr a
ite = ITE

-- | Exclusive or: Return true if exactly one argument is true.
xor :: SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool
xor = XOr

-- | Implication
(.=>.) :: SMTExpr Bool -- ^ If this expression is true
          -> SMTExpr Bool -- ^ This one must be as well
          -> SMTExpr Bool
(.=>.) = Implies

-- | Negates a boolean expression
not' :: SMTExpr Bool -> SMTExpr Bool
not' = Not

-- | Extracts an element of an array by its index
select :: (Args i,SMTType v) => SMTExpr (SMTArray i v) -> i -> SMTExpr v
select = Select

-- | The expression @store arr i v@ stores the value /v/ in the array /arr/ at position /i/ and returns the resulting new array.
store :: (Args i,SMTType v) => SMTExpr (SMTArray i v) -> i -> SMTExpr v -> SMTExpr (SMTArray i v)
store = Store

asArray :: (Args i,SMTType v) => SMTExpr (SMTFun i v) -> SMTExpr (SMTArray i v)
asArray = AsArray

-- | Bitvector addition
bvadd :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvadd = BVAdd

-- | Bitvector subtraction
bvsub :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvsub = BVSub

-- | Bitvector multiplication
bvmul :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvmul = BVMul

-- | Bitvector unsigned remainder
bvurem :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvurem = BVURem

-- | Bitvector signed remainder
bvsrem :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr t
bvsrem = BVSRem

-- | Bitvector unsigned less-or-equal
bvule :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvule = BVULE

-- | Bitvector unsigned less-than
bvult :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvult = BVULT

-- | Bitvector unsigned greater-or-equal
bvuge :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvuge = BVUGE

-- | Bitvector unsigned greater-than
bvugt :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvugt = BVUGT

-- | Bitvector signed less-or-equal
bvsle :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvsle = BVSLE

-- | Bitvector signed less-than
bvslt :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvslt = BVSLT

-- | Bitvector signed greater-or-equal
bvsge :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvsge = BVSGE

-- | Bitvector signed greater-than
bvsgt :: SMTBV t => SMTExpr t -> SMTExpr t -> SMTExpr Bool
bvsgt = BVSGT

-- | Bitvector concat
bvconcat :: (SMTType t1,SMTType t2,Concatable t1 t2,t3 ~ ConcatResult t1 t2,Concatable (SMTAnnotation t1) (SMTAnnotation t2),SMTAnnotation t3 ~ ConcatResult (SMTAnnotation t1) (SMTAnnotation t2))
            => SMTExpr t1 -> SMTExpr t2 -> SMTExpr t3
bvconcat = BVConcat

bvextract :: (SMTType t,Extractable t t) => Integer -> Integer -> SMTExpr t -> SMTExpr t
bvextract u l e = withUndef $ \un -> BVExtract u l (extract' un un u l (extractAnnotation e)) e
    where
      withUndef :: (t -> SMTExpr t) -> SMTExpr t
      withUndef f = f undefined

bvsplitu16to8 :: SMTExpr Word16 -> (SMTExpr Word8,SMTExpr Word8)
bvsplitu16to8 e = (BVExtract 15 8 () e,BVExtract 7 0 () e)

bvsplitu32to16 :: SMTExpr Word32 -> (SMTExpr Word16,SMTExpr Word16)
bvsplitu32to16 e = (BVExtract 31 16 () e,BVExtract 15 0 () e)

bvsplitu32to8 :: SMTExpr Word32 -> (SMTExpr Word8,SMTExpr Word8,SMTExpr Word8,SMTExpr Word8)
bvsplitu32to8 e = (BVExtract 31 24 () e,BVExtract 23 16 () e,BVExtract 15 8 () e,BVExtract 7 0 () e)

bvsplitu64to32 :: SMTExpr Word64 -> (SMTExpr Word32,SMTExpr Word32)
bvsplitu64to32 e = (BVExtract 63 32 () e,BVExtract 31 0 () e)

bvsplitu64to16 :: SMTExpr Word64 -> (SMTExpr Word16,SMTExpr Word16,SMTExpr Word16,SMTExpr Word16)
bvsplitu64to16 e = (BVExtract 63 48 () e,BVExtract 47 32 () e,BVExtract 31 16 () e,BVExtract 15 0 () e)

bvsplitu64to8 :: SMTExpr Word64 -> (SMTExpr Word8,SMTExpr Word8,SMTExpr Word8,SMTExpr Word8,SMTExpr Word8,SMTExpr Word8,SMTExpr Word8,SMTExpr Word8)
bvsplitu64to8 e = (BVExtract 63 56 () e,BVExtract 55 48 () e,BVExtract 47 40 () e,BVExtract 39 32 () e,BVExtract 31 24 () e,BVExtract 23 16 () e,BVExtract 15 8 () e,BVExtract 7 0 () e)

-- | If the supplied function returns true for all possible values, the forall quantification returns true.
forAll :: Args a => (a -> SMTExpr Bool) -> SMTExpr Bool
forAll = Forall

-- | If the supplied function returns true for at least one possible value, the exists quantification returns true.
exists :: Args a => (a -> SMTExpr Bool) -> SMTExpr Bool
exists = Exists

-- | Binds an expression to a variable.
--   Can be used to prevent blowups in the command stream if expressions are used multiple times.
--   @let' x f@ is functionally equivalent to @f x@.
let' :: (SMTType a,SMTAnnotation a ~ ()) => SMTExpr a -> (SMTExpr a -> SMTExpr b) -> SMTExpr b
let' = Let

-- | Like 'let'', but can define multiple variables of the same type.
lets :: SMTType a => [SMTExpr a] -> ([SMTExpr a] -> SMTExpr b) -> SMTExpr b
lets = Lets

-- | Like 'forAll', but can quantify over more than one variable (of the same type)
forAllList :: Args a => Integer -- ^ Number of variables to quantify
              -> ([a] -> SMTExpr Bool) -- ^ Function which takes a list of the quantified variables
              -> SMTExpr Bool
forAllList = ForallList

-- | Checks if the expression is formed a specific constructor.
is :: SMTType a => SMTExpr a -> Constructor a -> SMTExpr Bool
is e con = ConTest con e

-- | Access a field of an expression
(.#) :: (SMTType a,SMTType f) => SMTExpr a -> Field a f -> SMTExpr f
(.#) e f = FieldSel f e

-- | Takes the first element of a list
head' :: SMTExpr [a] -> SMTExpr a
head' = Head

-- | Drops the first element from a list
tail' :: SMTExpr [a] -> SMTExpr [a]
tail' = Tail

-- | Put a new element at the front of the list
insert' :: SMTExpr a -> SMTExpr [a] -> SMTExpr [a]
insert' = Insert

-- | Sets the logic used for the following program (Not needed for many solvers).
setLogic :: Text -> SMT ()
setLogic name = putRequest $ L.List [L.Symbol "set-logic"
                                    ,L.Symbol name]

-- | Given an arbitrary expression, this creates a named version of it and a name to reference it later on.
named :: (SMTType a,SMTAnnotation a ~ ()) => SMTExpr a -> SMT (SMTExpr a,SMTExpr a)
named expr = do
  (c,decl,mp) <- get
  put (c+1,decl,mp)
  let name = T.pack $ "named"++show c
  return (Named expr name,Var name ())

-- | Perform craig interpolation (<http://en.wikipedia.org/wiki/Craig_interpolation>) on the given terms and returns interpolants for them.
--   Note that not all SMT solvers support this.
getInterpolants :: [SMTExpr Bool] -> SMT [SMTExpr Bool]
getInterpolants exprs = do
  (_,_,mp) <- get
  putRequest (L.List (L.Symbol "get-interpolants":fmap (\e -> let (r,_) = exprToLisp e 0 in r) exprs))
  L.List res <- parseResponse
  mapM (lispToExprT () (\name -> mp Map.! name)) res
  
-- | After an unsuccessful 'checkSat' this method extracts a proof from the SMT solver that the instance is unsatisfiable.
getProof :: SMT (SMTExpr Bool)
getProof = do
  (_,_,mp) <- get
  let mp' = Map.union mp commonTheorems
  putRequest (L.List [L.Symbol "get-proof"])
  res <- parseResponse
  lispToExprT () (\name -> case Map.lookup name mp' of
                             Nothing -> error $ "Failed to find a definition for "++show name
                             Just n -> n
                 ) res

commonTheorems :: Map T.Text TypeRep
commonTheorems = Map.fromList
  [(T.pack "|unit-resolution|",typeOf (undefined :: (Bool,Bool,Bool) -> Bool))
  ,(T.pack "|and-elim|",typeOf (undefined :: (Bool,Bool) -> Bool))
  ,(T.pack "asserted",typeOf (undefined :: Bool -> Bool))
  ,(T.pack "monotonicity",typeOf (undefined :: (Bool,Bool) -> Bool))
  ,(T.pack "trans",typeOf (undefined :: (Bool,Bool,Bool) -> Bool))
  ,(T.pack "rewrite",typeOf (undefined :: Bool -> Bool))
  ,(T.pack "mp",typeOf (undefined :: (Bool,Bool,Bool) -> Bool))
  ]