{- | Defines the user-accessible interface of the smtlib2 library -}
{-# LANGUAGE TypeFamilies,OverloadedStrings,FlexibleContexts,ScopedTypeVariables,CPP #-}
module Language.SMTLib2.Internals.Interface where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances (extractAnnotation)
import Language.SMTLib2.Internals.Optimize
import Language.SMTLib2.Internals.Operators
import Language.SMTLib2.Pipe
import Language.SMTLib2.Strategy

import Data.Typeable
import Data.Map as Map hiding (assocs)
import Data.Array
import Data.Unit
import Data.List (genericReplicate)
import Control.Monad.Trans (lift)
import Data.Proxy

-- | Check if the model is satisfiable (e.g. if there is a value for each variable so that every assertion holds)
checkSat :: Monad m => SMT' m Bool
checkSat = smtBackend $ \backend -> do
  lift $ smtCheckSat backend Nothing

-- | Check if the model is satisfiable using a given tactic. (Works only with Z3)
checkSatUsing :: Monad m => Tactic -> SMT' m Bool
checkSatUsing t = smtBackend $ \backend -> do
  lift $ smtCheckSat backend (Just t)

-- | Perform a stacked operation, meaning that every assertion and declaration made in it will be undone after the operation.
stack :: Monad m => SMT' m a -> SMT' m a
stack act = smtBackend $ \backend -> do
  lift $ smtPush backend
  res <- act
  lift $ smtPop backend
  return res

-- | Insert a comment into the SMTLib2 command stream.
--   If you aren't looking at the command stream for debugging, this will do nothing.
comment :: Monad m => String -> SMT' m ()
comment msg = smtBackend $ \backend -> do
  lift $ smtComment backend msg

-- | Create a new named variable
varNamed :: (SMTType t,Typeable t,Unit (SMTAnnotation t),Monad m) => String -> SMT' m (SMTExpr t)
varNamed name = varNamedAnn name unit

-- | Create a named and annotated variable.
varNamedAnn :: (SMTType t,Typeable t,Monad m) => String -> SMTAnnotation t -> SMT' m (SMTExpr t)
varNamedAnn = argVarsAnnNamed

-- | Create a annotated variable
varAnn :: (SMTType t,Typeable t,Monad m) => SMTAnnotation t -> SMT' m (SMTExpr t)
varAnn ann = varNamedAnn "var" ann

-- | Create a fresh new variable
var :: (SMTType t,Typeable t,Unit (SMTAnnotation t),Monad m) => SMT' m (SMTExpr t)
var = varNamed "var"

-- | Like `argVarsAnnNamed`, but defaults the name to "var"
argVarsAnn :: (Args a,Monad m) => ArgAnnotation a -> SMT' m a
argVarsAnn = argVarsAnnNamed "var"

-- | Create annotated named SMT variables of the `Args` class.
--   If more than one variable is needed, they get a numerical suffix.
argVarsAnnNamed :: (Args a,Monad m) => String -> ArgAnnotation a -> SMT' m a
argVarsAnnNamed name ann = do
  st <- getSMT
  let ename = escapeName name
      namec = case Map.lookup name (nameCount st) of
        Nothing -> 0
        Just c -> c
      ((nc,act,mp'),res) = foldExprs
                           (\(cc,act',cmp) u ann'
                            -> let rname = case cc of
                                     0 -> ename
                                     _ -> ename++"_"++show cc
                                   sort = getSort (getUndef u) ann'
                                   resVar = Var rname ann'
                               in ((cc+1,
                                    act' >> (smtBackend $ \backend -> do
                                                declareType (getUndef u) ann'
                                                lift $ smtDeclareFun backend rname [] sort
                                                mapM_ assert $ additionalConstraints (getUndef u) ann' (Var rname ann')),
                                    Map.insert rname (UntypedExpr resVar) cmp
                                   ),
                                   resVar)) (namec,return (),namedExprs st) undefined ann
  putSMT $ st { nameCount = Map.insert name nc (nameCount st)
              , namedExprs = mp' }
  act
  return res

-- | Like `argVarsAnn`, but can only be used for unit type annotations.
argVars :: (Args a,Unit (ArgAnnotation a),Monad m) => SMT' m a
argVars = argVarsAnn unit

-- | A constant expression.
constant :: (SMTValue t,Unit (SMTAnnotation t)) => t -> SMTExpr t
constant x = Const x unit

-- | An annotated constant expression.
constantAnn :: SMTValue t => t -> SMTAnnotation t -> SMTExpr t
constantAnn x ann = Const x ann

getValue :: (SMTValue t,Monad m) => SMTExpr t -> SMT' m t
getValue expr = smtBackend $ \backend -> do
  st <- getSMT
  lift $ smtGetValue backend (namedExprs st) (declaredDataTypes st) expr

-- | Extract all values of an array by giving the range of indices.
unmangleArray :: (Liftable i,LiftArgs i,Ix (Unpacked i),SMTValue v,
                  Unit (ArgAnnotation i),Monad m)
                 => (Unpacked i,Unpacked i)
                 -> SMTExpr (SMTArray i v)
                 -> SMT' m (Array (Unpacked i) v)
unmangleArray b expr = mapM (\i -> do
                                v <- getValue (App SMTSelect (expr,liftArgs i unit))
                                return (i,v)
                            ) (range b) >>= return.array b

-- | Define a new function with a body
defFun :: (Liftable a,SMTType r,Unit (ArgAnnotation a),Unit (SMTAnnotation r),Monad m)
          => (a -> SMTExpr r) -> SMT' m (SMTFunction a r)
defFun = defFunAnn unit unit

-- | Define a new constant.
defConst :: (SMTType r,Monad m) => SMTExpr r -> SMT' m (SMTExpr r)
defConst = defConstNamed "constvar"

-- | Define a new constant with a name
defConstNamed :: (SMTType r,Monad m) => String -> SMTExpr r -> SMT' m (SMTExpr r)
defConstNamed name e = smtBackend $ \backend -> do
  fname <- freeName name
  let ann = extractAnnotation e
  lift $ smtDefineFun backend fname [] {-(getSort (getUndef e) ann)-} e
  return $ Var fname ann

-- | Define a new function with a body and custom type annotations for arguments and result.
defFunAnnNamed :: (Liftable a,SMTType r,Monad m)
                  => String -> ArgAnnotation a -> SMTAnnotation r -> (a -> SMTExpr r) -> SMT' m (SMTFunction a r)
defFunAnnNamed name ann_arg ann_res f = smtBackend $ \backend -> do
  fname <- freeName name
  st <- getSMT
  let c_args = case Map.lookup "arg" (nameCount st) of
        Nothing -> 0
        Just n -> n

      res = SMTFun fname ann_res

      (_,rtp) = getFunUndef res

      (au,tps,c_args') = createArgs ann_arg (c_args+1)
  lift $ smtDefineFun backend fname tps {-(getSort rtp ann_res)-} (f au)
  return res

-- | Like `defFunAnnNamed`, but defaults the function name to "fun".
defFunAnn :: (Liftable a,SMTType r,Monad m)
             => ArgAnnotation a -> SMTAnnotation r -> (a -> SMTExpr r) -> SMT' m (SMTFunction a r)
defFunAnn = defFunAnnNamed "fun"

-- | Boolean conjunction
and' :: SMTFunction [SMTExpr Bool] Bool
and' = SMTLogic And

(.&&.) :: SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool
(.&&.) x y = App (SMTLogic And) [x,y]

-- | Boolean disjunction
or' :: SMTFunction [SMTExpr Bool] Bool
or' = SMTLogic Or

(.||.) :: SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool
(.||.) x y = App (SMTLogic Or) [x,y]

-- | Create a boolean expression that encodes that the array is equal to the supplied constant array.
arrayEquals :: (LiftArgs i,Liftable i,SMTValue v,Ix (Unpacked i),Unit (ArgAnnotation i),Unit (SMTAnnotation v))
               => SMTExpr (SMTArray i v) -> Array (Unpacked i) v -> SMTExpr Bool
arrayEquals expr arr 
  = case [(select expr (liftArgs i unit)) .==. (constant v)
         | (i,v) <- assocs arr ] of
      [] -> constant True
      xs -> foldl1 (.&&.) xs

-- | Asserts that a boolean expression is true
assert :: Monad m => SMTExpr Bool -> SMT' m ()
assert expr = smtBackend $ \backend -> do
  lift $ smtAssert backend expr Nothing

-- | Create a new interpolation group
interpolationGroup :: Monad m => SMT' m InterpolationGroup
interpolationGroup = do
  rname <- freeName "interp"
  return (InterpolationGroup rname)

-- | Assert a boolean expression to be true and assign it to an interpolation group
assertInterp :: Monad m => SMTExpr Bool -> InterpolationGroup -> SMT' m ()
assertInterp expr interp = smtBackend $ \backend -> do
  lift $ smtAssert backend expr (Just interp)

getInterpolant :: Monad m => [InterpolationGroup] -> SMT' m (SMTExpr Bool)
getInterpolant grps = smtBackend $ \backend -> do
  st <- getSMT
  --lift $ smtGetInterpolant backend (namedExprs st) (usedTypes st) grps
  error "TODO: getInterpolant"

-- | Set an option for the underlying SMT solver
setOption :: Monad m => SMTOption -> SMT' m ()
setOption opt = smtBackend $ \backend -> do
  lift $ smtSetOption backend opt

-- | Get information about the underlying SMT solver
getInfo :: Monad m => SMTInfo i -> SMT' m i
getInfo inf = smtBackend $ \backend -> do
  lift $ smtGetInfo backend inf

-- | Create a new uniterpreted function with annotations for
--   the argument and the return type.
funAnn :: (Liftable a,SMTType r,Monad m) => ArgAnnotation a -> SMTAnnotation r -> SMT' m (SMTFunction a r)
funAnn = funAnnNamed "fun"

-- | Create a new uninterpreted named function with annotation for
--   the argument and the return type.
funAnnNamed :: (Liftable a, SMTType r,Monad m) => String -> ArgAnnotation a -> SMTAnnotation r -> SMT' m (SMTFunction a r)
funAnnNamed name annArg annRet = smtBackend $ \backend -> do
  st <- getSMT
  let func = case Map.lookup name (nameCount st) of
        Nothing -> 0
        Just c -> c
  putSMT $ st { nameCount = Map.insert name (func+1) (nameCount st) }
  let rname = (escapeName name)++(case func of
                                     0 -> ""
                                     _ -> "_"++show func)
      res = SMTFun rname annRet
      
      (au,rtp) = getFunUndef res
      
      assertEq :: x -> x -> y -> y
      assertEq _ _ p = p
      
      (au2,tps,_) = createArgs annArg 0
      
  assertEq au au2 $ return ()
  lift $ smtDeclareFun backend rname [ l | (_,l) <- tps ] (getSort rtp annRet)
  return res

-- | funAnn with an annotation only for the return type.
funAnnRet :: (Liftable a,SMTType r,Unit (ArgAnnotation a),Monad m)
             => SMTAnnotation r -> SMT' m (SMTFunction a r)
funAnnRet = funAnn unit

-- | Create a new uninterpreted function.
fun :: (Liftable a,SMTType r,SMTAnnotation r ~ (),Unit (ArgAnnotation a),Monad m)
       => SMT' m (SMTFunction a r)
fun = funAnn unit unit

-- | Apply a function to an argument
app :: (Args arg,SMTType res) => SMTFunction arg res -> arg -> SMTExpr res
app = App

-- | Lift a function to arrays
map' :: (Liftable arg,Args i,SMTType res)
        => SMTFunction arg res -> SMTFunction (Lifted arg i) (SMTArray i res)
map' f = SMTMap f

-- | Two expressions shall be equal
(.==.) :: SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.==.) x y = App SMTEq [x,y]

infix 4 .==.

-- | A generalized version of `.==.`
argEq :: Args a => a -> a -> SMTExpr Bool
argEq xs ys = app and' $
              fst $ foldsExprs
              (\s [(arg1,_),(arg2,_)] -> ((arg1 .==. arg2):s,[arg1,arg2]))
              []
              [(xs,undefined),(ys,undefined)]

-- | Declares all arguments to be distinct
distinct :: SMTType a => [SMTExpr a] -> SMTExpr Bool
distinct = App SMTDistinct

-- | Calculate the sum of arithmetic expressions
plus :: (SMTArith a) => SMTFunction [SMTExpr a] a
plus = SMTArith Plus

-- | Calculate the product of arithmetic expressions
mult :: (SMTArith a) => SMTFunction [SMTExpr a] a
mult = SMTArith Mult

-- | Subtracts two expressions
minus :: (SMTArith a) => SMTFunction (SMTExpr a,SMTExpr a) a
minus = SMTMinus

-- | Divide an arithmetic expression by another
div' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
div' x y = App (SMTIntArith Div) (x,y)

div'' :: SMTFunction (SMTExpr Integer,SMTExpr Integer) Integer
div'' = SMTIntArith Div

-- | Perform a modulo operation on an arithmetic expression
mod' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
mod' x y = App (SMTIntArith Mod) (x,y)

mod'' :: SMTFunction (SMTExpr Integer,SMTExpr Integer) Integer
mod'' = SMTIntArith Mod

-- | Calculate the remainder of the division of two integer expressions
rem' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
rem' x y = App (SMTIntArith Rem) (x,y)

rem'' :: SMTFunction (SMTExpr Integer,SMTExpr Integer) Integer
rem'' = SMTIntArith Rem

-- | Divide a rational expression by another one
divide :: SMTExpr Rational -> SMTExpr Rational -> SMTExpr Rational
divide x y = App SMTDivide (x,y)

divide' :: SMTFunction (SMTExpr Rational,SMTExpr Rational) Rational
divide' = SMTDivide

-- | For an expression @x@, this returns the expression @-x@.
neg :: SMTArith a => SMTFunction (SMTExpr a) a
neg = SMTNeg

-- | Convert an integer expression to a real expression
toReal :: SMTExpr Integer -> SMTExpr Rational
toReal = App SMTToReal

-- | Convert a real expression into an integer expression
toInt :: SMTExpr Rational -> SMTExpr Integer
toInt = App SMTToInt

-- | If-then-else construct
ite :: (SMTType a) => SMTExpr Bool -- ^ If this expression is true
       -> SMTExpr a -- ^ Then return this expression
       -> SMTExpr a -- ^ Else this one
       -> SMTExpr a
ite c l r = App SMTITE (c,l,r)

-- | Exclusive or: Return true if exactly one argument is true.
xor :: SMTFunction [SMTExpr Bool] Bool
xor = SMTLogic XOr

-- | Implication
(.=>.) :: SMTExpr Bool -- ^ If this expression is true
          -> SMTExpr Bool -- ^ This one must be as well
          -> SMTExpr Bool
(.=>.) x y = App (SMTLogic Implies) [x,y]

-- | Negates a boolean expression
not' :: SMTExpr Bool -> SMTExpr Bool
not' = App SMTNot

not'' :: SMTFunction (SMTExpr Bool) Bool
not'' = SMTNot

-- | Extracts an element of an array by its index
select :: (Liftable i,SMTType v) => SMTExpr (SMTArray i v) -> i -> SMTExpr v
select arr i = App SMTSelect (arr,i)

-- | The expression @store arr i v@ stores the value /v/ in the array /arr/ at position /i/ and returns the resulting new array.
store :: (Liftable i,SMTType v) => SMTExpr (SMTArray i v) -> i -> SMTExpr v -> SMTExpr (SMTArray i v)
store arr i v = App SMTStore (arr,i,v)

-- | Interpret a function /f/ from /i/ to /v/ as an array with indices /i/ and elements /v/.
--   Such that: @f \`app\` j .==. select (asArray f) j@ for all indices j.
asArray :: (Args arg,Unit (ArgAnnotation arg),SMTType res)
           => SMTFunction arg res -> SMTExpr (SMTArray arg res)
asArray f = AsArray f unit

-- | Create an array where each element is the same.
constArray :: (Args i,SMTType v) => SMTExpr v -- ^ This element will be at every index of the array
           -> ArgAnnotation i -- ^ Annotations of the index type
           -> SMTExpr (SMTArray i v)
constArray e i_ann = App (SMTConstArray i_ann) e

-- | Bitvector and
bvand :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvand e1 e2 = App (SMTBVBin BVAnd) (e1,e2)

-- | Bitvector or
bvor :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvor e1 e2 = App (SMTBVBin BVOr) (e1,e2)

-- | Bitvector or
bvxor :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvxor e1 e2 = App (SMTBVBin BVXor) (e1,e2)

-- | Bitvector not
bvnot :: (SMTType (BitVector t)) => SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvnot e = App (SMTBVUn BVNot) e

-- | Bitvector signed negation
bvneg :: (SMTType (BitVector t)) => SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvneg e = App (SMTBVUn BVNeg) e

-- | Bitvector addition
bvadd :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvadd e1 e2 = App (SMTBVBin BVAdd) (e1,e2)

-- | Bitvector subtraction
bvsub :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvsub e1 e2 = App (SMTBVBin BVSub) (e1,e2)

-- | Bitvector multiplication
bvmul :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvmul e1 e2 = App (SMTBVBin BVMul) (e1,e2)

-- | Bitvector unsigned remainder
bvurem :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvurem e1 e2 = App (SMTBVBin BVURem) (e1,e2)

-- | Bitvector signed remainder
bvsrem :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvsrem e1 e2 = App (SMTBVBin BVSRem) (e1,e2)

-- | Bitvector unsigned division
bvudiv :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvudiv e1 e2 = App (SMTBVBin BVUDiv) (e1,e2)

-- | Bitvector signed division
bvsdiv :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvsdiv e1 e2 = App (SMTBVBin BVSDiv) (e1,e2)

-- | Bitvector unsigned less-or-equal
bvule :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvule e1 e2 = App (SMTBVComp BVULE) (e1,e2)

-- | Bitvector unsigned less-than
bvult :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvult e1 e2 = App (SMTBVComp BVULT) (e1,e2)

-- | Bitvector unsigned greater-or-equal
bvuge :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvuge e1 e2 = App (SMTBVComp BVUGE) (e1,e2)

-- | Bitvector unsigned greater-than
bvugt :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvugt e1 e2 = App (SMTBVComp BVUGT) (e1,e2)

-- | Bitvector signed less-or-equal
bvsle :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvsle e1 e2 = App (SMTBVComp BVSLE) (e1,e2)

-- | Bitvector signed less-than
bvslt :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvslt e1 e2 = App (SMTBVComp BVSLT) (e1,e2)

-- | Bitvector signed greater-or-equal
bvsge :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvsge e1 e2 = App (SMTBVComp BVSGE) (e1,e2)

-- | Bitvector signed greater-than
bvsgt :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvsgt e1 e2 = App (SMTBVComp BVSGT) (e1,e2)

-- | Bitvector shift left
bvshl :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvshl e1 e2 = App (SMTBVBin BVSHL) (e1,e2)

-- | Bitvector logical right shift
bvlshr :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvlshr e1 e2 = App (SMTBVBin BVLSHR) (e1,e2)

-- | Bitvector arithmetical right shift
bvashr :: (IsBitVector t) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvashr e1 e2 = App (SMTBVBin BVASHR) (e1,e2)

-- | Concats two bitvectors into one.
bvconcat :: (Concatable t1 t2) => SMTExpr (BitVector t1) -> SMTExpr (BitVector t2) -> SMTExpr (BitVector (ConcatResult t1 t2))
bvconcat e1 e2 = App SMTConcat (e1,e2)

-- | Extract a sub-vector out of a given bitvector.
bvextract :: (TypeableNat start,TypeableNat len,Extractable tp len')
             => Proxy start -- ^ The start of the extracted region
             -> Proxy len
             -> SMTExpr (BitVector tp) -- ^ The bitvector to extract from
             -> SMTExpr (BitVector len')
bvextract start len (e::SMTExpr (BitVector tp))
  = App (SMTExtract start len) e

bvextract' :: Integer -> Integer -> SMTExpr (BitVector BVUntyped) -> SMTExpr (BitVector BVUntyped)
bvextract' start len = reifyNat start $
                       \start' -> reifyNat len $ \len' -> bvextract start' len'

-- | Safely split a 16-bit bitvector into two 8-bit bitvectors.
bvsplitu16to8 :: SMTExpr BV16 -> (SMTExpr BV8,SMTExpr BV8)
bvsplitu16to8 e = (App (SMTExtract (Proxy::Proxy N8) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N0) (Proxy::Proxy N8)) e)

-- | Safely split a 32-bit bitvector into two 16-bit bitvectors.
bvsplitu32to16 :: SMTExpr BV32 -> (SMTExpr BV16,SMTExpr BV16)
bvsplitu32to16 e = (App (SMTExtract (Proxy::Proxy N16) (Proxy::Proxy N16)) e,
                    App (SMTExtract (Proxy::Proxy N0) (Proxy::Proxy N16)) e)

-- | Safely split a 32-bit bitvector into four 8-bit bitvectors.
bvsplitu32to8 :: SMTExpr BV32 -> (SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8)
bvsplitu32to8 e = (App (SMTExtract (Proxy::Proxy N24) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N16) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N8) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N0) (Proxy::Proxy N8)) e)

-- | Safely split a 64-bit bitvector into two 32-bit bitvectors.
bvsplitu64to32 :: SMTExpr BV64 -> (SMTExpr BV32,SMTExpr BV32)
bvsplitu64to32 e = (App (SMTExtract (Proxy::Proxy N32) (Proxy::Proxy N32)) e,
                    App (SMTExtract (Proxy::Proxy N0) (Proxy::Proxy N32)) e)

-- | Safely split a 64-bit bitvector into four 16-bit bitvectors.
bvsplitu64to16 :: SMTExpr BV64 -> (SMTExpr BV16,SMTExpr BV16,SMTExpr BV16,SMTExpr BV16)
bvsplitu64to16 e = (App (SMTExtract (Proxy::Proxy N48) (Proxy::Proxy N16)) e,
                    App (SMTExtract (Proxy::Proxy N32) (Proxy::Proxy N16)) e,
                    App (SMTExtract (Proxy::Proxy N16) (Proxy::Proxy N16)) e,
                    App (SMTExtract (Proxy::Proxy N0) (Proxy::Proxy N16)) e)

-- | Safely split a 64-bit bitvector into eight 8-bit bitvectors.
bvsplitu64to8 :: SMTExpr BV64 -> (SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8)
bvsplitu64to8 e = (App (SMTExtract (Proxy::Proxy N56) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N48) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N40) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N32) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N24) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N16) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N8) (Proxy::Proxy N8)) e,
                   App (SMTExtract (Proxy::Proxy N0) (Proxy::Proxy N8)) e)

-- | If the supplied function returns true for all possible values, the forall quantification returns true.
forAll :: (Args a,Unit (ArgAnnotation a)) => (a -> SMTExpr Bool) -> SMTExpr Bool
forAll = Forall unit

-- | An annotated version of `forAll`.
forAllAnn :: Args a => ArgAnnotation a -> (a -> SMTExpr Bool) -> SMTExpr Bool
forAllAnn = Forall

-- | If the supplied function returns true for at least one possible value, the exists quantification returns true.
exists :: (Args a,Unit (ArgAnnotation a)) => (a -> SMTExpr Bool) -> SMTExpr Bool
exists = Exists unit

-- | An annotated version of `exists`.
existsAnn :: Args a => ArgAnnotation a -> (a -> SMTExpr Bool) -> SMTExpr Bool
existsAnn = Exists

-- | Binds an expression to a variable.
--   Can be used to prevent blowups in the command stream if expressions are used multiple times.
--   @let' x f@ is functionally equivalent to @f x@.
let' :: (Args a,Unit (ArgAnnotation a)) => a -> (a -> SMTExpr b) -> SMTExpr b
let' = Let unit

-- | Like `let'`, but can be given an additional type annotation for the argument of the function.
letAnn :: Args a => ArgAnnotation a -> a -> (a -> SMTExpr b) -> SMTExpr b
letAnn = Let

-- | Like 'let'', but can define multiple variables of the same type.
lets :: (Args a,Unit (ArgAnnotation a)) => [a] -> ([a] -> SMTExpr b) -> SMTExpr b
lets xs = Let (fmap (const unit) xs) xs

-- | Like 'forAll', but can quantify over more than one variable (of the same type).
forAllList :: (Args a,Unit (ArgAnnotation a)) => Integer -- ^ Number of variables to quantify
              -> ([a] -> SMTExpr Bool) -- ^ Function which takes a list of the quantified variables
              -> SMTExpr Bool
forAllList l = Forall (genericReplicate l unit)

-- | Like `exists`, but can quantify over more than one variable (of the same type).
existsList :: (Args a,Unit (ArgAnnotation a)) => Integer -- ^ Number of variables to quantify
           -> ([a] -> SMTExpr Bool) -- ^ Function which takes a list of the quantified variables
           -> SMTExpr Bool
existsList l = Exists (genericReplicate l unit)


-- | Checks if the expression is formed a specific constructor.
is :: (Args arg,SMTType dt) => SMTExpr dt -> Constructor arg dt -> SMTExpr Bool
is e con = App (SMTConTest con) e

-- | Access a field of an expression
(.#) :: (SMTRecordType a,SMTType f) => SMTExpr a -> Field a f -> SMTExpr f
(.#) e f = App (SMTFieldSel f) e

-- | Takes the first element of a list
head' :: (SMTType a,Unit (SMTAnnotation a)) => SMTExpr [a] -> SMTExpr a
head' = App (SMTFun "head" unit)

-- | Drops the first element from a list
tail' :: (SMTType a,Unit (SMTAnnotation a)) => SMTExpr [a] -> SMTExpr [a]
tail' = App (SMTFun "tail" unit)

-- | Put a new element at the front of the list
insert' :: (SMTType a,Unit (SMTAnnotation a)) => SMTExpr a -> SMTExpr [a] -> SMTExpr [a]
insert' = curry (App (SMTFun "insert" unit))

-- | Checks if a list is empty.
isNil :: (SMTType a) => SMTExpr [a] -> SMTExpr Bool
isNil e = is e (Constructor "nil" :: Constructor () [a])

-- | Checks if a list is non-empty.
isInsert :: (SMTType a,Unit (SMTAnnotation a)) => SMTExpr [a] -> SMTExpr Bool
isInsert e = is e (Constructor "insert" :: Constructor (SMTExpr a,SMTExpr [a]) [a])

-- | Sets the logic used for the following program (Not needed for many solvers).
setLogic :: Monad m => String -> SMT' m ()
setLogic name = smtBackend $ \backend -> do
  lift $ smtSetLogic backend name

-- | Given an arbitrary expression, this creates a named version of it and a name to reference it later on.
named :: (SMTType a,SMTAnnotation a ~ (),Monad m)
         => String -> SMTExpr a -> SMT' m (SMTExpr a,SMTExpr a)
named name expr = do
  rname <- freeName name
  return (Named expr rname,Var rname ())

-- | Like `named`, but defaults the name to "named".
named' :: (SMTType a,SMTAnnotation a ~ (),Monad m)
          => SMTExpr a -> SMT' m (SMTExpr a,SMTExpr a)
named' = named "named"
  
-- | After an unsuccessful 'checkSat' this method extracts a proof from the SMT solver that the instance is unsatisfiable.
getProof :: Monad m => SMT' m (SMTExpr Bool)
getProof = smtBackend $ \backend -> do
  st <- getSMT
  lift $ smtGetProof backend (namedExprs st) (declaredDataTypes st)

-- | Use the SMT solver to simplify a given expression.
--   Currently only works with Z3.
simplify :: (SMTType t,Monad m) => SMTExpr t -> SMT' m (SMTExpr t)
simplify expr = smtBackend $ \backend -> do
  st <- getSMT
  lift $ smtSimplify backend (namedExprs st) (declaredDataTypes st) expr

-- | After an unsuccessful 'checkSat', return a list of names of named
--   expression which make the instance unsatisfiable.
getUnsatCore :: Monad m => SMT' m [String]
getUnsatCore = smtBackend $ \backend -> do
  lift $ smtGetUnsatCore backend
  
optimizeExpr' :: SMTExpr a -> SMTExpr a
optimizeExpr' e = case optimizeExpr e of
  Nothing -> e
  Just e' -> e'

instance Show (SMTExpr t) where
  show expr = show $ fst $ exprToLisp expr 0
