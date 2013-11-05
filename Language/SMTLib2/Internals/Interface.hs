{- | Defines the user-accessible interface of the smtlib2 library -}
{-# LANGUAGE TypeFamilies,OverloadedStrings,FlexibleContexts,ScopedTypeVariables,CPP #-}
module Language.SMTLib2.Internals.Interface where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Instances (extractAnnotation)
import Language.SMTLib2.Internals.Translation
import Language.SMTLib2.Functions

import Data.Typeable
import Data.Text as T hiding (foldl1)
import Data.Map as Map hiding (assocs)
import Data.Array
import qualified Data.AttoLisp as L
import Data.Unit
import Data.List (genericReplicate)
import Data.Monoid
import Control.Monad.Trans (MonadIO)
#ifdef SMTLIB2_WITH_DATAKINDS
import Data.Proxy
#endif

-- | Create a new named variable
varNamed :: (SMTType t,Typeable t,Unit (SMTAnnotation t),MonadIO m) => String -> SMT' m (SMTExpr t)
varNamed name = varNamedAnn name unit

-- | Create a named and annotated variable.
varNamedAnn :: (SMTType t,Typeable t,MonadIO m) => String -> SMTAnnotation t -> SMT' m (SMTExpr t)
varNamedAnn = argVarsAnnNamed

-- | Create a annotated variable
varAnn :: (SMTType t,Typeable t,MonadIO m) => SMTAnnotation t -> SMT' m (SMTExpr t)
varAnn ann = varNamedAnn "var" ann

-- | Create a fresh new variable
var :: (SMTType t,Typeable t,Unit (SMTAnnotation t),MonadIO m) => SMT' m (SMTExpr t)
var = varNamed "var"

-- | Like `argVarsAnnNamed`, but defaults the name to "var"
argVarsAnn :: (Args a,MonadIO m) => ArgAnnotation a -> SMT' m a
argVarsAnn = argVarsAnnNamed "var"

-- | Create annotated named SMT variables of the `Args` class.
--   If more than one variable is needed, they get a numerical suffix.
argVarsAnnNamed :: (Args a,MonadIO m) => String -> ArgAnnotation a -> SMT' m a
argVarsAnnNamed name ann = do
  (names,decl,mp) <- getSMT
  let ename = escapeName name
      namec = case Map.lookup name names of
        Nothing -> 0
        Just c -> c
      ((nc,act,mp'),res) = foldExprs
                           (\(cc,act',cmp) u ann'
                            -> let rname = T.pack $ case cc of
                                     0 -> ename
                                     _ -> ename++"_"++show cc
                                   sort = getSort (getUndef u) ann'
                                   resVar = Var rname ann'
                               in ((cc+1,
                                    act' >> (do
                                                declareType (getUndef u) ann'
                                                declareFun rname [] sort
                                                mapM_ assert $ additionalConstraints (getUndef u) ann' (Var rname ann')),
                                    Map.insert rname (UntypedExpr resVar) cmp
                                   ),
                                   resVar)) (namec,return (),mp) undefined ann
  putSMT (Map.insert name nc names,decl,mp')
  act
  return res

-- | Like `argVarsAnn`, but can only be used for unit type annotations.
argVars :: (Args a,Unit (ArgAnnotation a),MonadIO m) => SMT' m a
argVars = argVarsAnn unit

-- | A constant expression.
constant :: (SMTValue t,Unit (SMTAnnotation t)) => t -> SMTExpr t
constant x = Const x unit

-- | An annotated constant expression.
constantAnn :: SMTValue t => t -> SMTAnnotation t -> SMTExpr t
constantAnn x ann = Const x ann

-- | Boolean conjunction
and' :: SMTLogic
and' = And

(.&&.) :: SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool
(.&&.) x y = App And [x,y]

-- | Boolean disjunction
or' :: SMTLogic
or' = Or

(.||.) :: SMTExpr Bool -> SMTExpr Bool -> SMTExpr Bool
(.||.) x y = App Or [x,y]

-- | Create a boolean expression that encodes that the array is equal to the supplied constant array.
arrayEquals :: (LiftArgs i,Liftable i,SMTValue v,Ix (Unpacked i),Unit (ArgAnnotation i),Unit (SMTAnnotation v))
               => SMTExpr (SMTArray i v) -> Array (Unpacked i) v -> SMTExpr Bool
arrayEquals expr arr 
  = case [(select expr (liftArgs i unit)) .==. (constant v)
         | (i,v) <- assocs arr ] of
      [] -> constant True
      xs -> foldl1 (.&&.) xs

-- | Asserts that a boolean expression is true
assert :: MonadIO m => SMTExpr Bool -> SMT' m ()
assert expr = putRequest $ L.List [L.Symbol "assert"
                                  ,L.toLisp expr]

-- | Create a new interpolation group
interpolationGroup :: Monad m => SMT' m InterpolationGroup
interpolationGroup = do
  rname <- freeName "interp"
  return (InterpolationGroup rname)

-- | Assert a boolean expression to be true and assign it to an interpolation group
assertInterp :: MonadIO m => SMTExpr Bool -> InterpolationGroup -> SMT' m ()
assertInterp expr (InterpolationGroup g)
  = putRequest $ L.List [L.Symbol "assert"
                        ,L.List [L.Symbol "!"
                                ,L.toLisp expr
                                ,L.Symbol ":interpolation-group"
                                ,L.Symbol g]]

getInterpolant :: MonadIO m => [InterpolationGroup] -> SMT' m (SMTExpr Bool)
getInterpolant grps = do
  putRequest $ L.List [L.Symbol "get-interpolant"
                      ,L.List [ L.Symbol g | InterpolationGroup g <- grps ]
                      ]
  val <- parseResponse
  (_,tps,mp) <- getSMT
  sort_parser <- getSortParser
  case lispToExpr commonFunctions sort_parser
       (\n -> Map.lookup n mp) tps gcast (Just $ toSort (undefined::Bool) ()) val of
    Just (Just x) -> return x
    _ -> error $ "smtlib2: Failed to parse get-interpolant result: "++show val


-- | Set an option for the underlying SMT solver
setOption :: MonadIO m => SMTOption -> SMT' m ()
setOption opt = putRequest $ L.List $ [L.Symbol "set-option"]
                ++(case opt of
                      PrintSuccess v -> [L.Symbol ":print-success"
                                        ,L.Symbol $ if v then "true" else "false"]
                      ProduceModels v -> [L.Symbol ":produce-models"
                                         ,L.Symbol $ if v then "true" else "false"]
                      ProduceProofs v -> [L.Symbol ":produce-proofs"
                                         ,L.Symbol $ if v then "true" else "false"]
                      ProduceUnsatCores v -> [L.Symbol ":produce-unsat-cores"
                                             ,L.Symbol $ if v then "true" else "false"]
                      ProduceInterpolants v -> [L.Symbol ":produce-interpolants"
                                               ,L.Symbol $ if v then "true" else "false"]
                  )

-- | Create a new uniterpreted function with annotations for
--   the argument and the return type.
funAnn :: (Liftable a, SMTType r,MonadIO m) => ArgAnnotation a -> SMTAnnotation r -> SMT' m (SMTFun a r)
funAnn = funAnnNamed "fun"

-- | Create a new uninterpreted named function with annotation for
--   the argument and the return type.
funAnnNamed :: (Liftable a, SMTType r,MonadIO m) => String -> ArgAnnotation a -> SMTAnnotation r -> SMT' m (SMTFun a r)
funAnnNamed name annArg annRet = do
  (names,decl,mp) <- getSMT
  let func = case Map.lookup name names of
        Nothing -> 0
        Just c -> c
  putSMT (Map.insert name (func+1) names,decl,mp)
  let rname = T.pack $ (escapeName name)++(case func of
                                              0 -> ""
                                              _ -> "_"++show func)
      res = SMTFun rname annRet
      
      (au,rtp) = getFunUndef res
      
      assertEq :: x -> x -> y -> y
      assertEq _ _ p = p
      
      (au2,tps,_) = createArgs annArg 0
      
  assertEq au au2 $ return ()
  declareFun rname [ l | (_,l) <- tps ] (getSort rtp annRet)
  return res

-- | funAnn with an annotation only for the return type.
funAnnRet :: (Liftable a, SMTType r, Unit (ArgAnnotation a), MonadIO m) => SMTAnnotation r -> SMT' m (SMTFun a r)
funAnnRet = funAnn unit

-- | Create a new uninterpreted function.
fun :: (Liftable a,SMTType r,SMTAnnotation r ~ (),Unit (ArgAnnotation a),MonadIO m) => SMT' m (SMTFun a r)
fun = funAnn unit unit

-- | Apply a function to an argument
app :: (SMTFunction f) => f -> SMTFunArg f -> SMTExpr (SMTFunRes f)
app = App

-- | Lift a function to arrays
map' :: (SMTFunction f,Liftable (SMTFunArg f)) 
        => f -> SMTMap f i (Lifted (SMTFunArg f) i)
map' f = SMTMap f

-- | Two expressions shall be equal
(.==.) :: SMTType a => SMTExpr a -> SMTExpr a -> SMTExpr Bool
(.==.) x y = App Eq [x,y]

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
distinct = App Distinct

-- | Calculate the sum of arithmetic expressions
plus :: (SMTArith a) => SMTArithOp a
plus = Plus

-- | Calculate the product of arithmetic expressions
mult :: (SMTArith a) => SMTArithOp a
mult = Mult

-- | Subtracts two expressions
minus :: (SMTArith a) => SMTMinus a
minus = Minus

-- | Divide an arithmetic expression by another
div' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
div' x y = App Div (x,y)

div'' :: SMTIntArith
div'' = Div

-- | Perform a modulo operation on an arithmetic expression
mod' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
mod' x y = App Mod (x,y)

mod'' :: SMTIntArith
mod'' = Mod

-- | Calculate the remainder of the division of two integer expressions
rem' :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Integer
rem' x y = App Rem (x,y)

rem'' :: SMTIntArith
rem'' = Rem

-- | Divide a rational expression by another one
divide :: SMTExpr Rational -> SMTExpr Rational -> SMTExpr Rational
divide x y = App Divide (x,y)

divide' :: SMTDivide
divide' = Divide

-- | For an expression @x@, this returns the expression @-x@.
neg :: SMTArith a => SMTNeg a
neg = Neg

-- | Convert an integer expression to a real expression
toReal :: SMTExpr Integer -> SMTExpr Rational
toReal = App ToReal

-- | Convert a real expression into an integer expression
toInt :: SMTExpr Rational -> SMTExpr Integer
toInt = App ToInt

-- | If-then-else construct
ite :: (SMTType a) => SMTExpr Bool -- ^ If this expression is true
       -> SMTExpr a -- ^ Then return this expression
       -> SMTExpr a -- ^ Else this one
       -> SMTExpr a
ite c l r = App ITE (c,l,r)

-- | Exclusive or: Return true if exactly one argument is true.
xor :: SMTLogic
xor = XOr

-- | Implication
(.=>.) :: SMTExpr Bool -- ^ If this expression is true
          -> SMTExpr Bool -- ^ This one must be as well
          -> SMTExpr Bool
(.=>.) x y = App Implies [x,y]

-- | Negates a boolean expression
not' :: SMTExpr Bool -> SMTExpr Bool
not' = App Not

not'' :: SMTNot
not'' = Not

-- | Extracts an element of an array by its index
select :: (Liftable i,SMTType v) => SMTExpr (SMTArray i v) -> i -> SMTExpr v
select arr i = App Select (arr,i)

-- | The expression @store arr i v@ stores the value /v/ in the array /arr/ at position /i/ and returns the resulting new array.
store :: (Liftable i,SMTType v) => SMTExpr (SMTArray i v) -> i -> SMTExpr v -> SMTExpr (SMTArray i v)
store arr i v = App Store (arr,i,v)

-- | Interpret a function /f/ from /i/ to /v/ as an array with indices /i/ and elements /v/.
--   Such that: @f \`app\` j .==. select (asArray f) j@ for all indices j.
asArray :: (SMTFunction f,Unit (ArgAnnotation (SMTFunArg f))) 
           => f -> SMTExpr (SMTArray (SMTFunArg f) (SMTFunRes f))
asArray f = AsArray f unit

-- | Create an array where each element is the same.
constArray :: (Args i,SMTType v) => SMTExpr v -- ^ This element will be at every index of the array
           -> ArgAnnotation i -- ^ Annotations of the index type
           -> SMTExpr (SMTArray i v)
constArray e i_ann = App (ConstArray i_ann) e

-- | Bitvector and
bvand :: (SMTFunction (SMTBVBinOp t),
          SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVBinOp t) ~ BitVector t
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvand (e1::SMTExpr (BitVector t)) e2 = App (BVAnd::SMTBVBinOp t) (e1,e2)

-- | Bitvector or
bvor :: (SMTFunction (SMTBVBinOp t),
         SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
         SMTFunRes (SMTBVBinOp t) ~ BitVector t
        ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvor (e1::SMTExpr (BitVector t)) e2 = App (BVOr::SMTBVBinOp t) (e1,e2)

-- | Bitvector or
bvxor :: (SMTFunction (SMTBVBinOp t),
         SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
         SMTFunRes (SMTBVBinOp t) ~ BitVector t
        ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvxor (e1::SMTExpr (BitVector t)) e2 = App (BVXor::SMTBVBinOp t) (e1,e2)

-- | Bitvector not
bvnot :: (SMTFunction (SMTBVUnOp t), 
          SMTFunArg (SMTBVUnOp t) ~ SMTExpr (BitVector t),
          SMTFunRes (SMTBVUnOp t) ~ BitVector t
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvnot (e::SMTExpr (BitVector t)) = App (BVNot::SMTBVUnOp t) e

-- | Bitvector signed negation
bvneg :: (SMTFunction (SMTBVUnOp t),
          SMTFunArg (SMTBVUnOp t) ~ SMTExpr (BitVector t),
          SMTFunRes (SMTBVUnOp t) ~ BitVector t
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvneg (e::SMTExpr (BitVector t)) = App (BVNeg::SMTBVUnOp t) e

-- | Bitvector addition
bvadd :: (SMTFunction (SMTBVBinOp t),
         SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
         SMTFunRes (SMTBVBinOp t) ~ BitVector t
        ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvadd (e1::SMTExpr (BitVector t)) e2 = App (BVAdd::SMTBVBinOp t) (e1,e2)

-- | Bitvector subtraction
bvsub :: (SMTFunction (SMTBVBinOp t),
         SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
         SMTFunRes (SMTBVBinOp t) ~ BitVector t
        ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvsub (e1::SMTExpr (BitVector t)) e2 = App (BVSub::SMTBVBinOp t) (e1,e2)

-- | Bitvector multiplication
bvmul :: (SMTFunction (SMTBVBinOp t),
         SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
         SMTFunRes (SMTBVBinOp t) ~ BitVector t
        ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvmul (e1::SMTExpr (BitVector t)) e2 = App (BVMul::SMTBVBinOp t) (e1,e2)

-- | Bitvector unsigned remainder
bvurem :: (SMTFunction (SMTBVBinOp t),
           SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
           SMTFunRes (SMTBVBinOp t) ~ BitVector t
          ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvurem (e1::SMTExpr (BitVector t)) e2 = App (BVURem::SMTBVBinOp t) (e1,e2)

-- | Bitvector signed remainder
bvsrem :: (SMTFunction (SMTBVBinOp t),
           SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
           SMTFunRes (SMTBVBinOp t) ~ BitVector t
          ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvsrem (e1::SMTExpr (BitVector t)) e2 = App (BVSRem::SMTBVBinOp t) (e1,e2)

-- | Bitvector unsigned division
bvudiv :: (SMTFunction (SMTBVBinOp t),
           SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
           SMTFunRes (SMTBVBinOp t) ~ BitVector t
          ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvudiv (e1::SMTExpr (BitVector t)) e2 = App (BVUDiv::SMTBVBinOp t) (e1,e2)

-- | Bitvector signed division
bvsdiv :: (SMTFunction (SMTBVBinOp t),
           SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
           SMTFunRes (SMTBVBinOp t) ~ BitVector t
          ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvsdiv (e1::SMTExpr (BitVector t)) e2 = App (BVSDiv::SMTBVBinOp t) (e1,e2)

-- | Bitvector unsigned less-or-equal
bvule :: (SMTFunction (SMTBVComp t), 
          SMTFunArg (SMTBVComp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVComp t) ~ Bool
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvule (e1::SMTExpr (BitVector t)) e2 = App (BVULE::SMTBVComp t) (e1,e2)

-- | Bitvector unsigned less-than
bvult :: (SMTFunction (SMTBVComp t), 
          SMTFunArg (SMTBVComp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVComp t) ~ Bool
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvult (e1::SMTExpr (BitVector t)) e2 = App (BVULT::SMTBVComp t) (e1,e2)

-- | Bitvector unsigned greater-or-equal
bvuge :: (SMTFunction (SMTBVComp t), 
          SMTFunArg (SMTBVComp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVComp t) ~ Bool
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvuge (e1::SMTExpr (BitVector t)) e2 = App (BVUGE::SMTBVComp t) (e1,e2)

-- | Bitvector unsigned greater-than
bvugt :: (SMTFunction (SMTBVComp t), 
          SMTFunArg (SMTBVComp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVComp t) ~ Bool
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvugt (e1::SMTExpr (BitVector t)) e2 = App (BVUGT::SMTBVComp t) (e1,e2)

-- | Bitvector signed less-or-equal
bvsle :: (SMTFunction (SMTBVComp t), 
          SMTFunArg (SMTBVComp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVComp t) ~ Bool
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvsle (e1::SMTExpr (BitVector t)) e2 = App (BVSLE::SMTBVComp t) (e1,e2)

-- | Bitvector signed less-than
bvslt :: (SMTFunction (SMTBVComp t), 
          SMTFunArg (SMTBVComp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVComp t) ~ Bool
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvslt (e1::SMTExpr (BitVector t)) e2 = App (BVSLT::SMTBVComp t) (e1,e2)

-- | Bitvector signed greater-or-equal
bvsge :: (SMTFunction (SMTBVComp t), 
          SMTFunArg (SMTBVComp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVComp t) ~ Bool
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvsge (e1::SMTExpr (BitVector t)) e2 = App (BVSGE::SMTBVComp t) (e1,e2)

-- | Bitvector signed greater-than
bvsgt :: (SMTFunction (SMTBVComp t), 
          SMTFunArg (SMTBVComp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVComp t) ~ Bool
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr Bool
bvsgt (e1::SMTExpr (BitVector t)) e2 = App (BVSGT::SMTBVComp t) (e1,e2)

-- | Bitvector shift left
bvshl :: (SMTFunction (SMTBVBinOp t),
          SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
          SMTFunRes (SMTBVBinOp t) ~ BitVector t
         ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvshl (e1::SMTExpr (BitVector t)) e2 = App (BVSHL::SMTBVBinOp t) (e1,e2)

-- | Bitvector logical right shift
bvlshr :: (SMTFunction (SMTBVBinOp t),
           SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
           SMTFunRes (SMTBVBinOp t) ~ BitVector t
          ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvlshr (e1::SMTExpr (BitVector t)) e2 = App (BVLSHR::SMTBVBinOp t) (e1,e2)

-- | Bitvector arithmetical right shift
bvashr :: (SMTFunction (SMTBVBinOp t),
           SMTFunArg (SMTBVBinOp t) ~ (SMTExpr (BitVector t),SMTExpr (BitVector t)),
           SMTFunRes (SMTBVBinOp t) ~ BitVector t
          ) => SMTExpr (BitVector t) -> SMTExpr (BitVector t) -> SMTExpr (BitVector t)
bvashr (e1::SMTExpr (BitVector t)) e2 = App (BVASHR::SMTBVBinOp t) (e1,e2)

-- | Concats two bitvectors into one.
bvconcat :: (SMTFunction (SMTConcat t1 t2)
            ,SMTFunArg (SMTConcat t1 t2) ~ (SMTExpr (BitVector t1),SMTExpr (BitVector t2))
            ,SMTFunRes (SMTConcat t1 t2) ~ BitVector t3
            ) => SMTExpr (BitVector t1) -> SMTExpr (BitVector t2) -> SMTExpr (BitVector t3)
bvconcat (e1::SMTExpr (BitVector t1)) (e2::SMTExpr (BitVector t2)) = App (BVConcat::SMTConcat t1 t2) (e1,e2)

-- | Extract a sub-vector out of a given bitvector.
#ifdef SMTLIB2_WITH_DATAKINDS
bvextract :: (SMTFunction (SMTExtract tp start len)
             ,SMTFunArg (SMTExtract tp start len) ~ SMTExpr (BitVector tp)
             ,SMTFunRes (SMTExtract tp start len) ~ BitVector r
             )
             => Proxy start -- ^ The start of the extracted region
             -> Proxy len -- ^ The length of the extracted region
             -> SMTExpr (BitVector tp) -- ^ The bitvector to extract from
             -> SMTExpr (BitVector r)
bvextract (_::Proxy start) (_::Proxy len) (e::SMTExpr (BitVector tp))
  = App (BVExtract::SMTExtract tp start len) e
#else
bvextract :: (SMTFunction (SMTExtract tp start len)
             ,SMTFunArg (SMTExtract tp start len) ~ SMTExpr (BitVector tp)
             ,SMTFunRes (SMTExtract tp start len) ~ BitVector r
             )
             => start -- ^ The start of the extracted region
             -> len -- ^ The length of the extracted region
             -> SMTExpr (BitVector tp) -- ^ The bitvector to extract from
             -> SMTExpr (BitVector r)
bvextract (_::start) (_::len) (e::SMTExpr (BitVector tp))
  = App (BVExtract::SMTExtract tp start len) e
#endif

bvextract' :: Integer -> Integer -> SMTExpr (BitVector BVUntyped) -> SMTExpr (BitVector BVUntyped)
bvextract' start len = reifyNat start $
                       \start' -> reifyNat len $ \len' -> bvextract start' len'

-- | Safely split a 16-bit bitvector into two 8-bit bitvectors.
bvsplitu16to8 :: SMTExpr BV16 -> (SMTExpr BV8,SMTExpr BV8)
bvsplitu16to8 e = (App (BVExtract::SMTExtract (BVTyped N16) N8 N8) e,
                   App (BVExtract::SMTExtract (BVTyped N16) N0 N8) e)

-- | Safely split a 32-bit bitvector into two 16-bit bitvectors.
bvsplitu32to16 :: SMTExpr BV32 -> (SMTExpr BV16,SMTExpr BV16)
bvsplitu32to16 e = (App (BVExtract::SMTExtract (BVTyped N32) N16 N16) e,
                    App (BVExtract::SMTExtract (BVTyped N32) N0  N16) e)

-- | Safely split a 32-bit bitvector into four 8-bit bitvectors.
bvsplitu32to8 :: SMTExpr BV32 -> (SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8)
bvsplitu32to8 e = (App (BVExtract::SMTExtract (BVTyped N32) N24 N8) e,
                   App (BVExtract::SMTExtract (BVTyped N32) N16 N8) e,
                   App (BVExtract::SMTExtract (BVTyped N32) N8  N8) e,
                   App (BVExtract::SMTExtract (BVTyped N32) N0  N8) e)

-- | Safely split a 64-bit bitvector into two 32-bit bitvectors.
bvsplitu64to32 :: SMTExpr BV64 -> (SMTExpr BV32,SMTExpr BV32)
bvsplitu64to32 e = (App (BVExtract::SMTExtract (BVTyped N64) N32 N32) e,
                    App (BVExtract::SMTExtract (BVTyped N64) N0  N32) e)

-- | Safely split a 64-bit bitvector into four 16-bit bitvectors.
bvsplitu64to16 :: SMTExpr BV64 -> (SMTExpr BV16,SMTExpr BV16,SMTExpr BV16,SMTExpr BV16)
bvsplitu64to16 e = (App (BVExtract::SMTExtract (BVTyped N64) N48 N16) e,
                    App (BVExtract::SMTExtract (BVTyped N64) N32 N16) e,
                    App (BVExtract::SMTExtract (BVTyped N64) N16 N16) e,
                    App (BVExtract::SMTExtract (BVTyped N64) N0  N16) e)

-- | Safely split a 64-bit bitvector into eight 8-bit bitvectors.
bvsplitu64to8 :: SMTExpr BV64 -> (SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8,SMTExpr BV8)
bvsplitu64to8 e = (App (BVExtract::SMTExtract (BVTyped N64) N56 N8) e,
                   App (BVExtract::SMTExtract (BVTyped N64) N48 N8) e,
                   App (BVExtract::SMTExtract (BVTyped N64) N40 N8) e,
                   App (BVExtract::SMTExtract (BVTyped N64) N32 N8) e,
                   App (BVExtract::SMTExtract (BVTyped N64) N24 N8) e,
                   App (BVExtract::SMTExtract (BVTyped N64) N16 N8) e,
                   App (BVExtract::SMTExtract (BVTyped N64) N8  N8) e,
                   App (BVExtract::SMTExtract (BVTyped N64) N0  N8) e)

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
is :: SMTType a => SMTExpr a -> Constructor a -> SMTExpr Bool
is e con = App (ConTest con) e

-- | Access a field of an expression
(.#) :: (SMTRecordType a,SMTType f) => SMTExpr a -> Field a f -> SMTExpr f
(.#) e f = App (FieldSel f) e

-- | Takes the first element of a list
head' :: SMTType a => SMTExpr [a] -> SMTExpr a
head' = App Head

-- | Drops the first element from a list
tail' :: SMTType a => SMTExpr [a] -> SMTExpr [a]
tail' = App Tail

-- | Put a new element at the front of the list
insert' :: SMTType a => SMTExpr a -> SMTExpr [a] -> SMTExpr [a]
insert' = curry (App Insert)

-- | Checks if a list is empty.
isNil :: SMTType a => SMTExpr [a] -> SMTExpr Bool
isNil e = is e (Constructor "nil")

-- | Checks if a list is non-empty.
isInsert :: SMTType a => SMTExpr [a] -> SMTExpr Bool
isInsert e = is e (Constructor "insert")

-- | Sets the logic used for the following program (Not needed for many solvers).
setLogic :: MonadIO m => Text -> SMT' m ()
setLogic name = putRequest $ L.List [L.Symbol "set-logic"
                                    ,L.Symbol name]

-- | Given an arbitrary expression, this creates a named version of it and a name to reference it later on.
named :: (SMTType a,SMTAnnotation a ~ (),MonadIO m) => String -> SMTExpr a -> SMT' m (SMTExpr a,SMTExpr a)
named name expr = do
  rname <- freeName name
  return (Named expr rname,Var rname ())

-- | Like `named`, but defaults the name to "named".
named' :: (SMTType a,SMTAnnotation a ~ (),MonadIO m) => SMTExpr a -> SMT' m (SMTExpr a,SMTExpr a)
named' = named "named"
  
-- | After an unsuccessful 'checkSat' this method extracts a proof from the SMT solver that the instance is unsatisfiable.
getProof :: MonadIO m => SMT' m (SMTExpr Bool)
getProof = do
  (_,tps,mp) <- getSMT
  sort_parser <- getSortParser
  putRequest (L.List [L.Symbol "get-proof"])
  res <- parseResponse
  let proof = case res of
        L.List items -> case findProof items of
          Nothing -> res
          Just p -> p
        _ -> res
  case lispToExpr (commonFunctions `mappend` commonTheorems) sort_parser
       (\n -> Map.lookup n mp) tps gcast (Just $ toSort (undefined::Bool) ()) proof of
    Just (Just x) -> return x
    _ -> error $ "smtlib2: Couldn't parse proof "++show res
  where
    findProof [] = Nothing
    findProof ((L.List [L.Symbol "proof",proof]):_) = Just proof
    findProof (x:xs) = findProof xs

-- | Use the SMT solver to simplify a given expression.
--   Currently only works with Z3.
simplify :: (SMTType t,MonadIO m) => SMTExpr t -> SMT' m (SMTExpr t)
simplify (expr::SMTExpr t) = do
  clearInput
  putRequest $ L.List [L.Symbol "simplify"
                      ,L.toLisp expr]
  val <- parseResponse
  (_,tps,mp) <- getSMT
  sort_parser <- getSortParser
  case lispToExpr commonFunctions sort_parser
       (\n -> Map.lookup n mp) tps gcast (Just $ toSort (undefined::t) (extractAnnotation expr)) val of
    Just (Just x) -> return x
    _ -> error $ "smtlib2: Failed to parse simplify result: "++show val

-- | After an unsuccessful 'checkSat', return a list of names of named
--   expression which make the instance unsatisfiable.
getUnsatCore :: MonadIO m => SMT' m [String]
getUnsatCore = do
  putRequest (L.List [L.Symbol "get-unsat-core"])
  res <- parseResponse
  case res of
    L.List names -> return $
                    fmap (\name -> case name of
                             L.Symbol s -> T.unpack s
                             _ -> error $ "Language.SMTLib2.getUnsatCore: Unknown expression "
                                  ++show name++" in core list."
                         ) names
    _ -> error $ "Language.SMTLib2.getUnsatCore: Unknown response "++show res++" to query."

-- | A map which contains signatures for a few common theorems which can be used in the proofs which 'getProof' returns.
commonTheorems :: FunctionParser
commonTheorems = mconcat
                 [nameParser (L.Symbol "|unit-resolution|")
                  (OverloadedParser (const True)
                   (const $ Just $ toSort (undefined::Bool) ())
                   $ \_ _ f -> Just $ f (SMTFun "|unit-resolution|" () :: SMTFun [SMTExpr Bool] Bool))
                 ,simpleParser (SMTFun "asserted" () :: SMTFun (SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "hypothesis" () :: SMTFun (SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "lemma" () :: SMTFun (SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "monotonicity" () :: SMTFun (SMTExpr Bool,SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "trans" () :: SMTFun (SMTExpr Bool,SMTExpr Bool,SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "rewrite" () :: SMTFun (SMTExpr Bool) Bool)
                 ,simpleParser (SMTFun "mp" () :: SMTFun (SMTExpr Bool,SMTExpr Bool,SMTExpr Bool) Bool)]

optimizeExpr' :: SMTExpr a -> SMTExpr a
optimizeExpr' e = case optimizeExpr e of
  Nothing -> e
  Just e' -> e'
