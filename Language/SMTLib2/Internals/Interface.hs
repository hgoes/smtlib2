module Language.SMTLib2.Internals.Interface
       (Same(),IsSMTNumber(),HasMonad(..),
        -- * Expressions
        pattern Var,
        -- ** Constants
        pattern ConstBool,pattern ConstInt,pattern ConstReal,pattern ConstBV,
        constant,asConstant,true,false,cbool,cint,creal,cbv,cbvUntyped,cbvUntyped',cdt,
        -- ** Quantification
        exists,forall,
        -- ** Let
        let',
        -- ** Functions
        pattern Fun,app,fun,
        -- *** Equality
        pattern EqLst,pattern Eq,pattern (:==:),
        eq,(.==.),
        pattern DistinctLst,pattern Distinct,pattern (:/=:),
        distinct,(./=.),
        -- *** Map
        map',
        -- *** Comparison
        pattern Ord,pattern (:>=:),pattern (:>:),pattern (:<=:),pattern (:<:),
        ord,(.>=.),(.>.),(.<=.),(.<.),
        -- *** Arithmetic
        pattern ArithLst,pattern Arith,arith,
        pattern PlusLst,pattern Plus,pattern (:+:),plus,(.+.),
        pattern MultLst,pattern Mult,pattern (:*:),mult,(.*.),
        pattern MinusLst,pattern Minus,pattern (:-:),pattern Neg,minus,(.-.),neg,
        pattern Div,pattern Mod,pattern Rem,pattern Exp,div',mod',rem',exp',
        pattern (:/:),(./.),
        pattern Abs,abs',
        -- *** Logic
        pattern Not,not',
        pattern LogicLst,pattern Logic,logic,
        pattern AndLst,pattern And,pattern (:&:),and',(.&.),
        pattern OrLst,pattern Or,pattern (:|:),or',(.|.),
        pattern XOrLst,pattern XOr,xor',
        pattern ImpliesLst,pattern Implies,pattern (:=>:),implies,(.=>.),
        pattern AtLeastLst,pattern AtLeast,atLeast,
        pattern AtMostLst,pattern AtMost,atMost,
        -- *** Conversion
        pattern ToReal,pattern ToInt,toReal,toInt,
        -- *** If-then-else
        pattern ITE,ite,
        -- *** Bitvectors
        pattern BVComp,pattern BVULE,pattern BVULT,pattern BVUGE,pattern BVUGT,pattern BVSLE,pattern BVSLT,pattern BVSGE,pattern BVSGT,bvcomp,bvule,bvult,bvuge,bvugt,bvsle,bvslt,bvsge,bvsgt,
        pattern BVBin,pattern BVAdd,pattern BVSub,pattern BVMul,pattern BVURem,pattern BVSRem,pattern BVUDiv,pattern BVSDiv,pattern BVSHL,pattern BVLSHR,pattern BVASHR,pattern BVXor,pattern BVAnd,pattern BVOr,bvbin,bvadd,bvsub,bvmul,bvurem,bvsrem,bvudiv,bvsdiv,bvshl,bvlshr,bvashr,bvxor,bvand,bvor,
        pattern BVUn,pattern BVNot,pattern BVNeg,
        bvun,bvnot,bvneg,
        pattern Concat,pattern Extract,concat',extract',extractChecked,extractUntypedStart,extractUntyped,extractUntyped',
        -- *** Arrays
        pattern Select,pattern Store,pattern ConstArray,select,select1,store,store1,constArray,
        -- *** Datatypes
        pattern Mk,mk,pattern Is,is,(.#.),
        -- *** Misc
        pattern Divisible,divisible,
        -- * Lists
        (.:.),nil
       ) where

import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Expression hiding (Function(..),OrdOp(..),ArithOp(..),ArithOpInt(..),LogicOp(..),BVCompOp(..),BVBinOp(..),BVUnOp(..),Const,Var,arith,plus,minus,mult,abs')
import qualified Language.SMTLib2.Internals.Expression as E
import Language.SMTLib2.Internals.Embed

import Data.Constraint
import Data.Functor.Identity
import qualified GHC.TypeLits as TL

-- Helper classes

-- | All elements of this list must be of the same type
class Same (tps :: [Type]) where
  type SameType tps :: Type
  -- | Extract the type that all elements of the list share.
  --   This is simply the first element.
  sameType :: List Repr tps -> Repr (SameType tps)
  -- | Convert a list of same elements to an all-equal list.
  --   This is just the identity function.
  sameToAllEq :: List e tps -> List e (AllEq (SameType tps) (List.Length tps))

instance Same '[tp] where
  type SameType '[tp] = tp
  sameType (tp ::: Nil) = tp
  sameToAllEq = id

instance (Same (tp ': tps),tp ~ (SameType (tp ': tps))) => Same (tp ': tp ': tps) where
  type SameType (tp ': tp ': tps) = tp
  sameType (x ::: _) = x
  sameToAllEq (x ::: xs) = x ::: (sameToAllEq xs)

-- | Convert an all-equal list to a list of elements of same type.
--   This can fail (return 'Nothing') when the list is empty.
allEqToSame :: Repr tp -> Natural n -> List e (AllEq tp n)
            -> Maybe (Dict (Same (AllEq tp n),
                            SameType (AllEq tp n) ~ tp))
allEqToSame _ Zero Nil = Nothing
allEqToSame tp (Succ Zero) (x ::: Nil) = Just Dict
allEqToSame tp (Succ (Succ n)) (x ::: y ::: ys) = do
  Dict <- allEqToSame tp (Succ n) (y ::: ys)
  return Dict

-- | The same as 'allEqToSame' but also returns the original list.
--   Only used for pattern matching.
allEqToSame' :: Repr tp -> Natural n -> List e (AllEq tp n)
             -> Maybe (Dict (Same (AllEq tp n),
                             SameType (AllEq tp n) ~ tp),
                       List e (AllEq tp n))
allEqToSame' tp n lst = do
  d <- allEqToSame tp n lst
  return (d,lst)

class Num (Value tp) => IsSMTNumber (tp :: Type) where
  smtNumRepr :: NumRepr tp
  smtFromInteger :: Integer -> Value tp

instance IsSMTNumber IntType where
  smtNumRepr = NumInt
  smtFromInteger n = IntValue n

instance IsSMTNumber RealType where
  smtNumRepr = NumReal
  smtFromInteger n = RealValue (fromInteger n)

class HasMonad a where
  type MatchMonad a (m :: * -> *) :: Constraint
  type MonadResult a :: *
  embedM :: (Applicative m,MatchMonad a m) => a -> m (MonadResult a)

instance HasMonad (e (tp::Type)) where
  type MatchMonad (e tp) m = ()
  type MonadResult (e tp) = e tp
  embedM = pure

instance HasMonad ((m :: * -> *) (e (tp::Type))) where
  type MatchMonad (m (e tp)) m' = m ~ m'
  type MonadResult (m (e tp)) = e tp
  embedM = id

instance HasMonad (List e (tp::[Type])) where
  type MatchMonad (List e tp) m = ()
  type MonadResult (List e tp) = List e tp
  embedM = pure

instance HasMonad (m (List e (tp::[Type]))) where
  type MatchMonad (m (List e tp)) m' = m ~ m'
  type MonadResult (m (List e tp)) = List e tp
  embedM = id

matchNumRepr :: NumRepr tp -> Dict (IsSMTNumber tp)
matchNumRepr NumInt = Dict
matchNumRepr NumReal = Dict

matchNumRepr' :: NumRepr tp -> (Dict (IsSMTNumber tp),NumRepr tp)
matchNumRepr' r = (matchNumRepr r,r)

-- Patterns

#if __GLASGOW_HASKELL__ >= 800
#define SEP ->
#define MK_SIG(PROV,REQ,NAME,LHS,RHS) pattern NAME :: REQ => PROV => LHS -> RHS
#elif __GLASGOW_HASKELL__ >= 710
#define SEP ->
#define MK_SIG(PROV,REQ,NAME,LHS,RHS) pattern NAME :: PROV => REQ => LHS -> RHS
#else
#define SEP
#define MK_SIG(PROV,REQ,NAME,LHS,RHS) pattern PROV => NAME LHS :: REQ => RHS
#endif

-- | Matches constant boolean expressions ('true' or 'false').
MK_SIG((rtp ~ BoolType),(),ConstBool,Bool,Expression v qv fun fv lv e rtp)
pattern ConstBool x = E.Const (BoolValue x)

MK_SIG((rtp ~ IntType),(),ConstInt,Integer,Expression v qv fun fv lv e rtp)
pattern ConstInt x = E.Const (IntValue x)

MK_SIG((rtp ~ RealType),(),ConstReal,Rational,Expression v qv fun fv lv e rtp)
pattern ConstReal x = E.Const (RealValue x)

MK_SIG((rtp ~ BitVecType bw),(),ConstBV,Integer SEP (BitWidth bw),Expression v qv fun fv lv e rtp)
pattern ConstBV x bw = E.Const (BitVecValue x bw)

pattern Fun f arg = App (E.Fun f) arg

MK_SIG((rtp ~ BoolType),(),EqLstP,(Repr tp) SEP [e tp],Expression v qv fun fv lv e rtp)
pattern EqLstP tp lst <- App (E.Eq tp n) (allEqToList n -> lst) where
   EqLstP tp lst = allEqFromList lst (\n -> App (E.Eq tp n))

MK_SIG((rtp ~ BoolType),(GetType e),EqLst,[e tp],Expression v qv fun fv lv e rtp)
pattern EqLst lst <- EqLstP _ lst where
  EqLst lst@(x:_) = EqLstP (getType x) lst

MK_SIG((rtp ~ BoolType,Same tps),(GetType e),Eq,List e tps,Expression v qv fun fv lv e rtp)
pattern Eq lst <- App (E.Eq tp n) (allEqToSame' tp n -> Just (Dict,lst)) where
  Eq lst = sameApp E.Eq lst

MK_SIG((rtp ~ BoolType),(GetType e),(:==:),(e tp) SEP (e tp),Expression v qv fun fv lv e rtp)
pattern (:==:) x y <- App (E.Eq _ (Succ (Succ Zero))) (x ::: y ::: Nil) where
  (:==:) x y = App (E.Eq (getType x) (Succ (Succ Zero))) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType),(),DistinctLstP,(Repr tp) SEP [e tp],Expression v qv fun fv lv e rtp)
pattern DistinctLstP tp lst <- App (E.Distinct tp n) (allEqToList n -> lst) where
   DistinctLstP tp lst = allEqFromList lst (\n -> App (E.Distinct tp n))

MK_SIG((rtp ~ BoolType),(GetType e),DistinctLst,[e tp],Expression v qv fun fv lv e rtp)
pattern DistinctLst lst <- DistinctLstP _ lst where
  DistinctLst lst@(x:_) = DistinctLstP (getType x) lst

MK_SIG((rtp ~ BoolType,Same tps),(GetType e),Distinct,List e tps,Expression v qv fun fv lv e rtp)
pattern Distinct lst <- App (E.Distinct tp n) (allEqToSame' tp n -> Just (Dict,lst)) where
  Distinct lst = sameApp E.Distinct lst

MK_SIG((rtp ~ BoolType),(GetType e),(:/=:),(e tp) SEP (e tp),Expression v qv fun fv lv e rtp)
pattern (:/=:) x y <- App (E.Distinct _ (Succ (Succ Zero))) (x ::: y ::: Nil) where
  (:/=:) x y = App (E.Distinct (getType x) (Succ (Succ Zero))) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),Ord,E.OrdOp SEP (e tp) SEP (e tp),Expression v qv fun fv lv e rtp)
pattern Ord op x y <- App (E.Ord (matchNumRepr -> Dict) op) (x ::: y ::: Nil) where
  Ord op x y = App (E.Ord smtNumRepr op) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),(:>=:),(e tp) SEP (e tp),Expression v qv fun fv lv e rtp)
pattern (:>=:) x y <- App (E.Ord (matchNumRepr -> Dict) E.Ge) (x ::: y ::: Nil) where
  (:>=:) x y = App (E.Ord smtNumRepr E.Ge) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),(:>:),(e tp) SEP (e tp),Expression v qv fun fv lv e rtp)
pattern (:>:) x y <- App (E.Ord (matchNumRepr -> Dict) E.Gt) (x ::: y ::: Nil) where
  (:>:) x y = App (E.Ord smtNumRepr E.Gt) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),(:<=:),(e tp) SEP (e tp),Expression v qv fun fv lv e rtp)
pattern (:<=:) x y <- App (E.Ord (matchNumRepr -> Dict) E.Le) (x ::: y ::: Nil) where
  (:<=:) x y = App (E.Ord smtNumRepr E.Le) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),(:<:),(e tp) SEP (e tp),Expression v qv fun fv lv e rtp)
pattern (:<:) x y <- App (E.Ord (matchNumRepr -> Dict) E.Lt) (x ::: y ::: Nil) where
  (:<:) x y = App (E.Ord smtNumRepr E.Lt) (x ::: y ::: Nil)

MK_SIG((),(),ArithLstP,E.ArithOp SEP (NumRepr tp) SEP [e tp],Expression v qv fun fv lv e tp)
pattern ArithLstP op tp lst <- App (E.Arith tp op n) (allEqToList n -> lst) where
  ArithLstP op tp lst = allEqFromList lst (\n -> App (E.Arith tp op n))

MK_SIG((IsSMTNumber tp),(),ArithLst,E.ArithOp SEP [e tp],Expression v qv fun fv lv e tp)
pattern ArithLst op lst <- ArithLstP op (matchNumRepr -> Dict) lst where
  ArithLst op lst = ArithLstP op smtNumRepr lst

MK_SIG((IsSMTNumber tp,Same tps,tp ~ SameType tps),(),Arith,E.ArithOp SEP (List e tps),Expression v qv fun fv lv e tp)
pattern Arith op lst <- App (E.Arith (matchNumRepr' -> (Dict,tp)) op n)
                        (allEqToSame' (numRepr tp) n -> Just (Dict,lst)) where
  Arith op lst = App (E.Arith smtNumRepr op (List.length lst)) (sameToAllEq lst)

pattern PlusLst lst = ArithLst E.Plus lst
pattern Plus lst = Arith E.Plus lst
pattern (:+:) x y = Arith E.Plus (x ::: y ::: Nil)

pattern MinusLst lst = ArithLst E.Minus lst
pattern Minus lst = Arith E.Minus lst
pattern (:-:) x y = Arith E.Minus (x ::: y ::: Nil)
pattern Neg x = Arith E.Minus (x ::: Nil)

pattern MultLst lst = ArithLst E.Mult lst
pattern Mult lst = Arith E.Mult lst
pattern (:*:) x y = Arith E.Mult (x ::: y ::: Nil)

pattern Div x y = App (E.ArithIntBin E.Div) (x ::: y ::: Nil)
pattern Mod x y = App (E.ArithIntBin E.Mod) (x ::: y ::: Nil)
pattern Rem x y = App (E.ArithIntBin E.Rem) (x ::: y ::: Nil)
pattern Exp x y = App (E.ArithIntBin E.Exp) (x ::: y ::: Nil)

pattern (:/:) x y = App E.Divide (x ::: y ::: Nil)

MK_SIG((IsSMTNumber tp),(),Abs,e tp,Expression v qv fun fv lv e tp)
pattern Abs x <- App (E.Abs (matchNumRepr -> Dict)) (x ::: Nil) where
  Abs x = App (E.Abs smtNumRepr) (x ::: Nil)

pattern Not x = App E.Not (x ::: Nil)

MK_SIG((rtp ~ BoolType),(),LogicLst,E.LogicOp SEP [e BoolType],Expression v qv fun fv lv e rtp)
pattern LogicLst op lst <- App (E.Logic op n) (allEqToList n -> lst) where
  LogicLst op lst = allEqFromList lst (\n -> App (E.Logic op n))

MK_SIG((rtp ~ BoolType,Same tps,SameType tps ~ BoolType),(),Logic,E.LogicOp SEP (List e tps),Expression v qv fun fv lv e rtp)
pattern Logic op lst <- App (E.Logic op n) (allEqToSame' bool n -> Just (Dict,lst)) where
  Logic op lst = App (E.Logic op (List.length lst)) (sameToAllEq lst)

pattern AndLst lst = LogicLst E.And lst
pattern And lst = Logic E.And lst
MK_SIG((rtp ~ BoolType),(),(:&:),(e BoolType) SEP (e BoolType),Expression v qv fun fv lv e rtp)
pattern (:&:) x y = App (E.Logic E.And (Succ (Succ Zero))) (x ::: y ::: Nil)

pattern OrLst lst = LogicLst E.Or lst
pattern Or lst = Logic E.Or lst
MK_SIG((rtp ~ BoolType),(),(:|:),(e BoolType) SEP (e BoolType),Expression v qv fun fv lv e rtp)
pattern (:|:) x y = App (E.Logic E.Or (Succ (Succ Zero))) (x ::: y ::: Nil)

pattern XOrLst lst = LogicLst E.XOr lst
pattern XOr lst = Logic E.XOr lst

pattern ImpliesLst lst = LogicLst E.Implies lst
pattern Implies lst = Logic E.Implies lst
MK_SIG((rtp ~ BoolType),(),(:=>:),(e BoolType) SEP (e BoolType),Expression v qv fun fv lv e rtp)
pattern (:=>:) x y = App (E.Logic E.Implies (Succ (Succ Zero))) (x ::: y ::: Nil)

pattern AtLeastLst n lst = LogicLst (E.AtLeast n) lst
pattern AtLeast n lst = Logic (E.AtLeast n) lst

pattern AtMostLst n lst = LogicLst (E.AtMost n) lst
pattern AtMost n lst = Logic (E.AtMost n) lst

pattern ToReal x = App E.ToReal (x ::: Nil)
pattern ToInt x = App E.ToInt (x ::: Nil)

MK_SIG((),(GetType e),ITE,(e BoolType) SEP (e tp) SEP (e tp),Expression v qv fun fv lv e tp)
pattern ITE c ifT ifF <- App (E.ITE _) (c ::: ifT ::: ifF ::: Nil) where
  ITE c ifT ifF = App (E.ITE (getType ifT)) (c ::: ifT ::: ifF ::: Nil)

MK_SIG((rtp ~ BoolType),(GetType e),BVComp,E.BVCompOp SEP (e (BitVecType bw)) SEP (e (BitVecType bw)),Expression v qv fun fv lv e rtp)
pattern BVComp op lhs rhs <- App (E.BVComp op _) (lhs ::: rhs ::: Nil) where
  BVComp op lhs rhs = App (E.BVComp op (getBW lhs)) (lhs ::: rhs ::: Nil)

pattern BVULE lhs rhs = BVComp E.BVULE lhs rhs
pattern BVULT lhs rhs = BVComp E.BVULT lhs rhs
pattern BVUGE lhs rhs = BVComp E.BVUGE lhs rhs
pattern BVUGT lhs rhs = BVComp E.BVUGT lhs rhs
pattern BVSLE lhs rhs = BVComp E.BVSLE lhs rhs
pattern BVSLT lhs rhs = BVComp E.BVSLT lhs rhs
pattern BVSGE lhs rhs = BVComp E.BVSGE lhs rhs
pattern BVSGT lhs rhs = BVComp E.BVSGT lhs rhs

MK_SIG((rtp ~ BitVecType bw),(GetType e),BVBin,E.BVBinOp SEP (e (BitVecType bw)) SEP (e (BitVecType bw)),Expression v qv fun fv lv e rtp)
pattern BVBin op lhs rhs <- App (E.BVBin op _) (lhs ::: rhs ::: Nil) where
  BVBin op lhs rhs = App (E.BVBin op (getBW lhs)) (lhs ::: rhs ::: Nil)

pattern BVAdd lhs rhs = BVBin E.BVAdd lhs rhs
pattern BVSub lhs rhs = BVBin E.BVSub lhs rhs
pattern BVMul lhs rhs = BVBin E.BVMul lhs rhs
pattern BVURem lhs rhs = BVBin E.BVURem lhs rhs
pattern BVSRem lhs rhs = BVBin E.BVSRem lhs rhs
pattern BVUDiv lhs rhs = BVBin E.BVUDiv lhs rhs
pattern BVSDiv lhs rhs = BVBin E.BVSDiv lhs rhs
pattern BVSHL lhs rhs = BVBin E.BVSHL lhs rhs
pattern BVLSHR lhs rhs = BVBin E.BVLSHR lhs rhs
pattern BVASHR lhs rhs = BVBin E.BVASHR lhs rhs
pattern BVXor lhs rhs = BVBin E.BVXor lhs rhs
pattern BVAnd lhs rhs = BVBin E.BVAnd lhs rhs
pattern BVOr lhs rhs = BVBin E.BVOr lhs rhs

MK_SIG((rtp ~ BitVecType bw),(GetType e),BVUn,E.BVUnOp SEP (e (BitVecType bw)),Expression v qv fun fv lv e rtp)
pattern BVUn op x <- App (E.BVUn op _) (x ::: Nil) where
  BVUn op x = App (E.BVUn op (getBW x)) (x ::: Nil)

pattern BVNot x = BVUn E.BVNot x
pattern BVNeg x = BVUn E.BVNeg x

MK_SIG((rtp ~ val),(GetType e),Select,(e (ArrayType idx val)) SEP (List e idx),Expression v qv fun fv lv e rtp)
pattern Select arr idx <- App (E.Select _ _) (arr ::: idx) where
  Select arr idx = case getType arr of
    ArrayRepr idxTp elTp -> App (E.Select idxTp elTp) (arr ::: idx)

MK_SIG((rtp ~ ArrayType idx val),(GetType e),Store,(e (ArrayType idx val)) SEP (List e idx) SEP (e val),Expression v qv fun fv lv e rtp)
pattern Store arr idx el <- App (E.Store _ _) (arr ::: el ::: idx) where
  Store arr idx el = case getType arr of
    ArrayRepr idxTp elTp -> App (E.Store idxTp elTp) (arr ::: el ::: idx)

MK_SIG((rtp ~ ArrayType idx val),(GetType e),ConstArray,(List Repr idx) SEP (e val),Expression v qv fun fv lv e rtp)
pattern ConstArray idx el <- App (E.ConstArray idx _) (el ::: Nil) where
  ConstArray idx el = App (E.ConstArray idx (getType el)) (el ::: Nil)

MK_SIG((rtp ~ BitVecType (n1 TL.+ n2)),(GetType e),Concat,(e (BitVecType n1)) SEP (e (BitVecType n2)),Expression v qv fun fv lv e rtp)
pattern Concat lhs rhs <- App (E.Concat _ _) (lhs :::rhs ::: Nil) where
  Concat lhs rhs = case getType lhs of
    BitVecRepr n1 -> case getType rhs of
      BitVecRepr n2 -> App (E.Concat n1 n2) (lhs ::: rhs ::: Nil)

MK_SIG((rtp ~ BitVecType len),(GetType e),Extract,(BitWidth start) SEP (BitWidth len) SEP (e (BitVecType bw)),Expression v qv fun fv lv e rtp)
pattern Extract start len arg <- App (E.Extract _ start len) (arg ::: Nil) where
  Extract start len arg = case getType arg of
    BitVecRepr bw -> App (E.Extract bw start len) (arg ::: Nil)

MK_SIG((rtp ~ BoolType),(),Divisible,Integer SEP (e IntType),Expression v qv fun fv lv e rtp)
pattern Divisible n e = App (E.Divisible n) (e ::: Nil)

pattern Mk dt par con args = App (E.Constructor dt par con) args

MK_SIG((rtp ~ BoolType),(GetType e),Is,(Constr dt sig) SEP (e (DataType dt par)),Expression v qv fun fv lv e rtp)
pattern Is con e <- App (E.Test _ _ con) (e ::: Nil) where
  Is con e = case getType e of
    DataRepr dt par -> App (E.Test dt par con) (e ::: Nil)

{-MK_SIG((),(GetType e),(:#:),(e (DataType dt par)) SEP (Field dt tp),Expression v qv fun fv lv e (CType tp par))
pattern (:#:) e field <- App (E.Field _ _ field) (e ::: Nil) where
  (:#:) e field = case getType e of
    DataRepr dt par -> App (E.Field dt par field) (e ::: Nil)-}

sameApp :: (Same tps,GetType e)
        => (Repr (SameType tps) -> Natural (List.Length tps)
            -> E.Function fun '(AllEq (SameType tps) (List.Length tps),ret))
        -> List e tps
        -> Expression v qv fun fv lv e ret
sameApp f lst = App (f (sameType $ runIdentity $
                        List.mapM (return.getType) lst
                       ) (List.length lst))
                (sameToAllEq lst)

getBW :: GetType e => e (BitVecType bw) -> BitWidth bw
getBW e = case getType e of
  BitVecRepr bw -> bw

-- | Create a constant, for example an integer:
--
--   Example:
-- 
--   @
-- do
--   x <- declareVar int
--   -- x is greater than 5
--   assert $ x .>. constant (IntValue 5)
--   @
constant :: (Embed m e) => Value tp -> m (e tp)
constant x = embed $ pure $ E.Const x

-- | Create a boolean constant expression.
cbool :: Embed m e => Bool -> m (e BoolType)
cbool x = embed $ pure $ E.Const (BoolValue x)

-- | Create an integer constant expression.
cint :: Embed m e => Integer -> m (e IntType)
cint x = embed $ pure $ E.Const (IntValue x)

-- | Create a real constant expression.
--
--   Example:
--
--   @
-- import Data.Ratio
--
-- x = creal (5 % 4)
--   @
creal :: Embed m e => Rational -> m (e RealType)
creal x = embed $ pure $ E.Const (RealValue x)

-- | Create a constant bitvector expression.
cbv :: Embed m e => Integer -- ^ The value (negative values will be stored in two's-complement).
    -> BitWidth bw -- ^ The bitwidth of the bitvector value.
    -> m (e (BitVecType bw))
cbv i bw = embed $ pure $ E.Const (BitVecValue i bw)

-- | Create an untyped constant bitvector expression.
cbvUntyped :: (Embed m e,Monad m) => Integer -- ^ The value (negative values will be stored in two's-complement).
           -> Integer -- ^ The bitwidth (must be >= 0).
           -> (forall bw. e (BitVecType bw) -> m b)
           -> m b
cbvUntyped val w f = case TL.someNatVal w of
  Just (TL.SomeNat rw) -> do
    bv <- embed $ pure $ E.Const (BitVecValue val (bw rw))
    f bv
  Nothing -> error "cbvUntyped: Negative bitwidth"

cbvUntyped' :: (Embed m e,Monad m) => Integer -- ^ The value (negative values will be stored in two's-complement).
            -> Integer -- ^ The bitwidth (must be >= 0).
            -> (forall bw. BitWidth bw -> e (BitVecType bw) -> m b)
            -> m b
cbvUntyped' val w f = getBw w $ \rw -> do
  bv <- embed $ pure $ E.Const (BitVecValue val rw)
  f rw bv

cdt :: (Embed m e,IsDatatype t,List.Length par ~ Parameters t)
    => t par Value -> m (e (DataType t par))
cdt v = embed $ pure $ E.Const $ DataValue v

asConstant :: Expression v qv fun fv lv e tp -> Maybe (Value tp)
asConstant (E.Const v) = Just v
asConstant _ = Nothing

MK_SIG((tp ~ rtp),(),Var,(v tp),Expression v qv fun fv lv e rtp)
pattern Var x = E.Var x

fun :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ List e args)
    => EmFun m e '(args,res) -> a -> m (e res)
fun fun args = embed $ App (E.Fun fun) <$> embedM args
{-# INLINEABLE fun #-}

-- | Create an expression by applying a function to a list of arguments.
app :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ List e args)
    => E.Function (EmFun m e) '(args,res)
    -> a
    -> m (e res)
app f args = embed $ App f <$> embedM args
{-# INLINEABLE app #-}

-- | Create a typed list by appending an element to the front of another list.
(.:.) :: (HasMonad a,MonadResult a ~ e tp,MatchMonad a m,Applicative m)
      => a -> m (List e tps) -> m (List e (tp ': tps))
(.:.) x xs = (:::) <$> embedM x <*> xs
{-# INLINEABLE (.:.) #-}

infixr 5 .:.

-- | Create an empty list.
nil :: Applicative m => m (List e '[])
nil = pure Nil

-- | Create a boolean expression that encodes that two expressions have the same
--   value.
--
--   Example:
--
--   @
-- is5 :: 'Language.SMTLib2.Backend' b => 'Language.SMTLib2.Expr' b 'IntType' -> 'Language.SMTLib2.SMT' b 'BoolType'
-- is5 e = e `.==.` `cint` 5
--   @
(.==.) :: (Embed m e,HasMonad a,HasMonad b,
           MatchMonad a m,MatchMonad b m,
           MonadResult a ~ e tp,MonadResult b ~ e tp)
       => a -> b -> m (e BoolType)
(.==.) lhs rhs
  = embed $ (\lhs' rhs' tp -> App (E.Eq (tp lhs') (Succ (Succ Zero))) (lhs' ::: rhs' ::: Nil)) <$>
    (embedM lhs) <*>
    (embedM rhs) <*>
    embedTypeOf
{-# INLINEABLE (.==.) #-}

(./=.) :: (Embed m e,HasMonad a,HasMonad b,
           MatchMonad a m,MatchMonad b m,
           MonadResult a ~ e tp,MonadResult b ~ e tp)
       => a -> b -> m (e BoolType)
(./=.) lhs rhs
  = embed $ (\lhs' rhs' tp -> App (E.Distinct (tp lhs') (Succ (Succ Zero))) (lhs' ::: rhs' ::: Nil)) <$>
    (embedM lhs) <*>
    (embedM rhs) <*>
    embedTypeOf
{-# INLINEABLE (./=.) #-}

infix 4 .==., ./=.

eq :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp)
   => [a] -> m (e BoolType)
eq [] = embed $ pure $ E.Const (BoolValue True)
eq xs = embed $ (\xs' tp -> allEqFromList xs' $ \n -> App (E.Eq (tp $ head xs') n)) <$>
        (traverse embedM xs) <*>
        embedTypeOf
{-# INLINEABLE eq #-}

distinct :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp)
         => [a] -> m (e BoolType)
distinct [] = embed $ pure $ E.Const (BoolValue True)
distinct xs = embed $ (\xs' tp -> allEqFromList xs' $ \n -> App (E.Distinct (tp $ head xs') n)) <$>
              (traverse embedM xs) <*>
              embedTypeOf
{-# INLINEABLE distinct #-}

map' :: (Embed m e,HasMonad arg,MatchMonad arg m,MonadResult arg ~ List e (Lifted tps idx),
         Unlift tps idx,GetType e,GetFunType (EmFun m e))
     => E.Function (EmFun m e) '(tps,res)
     -> arg
     -> m (e (ArrayType idx res))
map' f arg = embed $ (\arg' -> let (tps,res) = getFunType f
                                   idx = unliftTypeWith (getTypes arg') tps
                               in E.App (E.Map idx f) arg') <$>
             (embedM arg)
{-# INLINEABLE map' #-}

ord :: (Embed m e,IsSMTNumber tp,HasMonad a,HasMonad b,
        MatchMonad a m,MatchMonad b m,
        MonadResult a ~ e tp,MonadResult b ~ e tp)
    => E.OrdOp -> a -> b -> m (e BoolType)
ord op lhs rhs = embed $ Ord op <$> embedM lhs <*> embedM rhs
{-# INLINEABLE ord #-}

(.>=.),(.>.),(.<=.),(.<.) :: (Embed m e,IsSMTNumber tp,HasMonad a,HasMonad b,
                              MatchMonad a m,MatchMonad b m,
                              MonadResult a ~ e tp,MonadResult b ~ e tp)
                          => a -> b -> m (e BoolType)
(.>=.) = ord E.Ge
(.>.) = ord E.Gt
(.<=.) = ord E.Le
(.<.) = ord E.Lt
{-# INLINEABLE (.>=.) #-}
{-# INLINEABLE (.>.) #-}
{-# INLINEABLE (.<=.) #-}
{-# INLINEABLE (.<.) #-}

infix 4 .>=.,.>.,.<=.,.<.

arith :: (Embed m e,HasMonad a,MatchMonad a m,
          MonadResult a ~ e tp,IsSMTNumber tp)
      => E.ArithOp -> [a] -> m (e tp)
arith op xs = embed $ ArithLst op <$> traverse embedM xs
{-# INLINEABLE arith #-}

plus,minus,mult :: (Embed m e,HasMonad a,MatchMonad a m,
                    MonadResult a ~ e tp,IsSMTNumber tp)
                => [a] -> m (e tp)
plus = arith E.Plus
minus = arith E.Minus
mult = arith E.Mult
{-# INLINEABLE plus #-}
{-# INLINEABLE minus #-}
{-# INLINEABLE mult #-}

(.+.),(.-.),(.*.) :: (Embed m e,HasMonad a,HasMonad b,
                      MatchMonad a m,MatchMonad b m,
                      MonadResult a ~ e tp,MonadResult b ~ e tp,
                      IsSMTNumber tp)
                  => a -> b -> m (e tp)
(.+.) x y = embed $ (:+:) <$> embedM x <*> embedM y
(.-.) x y = embed $ (:-:) <$> embedM x <*> embedM y
(.*.) x y = embed $ (:*:) <$> embedM x <*> embedM y
{-# INLINEABLE (.+.) #-}
{-# INLINEABLE (.-.) #-}
{-# INLINEABLE (.*.) #-}

infixl 6 .+.,.-.
infixl 7 .*.

neg :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp,IsSMTNumber tp)
    => a -> m (e tp)
neg x = embed $ Neg <$> embedM x
{-# INLINEABLE neg #-}

abs' :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp,IsSMTNumber tp)
     => a -> m (e tp)
abs' x = embed $ Abs <$> embedM x
{-# INLINEABLE abs' #-}

-- TODO: The following instances cause overlap:
{-instance (Embed m e) => Num (m (e IntType)) where
  fromInteger x = embed $ E.Const $ smtFromInteger x
  (+) x y = do
    x' <- x
    y' <- y
    embed $ x' :+: y'
  (-) x y = do
    x' <- x
    y' <- y
    embed $ x' :-: y'
  (*) x y = do
    x' <- x
    y' <- y
    embed $ x' :*: y'
  negate x = x >>= embed.Neg
  abs x = x >>= embed.Abs
  signum x = do
    x' <- x
    one <- embed $ E.Const (IntValue 1)
    negOne <- embed $ E.Const (IntValue (-1))
    zero <- embed $ E.Const (IntValue 0)
    ltZero <- embed $ x' :<: zero
    gtZero <- embed $ x' :>: zero
    cond1 <- embed $ App (E.ITE int) (ltZero ::: negOne ::: zero ::: Nil)
    embed $ App (E.ITE int) (gtZero ::: one ::: cond1 ::: Nil)

instance (Embed m e) => Num (m (e RealType)) where
  fromInteger x = embed $ E.Const $ smtFromInteger x
  (+) x y = do
    x' <- x
    y' <- y
    embed $ x' :+: y'
  (-) x y = do
    x' <- x
    y' <- y
    embed $ x' :-: y'
  (*) x y = do
    x' <- x
    y' <- y
    embed $ x' :*: y'
  negate x = x >>= embed.Neg
  abs x = x >>= embed.Abs
  signum x = do
    x' <- x
    one <- embed $ E.Const (smtFromInteger 1)
    negOne <- embed $ Neg one
    zero <- embed $ E.Const (smtFromInteger 0)
    ltZero <- embed $ x' :<: zero
    gtZero <- embed $ x' :>: zero
    cond1 <- embed $ App (E.ITE real) (ltZero ::: negOne ::: zero ::: Nil)
    embed $ App (E.ITE real) (gtZero ::: one ::: cond1 ::: Nil) -}

rem',div',mod' :: (Embed m e,HasMonad a,HasMonad b,
                   MatchMonad a m,MatchMonad b m,
                   MonadResult a ~ e IntType,MonadResult b ~ e IntType)
               => a -> b -> m (e IntType)
rem' x y = embed $ Rem <$> embedM x <*> embedM y
div' x y = embed $ Div <$> embedM x <*> embedM y
mod' x y = embed $ Mod <$> embedM x <*> embedM y
exp' x y = embed $ Exp <$> embedM x <*> embedM y
{-# INLINEABLE rem' #-}
{-# INLINEABLE div' #-}
{-# INLINEABLE mod' #-}
{-# INLINEABLE exp' #-}

infixl 7 `div'`, `rem'`, `mod'`

(./.) :: (Embed m e,HasMonad a,HasMonad b,MatchMonad a m,MatchMonad b m,
          MonadResult a ~ e RealType,MonadResult b ~ e RealType)
      => a -> b -> m (e RealType)
(./.) x y = embed $ (:/:) <$> embedM x <*> embedM y
{-# INLINEABLE (./.) #-}

infixl 7 ./.

-- TODO: The following instances cause overlap:
{- instance Embed m e => Fractional (m (e RealType)) where
  (/) x y = do
    x' <- x
    y' <- y
    embed $ x' :/: y'
  fromRational r = embed $ E.Const $ RealValue r -}

not' :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e BoolType)
     => a -> m (e BoolType)
not' x = embed $ Not <$> embedM x
{-# INLINEABLE not' #-}

logic :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e BoolType)
      => E.LogicOp -> [a] -> m (e BoolType)
logic op lst = embed $ LogicLst op <$> traverse embedM lst
{-# INLINEABLE logic #-}

and',or',xor',implies :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e BoolType)
                      => [a] -> m (e BoolType)
and' [] = true
and' [x] = embedM x
and' xs = embed $ AndLst <$> traverse embedM xs
or' [] = false
or' [x] = embedM x
or' xs = embed $ OrLst <$> traverse embedM xs
xor' xs = embed $ XOrLst <$> traverse embedM xs
implies xs = embed $ ImpliesLst <$> traverse embedM xs
{-# INLINEABLE and' #-}
{-# INLINEABLE or' #-}
{-# INLINEABLE xor' #-}
{-# INLINEABLE implies #-}

atLeast,atMost :: (Embed m e,HasMonad a,MatchMonad a m,
                   MonadResult a ~ e BoolType)
               => Integer -> [a] -> m (e BoolType)
atLeast n xs = embed $ AtLeastLst n <$> traverse embedM xs
atMost n xs = embed $ AtMostLst n <$> traverse embedM xs
{-# INLINEABLE atLeast #-}
{-# INLINEABLE atMost #-}

(.&.),(.|.),(.=>.) :: (Embed m e,HasMonad a,HasMonad b,
                       MatchMonad a m,MatchMonad b m,
                       MonadResult a ~ e BoolType,MonadResult b ~ e BoolType)
                   => a -> b -> m (e BoolType)
(.&.) x y = embed $ (:&:) <$> embedM x <*> embedM y
(.|.) x y = embed $ (:|:) <$> embedM x <*> embedM y
(.=>.) x y = embed $ (:=>:) <$> embedM x <*> embedM y
{-# INLINEABLE (.&.) #-}
{-# INLINEABLE (.|.) #-}
{-# INLINEABLE (.=>.) #-}

infixr 3 .&.
infixr 2 .|.
infixr 2 .=>.

toReal :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e IntType)
       => a -> m (e RealType)
toReal x = embed $ ToReal <$> embedM x
{-# INLINEABLE toReal #-}

toInt :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e RealType)
      => a -> m (e IntType)
toInt x = embed $ ToInt <$> embedM x
{-# INLINEABLE toInt #-}

ite :: (Embed m e,HasMonad a,HasMonad b,HasMonad c,
        MatchMonad a m,MatchMonad b m,MatchMonad c m,
        MonadResult a ~ e BoolType,MonadResult b ~ e tp,MonadResult c ~ e tp)
    => a -> b -> c -> m (e tp)
ite c ifT ifF = embed $ (\c' ifT' ifF' tp -> App (E.ITE (tp ifT')) (c' ::: ifT' ::: ifF' ::: Nil)) <$>
                embedM c <*>
                embedM ifT <*>
                embedM ifF <*>
                embedTypeOf
{-# INLINEABLE ite #-}

bvcomp :: forall m e a b bw.
          (Embed m e,HasMonad a,HasMonad b,
           MatchMonad a m,MatchMonad b m,
           MonadResult a ~ e (BitVecType bw),MonadResult b ~ e (BitVecType bw))
       => E.BVCompOp -> a -> b -> m (e BoolType)
bvcomp op x y = embed $ (\x' y' tp -> case tp x' of
                            BitVecRepr bw -> App (E.BVComp op bw) (x' ::: y' ::: Nil)) <$>
                embedM x <*>
                embedM y <*>
                embedTypeOf
{-# INLINEABLE bvcomp #-}

bvule,bvult,bvuge,bvugt,bvsle,bvslt,bvsge,bvsgt :: (Embed m e,HasMonad a,HasMonad b,
                                                    MatchMonad a m,MatchMonad b m,
                                                    MonadResult a ~ e (BitVecType bw),MonadResult b ~ e (BitVecType bw))
                                                   => a -> b -> m (e BoolType)
bvule = bvcomp E.BVULE
bvult = bvcomp E.BVULT
bvuge = bvcomp E.BVUGE
bvugt = bvcomp E.BVUGT
bvsle = bvcomp E.BVSLE
bvslt = bvcomp E.BVSLT
bvsge = bvcomp E.BVSGE
bvsgt = bvcomp E.BVSGT
{-# INLINEABLE bvule #-}
{-# INLINEABLE bvult #-}
{-# INLINEABLE bvuge #-}
{-# INLINEABLE bvugt #-}
{-# INLINEABLE bvsle #-}
{-# INLINEABLE bvslt #-}
{-# INLINEABLE bvsge #-}
{-# INLINEABLE bvsgt #-}

bvbin :: forall m e a b bw.
         (Embed m e,HasMonad a,HasMonad b,
          MatchMonad a m,MatchMonad b m,
          MonadResult a ~ e (BitVecType bw),MonadResult b ~ e (BitVecType bw))
      => E.BVBinOp -> a -> b -> m (e (BitVecType bw))
bvbin op x y = embed $ (\x' y' tp -> case tp x' of
                         BitVecRepr bw -> App (E.BVBin op bw) (x' ::: y' ::: Nil)) <$>
               embedM x <*>
               embedM y <*>
               embedTypeOf
{-# INLINEABLE bvbin #-}

bvadd,bvsub,bvmul,bvurem,bvsrem,bvudiv,bvsdiv,bvshl,bvlshr,bvashr,bvxor,bvand,bvor
  :: (Embed m e,HasMonad a,HasMonad b,
      MatchMonad a m,MatchMonad b m,
      MonadResult a ~ e (BitVecType bw),MonadResult b ~ e (BitVecType bw))
  => a -> b -> m (e (BitVecType bw))
bvadd = bvbin E.BVAdd
bvsub = bvbin E.BVSub
bvmul = bvbin E.BVMul
bvurem = bvbin E.BVURem
bvsrem = bvbin E.BVSRem
bvudiv = bvbin E.BVUDiv
bvsdiv = bvbin E.BVSDiv
bvshl = bvbin E.BVSHL
bvlshr = bvbin E.BVLSHR
bvashr = bvbin E.BVASHR
bvxor = bvbin E.BVXor
bvand = bvbin E.BVAnd
bvor = bvbin E.BVOr
{-# INLINEABLE bvadd #-}
{-# INLINEABLE bvsub #-}
{-# INLINEABLE bvmul #-}
{-# INLINEABLE bvurem #-}
{-# INLINEABLE bvsrem #-}
{-# INLINEABLE bvudiv #-}
{-# INLINEABLE bvsdiv #-}
{-# INLINEABLE bvshl #-}
{-# INLINEABLE bvlshr #-}
{-# INLINEABLE bvashr #-}
{-# INLINEABLE bvxor #-}
{-# INLINEABLE bvand #-}
{-# INLINEABLE bvor #-}

bvun :: forall m e a bw.
        (Embed m e,HasMonad a,
         MatchMonad a m,
         MonadResult a ~ e (BitVecType bw))
     => E.BVUnOp -> a -> m (e (BitVecType bw))
bvun op x = embed $ (\x' tp -> case tp x' of
                        BitVecRepr bw -> App (E.BVUn op bw) (x' ::: Nil)) <$>
            embedM x <*>
            embedTypeOf
{-# INLINEABLE bvun #-}

bvnot,bvneg :: (Embed m e,HasMonad a,
                MatchMonad a m,
                MonadResult a ~ e (BitVecType bw))
            => a -> m (e (BitVecType bw))
bvnot = bvun E.BVNot
bvneg = bvun E.BVNeg
{-# INLINEABLE bvnot #-}
{-# INLINEABLE bvneg #-}

-- | Access an array element.
--   The following law holds:
--
-- @
--    select (store arr i e) i .==. e
-- @
select :: (Embed m e,HasMonad arr,MatchMonad arr m,MonadResult arr ~ e (ArrayType idx el),
           HasMonad i,MatchMonad i m,MonadResult i ~ List e idx)
       => arr -> i -> m (e el)
select arr idx = embed $ (\arr' idx' tp -> case tp arr' of
                             ArrayRepr idxTp elTp -> App (E.Select idxTp elTp) (arr' ::: idx')) <$>
                 embedM arr <*>
                 embedM idx <*>
                 embedTypeOf
{-# INLINEABLE select #-}

-- | A specialized version of 'select' when the index is just a single element.
select1 :: (Embed m e,HasMonad arr,HasMonad idx,
            MatchMonad arr m,MatchMonad idx m,
            MonadResult arr ~ e (ArrayType '[idx'] el),
            MonadResult idx ~ e idx')
        => arr -> idx -> m (e el)
select1 arr idx = select arr (idx .:. nil)
{-# INLINEABLE select1 #-}

-- | Write an element into an array and return the resulting array.
--   The following laws hold (forall i/=j):
--
-- @
--    select (store arr i e) i .==. e
--    select (store arr i e) j .==. select arr j
-- @
store :: (Embed m e,HasMonad arr,MatchMonad arr m,MonadResult arr ~ e (ArrayType idx el),
          HasMonad i,MatchMonad i m,MonadResult i ~ List e idx,
          HasMonad nel,MatchMonad nel m,MonadResult nel ~ e el)
      => arr -> i -> nel -> m (e (ArrayType idx el))
store arr idx nel = embed $ (\arr' idx' nel' tp -> case tp arr' of
                                ArrayRepr idxTp elTp -> App (E.Store idxTp elTp) (arr' ::: nel' ::: idx')) <$>
                    embedM arr <*>
                    embedM idx <*>
                    embedM nel <*>
                    embedTypeOf
{-# INLINEABLE store #-}

-- | A specialized version of 'store' when the index is just a single element.
store1 :: (Embed m e,HasMonad arr,HasMonad idx,HasMonad el,
           MatchMonad arr m,MatchMonad idx m,MatchMonad el m,
           MonadResult arr ~ e (ArrayType '[idx'] el'),
           MonadResult idx ~ e idx',
           MonadResult el ~ e el')
        => arr -> idx -> el -> m (e (ArrayType '[idx'] el'))
store1 arr idx el = store arr (idx .:. nil) el
{-# INLINEABLE store1 #-}

-- | Create an array where every element is the same.
--   The following holds:
--
-- @
--    select (constArray tp e) i .==. e
-- @
constArray :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp)
           => List Repr idx -> a
           -> m (e (ArrayType idx tp))
constArray idx el = embed $ (\el' tp -> App (E.ConstArray idx (tp el')) (el' ::: Nil)) <$>
                    embedM el <*>
                    embedTypeOf
{-# INLINEABLE constArray #-}

concat' :: forall m e a b n1 n2.
           (Embed m e,HasMonad a,HasMonad b,
            MatchMonad a m,MatchMonad b m,
            MonadResult a ~ e (BitVecType n1),MonadResult b ~ e (BitVecType n2))
        => a -> b -> m (e (BitVecType (n1 TL.+ n2)))
concat' x y = embed $ f <$>
              embedM x <*>
              embedM y <*>
              embedTypeOf <*>
              embedTypeOf
  where
    f :: e (BitVecType n1) -> e (BitVecType n2)
      -> (e (BitVecType n1) -> Repr (BitVecType n1))
      -> (e (BitVecType n2) -> Repr (BitVecType n2))
      -> Expression v qv fun fv lv e (BitVecType (n1 TL.+ n2))
    f x' y' tp1 tp2 = case tp1 x' of
      BitVecRepr bw1 -> case tp2 y' of
        BitVecRepr bw2 -> App (E.Concat bw1 bw2) (x' ::: y' ::: Nil)
{-# INLINEABLE concat' #-}

extract' :: forall m e a bw start len.
            (Embed m e,HasMonad a,MatchMonad a m,
             MonadResult a ~ e (BitVecType bw),
             (start TL.+ len) TL.<= bw)
         => BitWidth start -> BitWidth len -> a
         -> m (e (BitVecType len))
extract' start len arg = embed $ f <$> embedM arg <*> embedTypeOf
  where
    f :: e (BitVecType bw) -> (e (BitVecType bw) -> Repr (BitVecType bw))
      -> Expression v qv fun fv lv e (BitVecType len)
    f arg' tp = case tp arg' of
      BitVecRepr bw -> App (E.Extract bw start len) (arg' ::: Nil)
{-# INLINEABLE extract' #-}

extractChecked :: forall m e a bw start len.
                  (Embed m e,HasMonad a,MatchMonad a m,TL.KnownNat start,TL.KnownNat len,
                   MonadResult a ~ e (BitVecType bw))
               => BitWidth start -> BitWidth len -> a
               -> m (e (BitVecType len))
extractChecked start len arg
  = embed $ f <$> embedM arg <*> embedTypeOf
  where
    f :: e (BitVecType bw) -> (e (BitVecType bw) -> Repr (BitVecType bw))
      -> Expression v qv fun fv lv e (BitVecType len)
    f arg' tp = case tp arg' of
      BitVecRepr bw
        | bwSize start + bwSize len <= bwSize bw
          -> App (E.Extract bw start len) (arg' ::: Nil)
        | otherwise -> error $ "extractChecked: Invalid parameters"
{-# INLINEABLE extractChecked #-}

extractUntypedStart :: forall m e a bw len.
                       (Embed m e,HasMonad a,MatchMonad a m,TL.KnownNat len,
                        MonadResult a ~ e (BitVecType bw))
                    => Integer -> BitWidth len -> a
                    -> m (e (BitVecType len))
extractUntypedStart start len arg = case TL.someNatVal start of
  Just (TL.SomeNat start') -> extractChecked (bw start') len arg
  Nothing -> error "extractUntypedStart: Negative start value"

extractUntyped :: forall m e a bw b.
                  (Embed m e,Monad m,HasMonad a,MatchMonad a m,
                    MonadResult a ~ e (BitVecType bw))
               => Integer -> Integer -> a
               -> (forall len. e (BitVecType len) -> m b)
               -> m b
extractUntyped start len arg f = case TL.someNatVal start of
  Just (TL.SomeNat start') -> case TL.someNatVal len of
    Just (TL.SomeNat len') -> do
      bv <- extractChecked (bw start') (bw len') arg
      f bv
    Nothing -> error "extractUntyped: Negative length"
  Nothing -> error "extractUntyped: Negative start value"

extractUntyped' :: forall m e a bw b.
                   (Embed m e,Monad m,HasMonad a,MatchMonad a m,
                    MonadResult a ~ e (BitVecType bw))
                => Integer -> Integer -> a
                -> (forall len. BitWidth len -> e (BitVecType len) -> m b)
                -> m b
extractUntyped' start len arg f
  = getBw start $
    \start' -> getBw len $
    \len' -> do
      bv <- extractChecked start' len' arg
      f len' bv

divisible :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e IntType)
          => Integer -> a -> m (e BoolType)
divisible n x = embed $ Divisible n <$> embedM x
{-# INLINEABLE divisible #-}

-- | Create the boolean expression "true".
true :: Embed m e => m (e BoolType)
true = embed $ pure $ E.Const (BoolValue True)
{-# INLINEABLE true #-}

-- | Create the boolean expression "false".
false :: Embed m e => m (e BoolType)
false = embed $ pure $ E.Const (BoolValue False)
{-# INLINEABLE false #-}

mk :: (Embed m e,HasMonad a,MatchMonad a m,
       MonadResult a ~ List e (Instantiated sig par),
       IsDatatype dt,List.Length par ~ Parameters dt)
   => Datatype dt -> List Repr par -> Constr dt sig -> a
   -> m (e (DataType dt par))
mk dt par con args = embed $ E.App (E.Constructor dt par con) <$>
                     embedM args
{-# INLINEABLE mk #-}

is :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e (DataType dt par),IsDatatype dt)
   => a -> Constr dt sig -> m (e BoolType)
is e con = embed $ (\re tp -> case tp re of
                       DataRepr dt par -> E.App (E.Test dt par con) ( re ::: Nil)
                   ) <$>
           embedM e <*>
           embedTypeOf
{-# INLINEABLE is #-}

(.#.) :: (Embed m e,HasMonad a,MatchMonad a m,
          MonadResult a ~ e (DataType dt par),IsDatatype dt)
      => a -> Field dt tp -> m (e (CType tp par))
(.#.) e f = embed $ (\re tp -> case tp re of
                        DataRepr dt par -> E.App (E.Field dt par f) (re ::: Nil)
                    ) <$>
            embedM e <*>
            embedTypeOf
{-# INLINEABLE (.#.) #-}

exists :: (Embed m e,Monad m) => List Repr tps
       -> (forall m e. (Embed m e,Monad m) => List e tps -> m (e BoolType))
       -> m (e BoolType)
exists tps f = embedQuantifier Exists tps (\vars -> do
                                              nvars <- List.traverse (\var -> embed $ pure $ QVar var) vars
                                              f nvars)

forall :: (Embed m e,Monad m) => List Repr tps
       -> (forall m e. (Embed m e,Monad m) => List e tps -> m (e BoolType))
       -> m (e BoolType)
forall tps f = embedQuantifier Forall tps (\vars -> do
                                              nvars <- List.traverse (\var -> embed $ pure $ QVar var) vars
                                              f nvars)

let' :: (Embed m e,Monad m,HasMonad a,MatchMonad a m,MonadResult a ~ e tp)
     => [LetBinding (EmLVar m e) e]
     -> a
     -> m (e tp)
let' args body = embed $ E.Let args <$> embedM body
