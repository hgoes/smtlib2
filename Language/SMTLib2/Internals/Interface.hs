module Language.SMTLib2.Internals.Interface
       (Same(),IsSMTNumber(),
        -- * Expressions
        pattern Var,
        -- ** Constants
        SMTType(),pattern ConstBool,pattern ConstInt,pattern ConstReal,pattern ConstBV,
        constant,asConstant,true,false,cbool,cint,creal,cbv,
        -- ** Functions
        pattern Fun,fun,(<:>),nil,
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
        pattern Div,pattern Mod,pattern Rem,div',mod',rem',
        pattern (:/:),(./.),
        pattern Abs,abs',
        -- *** Logic
        pattern Not,not',
        pattern LogicLst,pattern Logic,logic,
        pattern AndLst,pattern And,pattern (:&:),and',(.&.),
        pattern OrLst,pattern Or,pattern (:|:),or',(.|.),
        pattern XOrLst,pattern XOr,xor',
        pattern ImpliesLst,pattern Implies,pattern (:=>:),implies,(.=>.),
        -- *** Conversion
        pattern ToReal,pattern ToInt,toReal,toInt,
        -- *** If-then-else
        pattern ITE,ite,
        -- *** Bitvectors
        pattern BVComp,pattern BVULE,pattern BVULT,pattern BVUGE,pattern BVUGT,pattern BVSLE,pattern BVSLT,pattern BVSGE,pattern BVSGT,bvcomp,bvule,bvult,bvuge,bvugt,bvsle,bvslt,bvsge,bvsgt,
        pattern BVBin,pattern BVAdd,pattern BVSub,pattern BVMul,pattern BVURem,pattern BVSRem,pattern BVUDiv,pattern BVSDiv,pattern BVSHL,pattern BVLSHR,pattern BVASHR,pattern BVXor,pattern BVAnd,pattern BVOr,bvbin,bvadd,bvsub,bvmul,bvurem,bvsrem,bvudiv,bvsdiv,bvshl,bvlshr,bvashr,bvxor,bvand,bvor,
        pattern BVUn,pattern BVNot,pattern BVNeg,
        bvun,bvnot,bvneg,
        pattern Concat,pattern Extract,concat',extract',
        -- *** Arrays
        pattern Select,pattern Store,pattern ConstArray,select,select1,store,store1,constArray,
        -- *** Misc
        pattern Divisible,divisible
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
import Data.Ratio
import Data.GADT.Compare

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

class IsSMTNumber (tp :: Type) where
  smtNumRepr :: NumRepr tp
  smtFromInteger :: Integer -> Value con tp

instance IsSMTNumber IntType where
  smtNumRepr = NumInt
  smtFromInteger n = IntValue n

instance IsSMTNumber RealType where
  smtNumRepr = NumReal
  smtFromInteger n = RealValue (fromInteger n)

class HasMonad a where
  type MatchMonad a (m :: * -> *) :: Constraint
  type MonadResult a :: *
  embedM :: (Monad m,MatchMonad a m) => a -> m (MonadResult a)

instance HasMonad (e (tp::Type)) where
  type MatchMonad (e tp) m = ()
  type MonadResult (e tp) = e tp
  embedM = return

instance HasMonad ((m :: * -> *) (e (tp::Type))) where
  type MatchMonad (m (e tp)) m' = m ~ m'
  type MonadResult (m (e tp)) = e tp
  embedM = id

instance HasMonad (List e (tp::[Type])) where
  type MatchMonad (List e tp) m = ()
  type MonadResult (List e tp) = List e tp
  embedM = return

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

#if __GLASGOW_HASKELL__ >= 710
#define SEP ->
#define MK_SIG(PROV,REQ,NAME,LHS,RHS) pattern NAME :: PROV => REQ => LHS -> RHS
#else
#define SEP
#define MK_SIG(PROV,REQ,NAME,LHS,RHS) pattern PROV => NAME LHS :: REQ => RHS
#endif

MK_SIG((rtp ~ BoolType),(),ConstBool,Bool,Expression v qv fun con field fv lv e rtp)
pattern ConstBool x = E.Const (BoolValue x)

MK_SIG((rtp ~ IntType),(),ConstInt,Integer,Expression v qv fun con field fv lv e rtp)
pattern ConstInt x = E.Const (IntValue x)

MK_SIG((rtp ~ RealType),(),ConstReal,Rational,Expression v qv fun con field fv lv e rtp)
pattern ConstReal x = E.Const (RealValue x)

MK_SIG((rtp ~ BitVecType bw),(),ConstBV,Integer SEP (Natural bw),Expression v qv fun con field fv lv e rtp)
pattern ConstBV x bw = E.Const (BitVecValue x bw)

pattern Fun f arg = App (E.Fun f) arg

MK_SIG((rtp ~ BoolType),(),EqLstP,(Repr tp) SEP [e tp],Expression v qv fun con field fv lv e rtp)
pattern EqLstP tp lst <- App (E.Eq tp n) (allEqToList n -> lst) where
   EqLstP tp lst = allEqFromList lst (\n -> App (E.Eq tp n))

MK_SIG((rtp ~ BoolType),(GetType e),EqLst,[e tp],Expression v qv fun con field fv lv e rtp)
pattern EqLst lst <- EqLstP _ lst where
  EqLst lst@(x:_) = EqLstP (getType x) lst

MK_SIG((rtp ~ BoolType,Same tps),(GetType e),Eq,List e tps,Expression v qv fun con field fv lv e rtp)
pattern Eq lst <- App (E.Eq tp n) (allEqToSame' tp n -> Just (Dict,lst)) where
  Eq lst = sameApp E.Eq lst

MK_SIG((rtp ~ BoolType),(GetType e),(:==:),(e tp) SEP (e tp),Expression v qv fun con field fv lv e rtp)
pattern (:==:) x y <- App (E.Eq _ (Succ (Succ Zero))) (x ::: y ::: Nil) where
  (:==:) x y = App (E.Eq (getType x) (Succ (Succ Zero))) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType),(),DistinctLstP,(Repr tp) SEP [e tp],Expression v qv fun con field fv lv e rtp)
pattern DistinctLstP tp lst <- App (E.Distinct tp n) (allEqToList n -> lst) where
   DistinctLstP tp lst = allEqFromList lst (\n -> App (E.Distinct tp n))

MK_SIG((rtp ~ BoolType),(GetType e),DistinctLst,[e tp],Expression v qv fun con field fv lv e rtp)
pattern DistinctLst lst <- DistinctLstP _ lst where
  DistinctLst lst@(x:_) = DistinctLstP (getType x) lst

MK_SIG((rtp ~ BoolType,Same tps),(GetType e),Distinct,List e tps,Expression v qv fun con field fv lv e rtp)
pattern Distinct lst <- App (E.Distinct tp n) (allEqToSame' tp n -> Just (Dict,lst)) where
  Distinct lst = sameApp E.Distinct lst

MK_SIG((rtp ~ BoolType),(GetType e),(:/=:),(e tp) SEP (e tp),Expression v qv fun con field fv lv e rtp)
pattern (:/=:) x y <- App (E.Distinct _ (Succ (Succ Zero))) (x ::: y ::: Nil) where
  (:/=:) x y = App (E.Distinct (getType x) (Succ (Succ Zero))) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),Ord,E.OrdOp SEP (e tp) SEP (e tp),Expression v qv fun con field fv lv e rtp)
pattern Ord op x y <- App (E.Ord (matchNumRepr -> Dict) op) (x ::: y ::: Nil) where
  Ord op x y = App (E.Ord smtNumRepr op) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),(:>=:),(e tp) SEP (e tp),Expression v qv fun con field fv lv e rtp)
pattern (:>=:) x y <- App (E.Ord (matchNumRepr -> Dict) E.Ge) (x ::: y ::: Nil) where
  (:>=:) x y = App (E.Ord smtNumRepr E.Ge) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),(:>:),(e tp) SEP (e tp),Expression v qv fun con field fv lv e rtp)
pattern (:>:) x y <- App (E.Ord (matchNumRepr -> Dict) E.Gt) (x ::: y ::: Nil) where
  (:>:) x y = App (E.Ord smtNumRepr E.Gt) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),(:<=:),(e tp) SEP (e tp),Expression v qv fun con field fv lv e rtp)
pattern (:<=:) x y <- App (E.Ord (matchNumRepr -> Dict) E.Le) (x ::: y ::: Nil) where
  (:<=:) x y = App (E.Ord smtNumRepr E.Le) (x ::: y ::: Nil)

MK_SIG((rtp ~ BoolType,IsSMTNumber tp),(),(:<:),(e tp) SEP (e tp),Expression v qv fun con field fv lv e rtp)
pattern (:<:) x y <- App (E.Ord (matchNumRepr -> Dict) E.Lt) (x ::: y ::: Nil) where
  (:<:) x y = App (E.Ord smtNumRepr E.Lt) (x ::: y ::: Nil)

MK_SIG((),(),ArithLstP,E.ArithOp SEP (NumRepr tp) SEP [e tp],Expression v qv fun con field fv lv e tp)
pattern ArithLstP op tp lst <- App (E.Arith tp op n) (allEqToList n -> lst) where
  ArithLstP op tp lst = allEqFromList lst (\n -> App (E.Arith tp op n))

MK_SIG((IsSMTNumber tp),(),ArithLst,E.ArithOp SEP [e tp],Expression v qv fun con field fv lv e tp)
pattern ArithLst op lst <- ArithLstP op (matchNumRepr -> Dict) lst where
  ArithLst op lst = ArithLstP op smtNumRepr lst

MK_SIG((IsSMTNumber tp,Same tps,tp ~ SameType tps),(),Arith,E.ArithOp SEP (List e tps),Expression v qv fun con field fv lv e tp)
pattern Arith op lst <- App (E.Arith (matchNumRepr' -> (Dict,tp)) op n)
                        (allEqToSame' (numRepr tp) n -> Just (Dict,lst)) where
  Arith op lst = App (E.Arith smtNumRepr op (List.length lst)) (sameToAllEq lst)

pattern PlusLst lst = ArithLst E.Plus lst
pattern Plus lst = Arith E.Plus lst
pattern (:+:) x y = Plus (x ::: y ::: Nil)

pattern MinusLst lst = ArithLst E.Minus lst
pattern Minus lst = Arith E.Minus lst
pattern (:-:) x y = Minus (x ::: y ::: Nil)
pattern Neg x = Arith E.Minus (x ::: Nil)

pattern MultLst lst = ArithLst E.Mult lst
pattern Mult lst = Arith E.Mult lst
pattern (:*:) x y = Mult (x ::: y ::: Nil)

pattern Div x y = App (E.ArithIntBin E.Div) (x ::: y ::: Nil)
pattern Mod x y = App (E.ArithIntBin E.Mod) (x ::: y ::: Nil)
pattern Rem x y = App (E.ArithIntBin E.Rem) (x ::: y ::: Nil)

pattern (:/:) x y = App E.Divide (x ::: y ::: Nil)

MK_SIG((IsSMTNumber tp),(),Abs,e tp,Expression v qv fun con field fv lv e tp)
pattern Abs x <- App (E.Abs (matchNumRepr -> Dict)) (x ::: Nil) where
  Abs x = App (E.Abs smtNumRepr) (x ::: Nil)

pattern Not x = App E.Not (x ::: Nil)

MK_SIG((rtp ~ BoolType),(),LogicLst,E.LogicOp SEP [e BoolType],Expression v qv fun con field fv lv e rtp)
pattern LogicLst op lst <- App (E.Logic op n) (allEqToList n -> lst) where
  LogicLst op lst = allEqFromList lst (\n -> App (E.Logic op n))

MK_SIG((rtp ~ BoolType,Same tps,SameType tps ~ BoolType),(),Logic,E.LogicOp SEP (List e tps),Expression v qv fun con field fv lv e rtp)
pattern Logic op lst <- App (E.Logic op n) (allEqToSame' bool n -> Just (Dict,lst)) where
  Logic op lst = App (E.Logic op (List.length lst)) (sameToAllEq lst)

pattern AndLst lst = LogicLst E.And lst
pattern And lst = Logic E.And lst
MK_SIG((rtp ~ BoolType),(),(:&:),(e BoolType) SEP (e BoolType),Expression v qv fun con field fv lv e rtp)
pattern (:&:) x y = App (E.Logic E.And (Succ (Succ Zero))) (x ::: y ::: Nil)

pattern OrLst lst = LogicLst E.Or lst
pattern Or lst = Logic E.Or lst
MK_SIG((rtp ~ BoolType),(),(:|:),(e BoolType) SEP (e BoolType),Expression v qv fun con field fv lv e rtp)
pattern (:|:) x y = App (E.Logic E.Or (Succ (Succ Zero))) (x ::: y ::: Nil)

pattern XOrLst lst = LogicLst E.XOr lst
pattern XOr lst = Logic E.XOr lst

pattern ImpliesLst lst = LogicLst E.Implies lst
pattern Implies lst = Logic E.Implies lst
MK_SIG((rtp ~ BoolType),(),(:=>:),(e BoolType) SEP (e BoolType),Expression v qv fun con field fv lv e rtp)
pattern (:=>:) x y = App (E.Logic E.Implies (Succ (Succ Zero))) (x ::: y ::: Nil)

pattern ToReal x = App E.ToReal (x ::: Nil)
pattern ToInt x = App E.ToInt (x ::: Nil)

MK_SIG((),(GetType e),ITE,(e BoolType) SEP (e tp) SEP (e tp),Expression v qv fun con field fv lv e tp)
pattern ITE c ifT ifF <- App (E.ITE _) (c ::: ifT ::: ifF ::: Nil) where
  ITE c ifT ifF = App (E.ITE (getType ifT)) (c ::: ifT ::: ifF ::: Nil)

MK_SIG((rtp ~ BoolType),(GetType e),BVComp,E.BVCompOp SEP (e (BitVecType bw)) SEP (e (BitVecType bw)),Expression v qv fun con field fv lv e rtp)
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

MK_SIG((rtp ~ BitVecType bw),(GetType e),BVBin,E.BVBinOp SEP (e (BitVecType bw)) SEP (e (BitVecType bw)),Expression v qv fun con field fv lv e rtp)
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

MK_SIG((rtp ~ BitVecType bw),(GetType e),BVUn,E.BVUnOp SEP (e (BitVecType bw)),Expression v qv fun con field fv lv e rtp)
pattern BVUn op x <- App (E.BVUn op _) (x ::: Nil) where
  BVUn op x = App (E.BVUn op (getBW x)) (x ::: Nil)

pattern BVNot x = BVUn E.BVNot x
pattern BVNeg x = BVUn E.BVNeg x

MK_SIG((rtp ~ val),(GetType e),Select,(e (ArrayType idx val)) SEP (List e idx),Expression v qv fun con field fv lv e rtp)
pattern Select arr idx <- App (E.Select _ _) (arr ::: idx) where
  Select arr idx = case getType arr of
    ArrayRepr idxTp elTp -> App (E.Select idxTp elTp) (arr ::: idx)

MK_SIG((rtp ~ ArrayType idx val),(GetType e),Store,(e (ArrayType idx val)) SEP (List e idx) SEP (e val),Expression v qv fun con field fv lv e rtp)
pattern Store arr idx el <- App (E.Store _ _) (arr ::: el ::: idx) where
  Store arr idx el = case getType arr of
    ArrayRepr idxTp elTp -> App (E.Store idxTp elTp) (arr ::: el ::: idx)

MK_SIG((rtp ~ ArrayType idx val),(GetType e),ConstArray,(List Repr idx) SEP (e val),Expression v qv fun con field fv lv e rtp)
pattern ConstArray idx el <- App (E.ConstArray idx _) (el ::: Nil) where
  ConstArray idx el = App (E.ConstArray idx (getType el)) (el ::: Nil)

MK_SIG((rtp ~ BitVecType (n1+n2)),(GetType e),Concat,(e (BitVecType n1)) SEP (e (BitVecType n2)),Expression v qv fun con field fv lv e rtp)
pattern Concat lhs rhs <- App (E.Concat _ _) (lhs :::rhs ::: Nil) where
  Concat lhs rhs = case getType lhs of
    BitVecRepr n1 -> case getType rhs of
      BitVecRepr n2 -> App (E.Concat n1 n2) (lhs ::: rhs ::: Nil)

MK_SIG((rtp ~ BitVecType len,((start + len) <= bw) ~ True),(GetType e),Extract,(Natural start) SEP (Natural len) SEP (e (BitVecType bw)),Expression v qv fun con field fv lv e rtp)
pattern Extract start len arg <- App (E.Extract _ start len) (arg ::: Nil) where
  Extract start len arg = case getType arg of
    BitVecRepr bw -> App (E.Extract bw start len) (arg ::: Nil)

MK_SIG((rtp ~ BoolType),(),Divisible,Integer SEP (e IntType),Expression v qv fun con field fv lv e rtp)
pattern Divisible n e = App (E.Divisible n) (e ::: Nil)

sameApp :: (Same tps,GetType e)
        => (Repr (SameType tps) -> Natural (List.Length tps)
            -> E.Function fun con field '(AllEq (SameType tps) (List.Length tps),ret))
        -> List e tps
        -> Expression v qv fun con field fv lv e ret
sameApp f lst = App (f (sameType $ runIdentity $
                        List.mapM (return.getType) lst
                       ) (List.length lst))
                (sameToAllEq lst)

getBW :: GetType e => e (BitVecType bw) -> Natural bw
getBW e = case getType e of
  BitVecRepr bw -> bw

class SMTType t where
  type SMTReprType t :: Type
  toSMTConst :: t -> Value con (SMTReprType t)
  fromSMTConst :: Value con (SMTReprType t) -> t

instance SMTType Bool where
  type SMTReprType Bool = BoolType
  toSMTConst = BoolValue
  fromSMTConst (BoolValue x) = x

instance SMTType Integer where
  type SMTReprType Integer = IntType
  toSMTConst = IntValue
  fromSMTConst (IntValue x) = x

instance SMTType (Ratio Integer) where
  type SMTReprType (Ratio Integer) = RealType
  toSMTConst = RealValue
  fromSMTConst (RealValue x) = x

data BitVec bw = BitVec { bitVecValue :: Integer
                        , bitVecWidth :: Natural bw } deriving (Eq,Ord,Show)

instance SMTType (BitVec bw) where
  type SMTReprType (BitVec bw) = BitVecType bw
  toSMTConst (BitVec val sz) = BitVecValue val sz
  fromSMTConst (BitVecValue val sz) = BitVec val sz

{- XXX: This doesn't work in 7.10. Test it when 8.0 is out.

pattern Const :: (SMTType ctp,rtp ~ (SMTReprType ctp)) => ctp
              -> Expression v qv fun con field fv lv e rtp
pattern Const v <- E.Const (fromSMTConst -> v) where
  Const v = E.Const (toSMTConst v) -}

--constant :: SMTType tp => tp -> Expression v qv fun con field fv lv e (SMTReprType tp)
--constant x = E.Const (toSMTConst x)

constant :: (Embed m e,SMTType tp) => tp -> m (e (SMTReprType tp))
constant x = embed $ E.Const (toSMTConst x)

cbool :: Embed m e => Bool -> m (e BoolType)
cbool x = embed $ E.Const (BoolValue x)

cint :: Embed m e => Integer -> m (e IntType)
cint x = embed $ E.Const (IntValue x)

creal :: Embed m e => Rational -> m (e RealType)
creal x = embed $ E.Const (RealValue x)

cbv :: Embed m e => Integer -> Natural bw -> m (e (BitVecType bw))
cbv i bw = embed $ E.Const (BitVecValue i bw)

asConstant :: SMTType tp => Expression v qv fun con field fv lv e (SMTReprType tp) -> Maybe tp
asConstant (E.Const v) = Just $ fromSMTConst v
asConstant _ = Nothing

MK_SIG((tp ~ rtp),(),Var,(v tp),Expression v qv fun con field fv lv e rtp)
pattern Var x = E.Var x

fun :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ List e args)
    => EmFun m e '(args,res) -> a -> m (e res)
fun fun args = do
  args' <- embedM args
  embed (App (E.Fun fun) args')
{-# INLINEABLE fun #-}

(<:>) :: (HasMonad a,MonadResult a ~ e tp,MatchMonad a m,Monad m)
      => a -> m (List e tps) -> m (List e (tp ': tps))
(<:>) x xs = do
  x' <- embedM x
  xs' <- xs
  return (x' ::: xs')
{-# INLINEABLE (<:>) #-}

infixr 5 <:>

nil :: Monad m => m (List e '[])
nil = return Nil

(.==.) :: (Embed m e,HasMonad a,HasMonad b,
           MatchMonad a m,MatchMonad b m,
           MonadResult a ~ e tp,MonadResult b ~ e tp)
       => a -> b -> m (e BoolType)
(.==.) lhs rhs = do
  lhs' <- embedM lhs
  rhs' <- embedM rhs
  tp <- embedTypeOf lhs'
  embed $ App (E.Eq tp (Succ (Succ Zero))) (lhs' ::: rhs' ::: Nil)
{-# INLINEABLE (.==.) #-}

(./=.) :: (Embed m e,HasMonad a,HasMonad b,
           MatchMonad a m,MatchMonad b m,
           MonadResult a ~ e tp,MonadResult b ~ e tp)
       => a -> b -> m (e BoolType)
(./=.) lhs rhs = do
  lhs' <- embedM lhs
  rhs' <- embedM rhs
  tp <- embedTypeOf lhs'
  embed $ App (E.Distinct tp (Succ (Succ Zero))) (lhs' ::: rhs' ::: Nil)
{-# INLINEABLE (./=.) #-}

infix 4 .==., ./=.

eq :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp)
   => [a] -> m (e BoolType)
eq [] = embed (E.Const (BoolValue True))
eq xs = do
  xs'@(x:_) <- mapM embedM xs
  tp <- embedTypeOf x
  allEqFromList xs' $ \n -> embed.(App (E.Eq tp n))
{-# INLINEABLE eq #-}

distinct :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp)
         => [a] -> m (e BoolType)
distinct [] = embed (E.Const (BoolValue True))
distinct xs = do
  xs'@(x:_) <- mapM embedM xs
  tp <- embedTypeOf x
  allEqFromList xs' $ \n -> embed.(App (E.Distinct tp n))
{-# INLINEABLE distinct #-}

map' :: (Embed m e,HasMonad arg,MatchMonad arg m,MonadResult arg ~ List e (Lifted tps idx),
         Unlift tps idx,GetType e,GetFunType (EmFun m e),GetFieldType (EmField m e),GetConType (EmConstr m e))
     => E.Function (EmFun m e) (EmConstr m e) (EmField m e) '(tps,res)
     -> arg
     -> m (e (ArrayType idx res))
map' f arg = do
  arg' <- embedM arg
  let (tps,res) = getFunType f
      idx = unliftTypeWith (getTypes arg') tps
  embed $ E.App (E.Map idx f) arg'
{-# INLINEABLE map' #-}

ord :: (Embed m e,IsSMTNumber tp,HasMonad a,HasMonad b,
        MatchMonad a m,MatchMonad b m,
        MonadResult a ~ e tp,MonadResult b ~ e tp)
    => E.OrdOp -> a -> b -> m (e BoolType)
ord op lhs rhs = do
  lhs' <- embedM lhs
  rhs' <- embedM rhs
  embed $ Ord op lhs' rhs'
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
arith op xs = mapM embedM xs >>= embed.(ArithLst op)
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
(.+.) x y = do
  x' <- embedM x
  y' <- embedM y
  embed $ x' :+: y'
(.-.) x y = do
  x' <- embedM x
  y' <- embedM y
  embed $ x' :-: y'
(.*.) x y = do
  x' <- embedM x
  y' <- embedM y
  embed $ x' :*: y'
{-# INLINEABLE (.+.) #-}
{-# INLINEABLE (.-.) #-}
{-# INLINEABLE (.*.) #-}

infixl 6 .+.,.-.
infixl 7 .*.

neg :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp,IsSMTNumber tp)
    => a -> m (e tp)
neg x = do
  x' <- embedM x
  embed $ Neg x'
{-# INLINEABLE neg #-}

abs' :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp,IsSMTNumber tp)
     => a -> m (e tp)
abs' x = do
  x' <- embedM x
  embed $ Abs x'
{-# INLINEABLE abs' #-}

instance (Embed m e) => Num (m (e IntType)) where
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
    embed $ App (E.ITE real) (gtZero ::: one ::: cond1 ::: Nil)

rem',div',mod' :: (Embed m e,HasMonad a,HasMonad b,
                   MatchMonad a m,MatchMonad b m,
                   MonadResult a ~ e IntType,MonadResult b ~ e IntType)
               => a -> b -> m (e IntType)
rem' x y = do
  x' <- embedM x
  y' <- embedM y
  embed $ Rem x' y'
div' x y = do
  x' <- embedM x
  y' <- embedM y
  embed $ Div x' y'
mod' x y = do
  x' <- embedM x
  y' <- embedM y
  embed $ Mod x' y'
{-# INLINEABLE rem' #-}
{-# INLINEABLE div' #-}
{-# INLINEABLE mod' #-}

infixl 7 `div'`, `rem'`, `mod'`

(./.) :: (Embed m e,HasMonad a,HasMonad b,MatchMonad a m,MatchMonad b m,
          MonadResult a ~ e RealType,MonadResult b ~ e RealType)
      => a -> b -> m (e RealType)
(./.) x y = do
  x' <- embedM x
  y' <- embedM y
  embed $ x' :/: y'
{-# INLINEABLE (./.) #-}

infixl 7 ./.

instance Embed m e => Fractional (m (e RealType)) where
  (/) x y = do
    x' <- x
    y' <- y
    embed $ x' :/: y'
  fromRational r = embed $ E.Const $ RealValue r

not' :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e BoolType)
     => a -> m (e BoolType)
not' x = embedM x >>= embed.Not
{-# INLINEABLE not' #-}

logic :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e BoolType)
      => E.LogicOp -> [a] -> m (e BoolType)
logic op lst = mapM embedM lst >>= embed.(LogicLst op)
{-# INLINEABLE logic #-}

and',or',xor',implies :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e BoolType)
                      => [a] -> m (e BoolType)
and' xs = mapM embedM xs >>= embed.AndLst
or' xs = mapM embedM xs >>= embed.OrLst
xor' xs = mapM embedM xs >>= embed.XOrLst
implies xs = mapM embedM xs >>= embed.ImpliesLst
{-# INLINEABLE and' #-}
{-# INLINEABLE or' #-}
{-# INLINEABLE xor' #-}
{-# INLINEABLE implies #-}

(.&.),(.|.),(.=>.) :: (Embed m e,HasMonad a,HasMonad b,
                       MatchMonad a m,MatchMonad b m,
                       MonadResult a ~ e BoolType,MonadResult b ~ e BoolType)
                   => a -> b -> m (e BoolType)
(.&.) x y = do
  x' <- embedM x
  y' <- embedM y
  embed (x' :&: y')
(.|.) x y = do
  x' <- embedM x
  y' <- embedM y
  embed (x' :|: y')
(.=>.) x y = do
  x' <- embedM x
  y' <- embedM y
  embed (x' :=>: y')
{-# INLINEABLE (.&.) #-}
{-# INLINEABLE (.|.) #-}
{-# INLINEABLE (.=>.) #-}

infixr 3 .&.
infixr 2 .|.
infixr 2 .=>.

toReal :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e IntType)
       => a -> m (e RealType)
toReal x = embedM x >>= embed.ToReal
{-# INLINEABLE toReal #-}

toInt :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e RealType)
      => a -> m (e IntType)
toInt x = embedM x >>= embed.ToInt
{-# INLINEABLE toInt #-}

ite :: (Embed m e,HasMonad a,HasMonad b,HasMonad c,
        MatchMonad a m,MatchMonad b m,MatchMonad c m,
        MonadResult a ~ e BoolType,MonadResult b ~ e tp,MonadResult c ~ e tp)
    => a -> b -> c -> m (e tp)
ite c ifT ifF = do
  c' <- embedM c
  ifT' <- embedM ifT
  ifF' <- embedM ifF
  tp <- embedTypeOf ifT'
  embed $ App (E.ITE tp) (c' ::: ifT' ::: ifF' ::: Nil)
{-# INLINEABLE ite #-}

bvcomp :: forall m e a b bw.
          (Embed m e,HasMonad a,HasMonad b,
           MatchMonad a m,MatchMonad b m,
           MonadResult a ~ e (BitVecType bw),MonadResult b ~ e (BitVecType bw))
       => E.BVCompOp -> a -> b -> m (e BoolType)
bvcomp op x y = do
  (x' :: e (BitVecType bw)) <- embedM x
  (y' :: e (BitVecType bw)) <- embedM y
  BitVecRepr bw <- embedTypeOf x'
  embed $ App (E.BVComp op bw) (x' ::: y' ::: Nil)
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
bvbin op x y = do
  (x' :: e (BitVecType bw)) <- embedM x
  (y' :: e (BitVecType bw)) <- embedM y
  BitVecRepr bw <- embedTypeOf x'
  embed $ App (E.BVBin op bw) (x' ::: y' ::: Nil)
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
bvun op x = do
  (x' :: e (BitVecType bw)) <- embedM x
  BitVecRepr bw <- embedTypeOf x'
  embed $ App (E.BVUn op bw) (x' ::: Nil)
{-# INLINEABLE bvun #-}

bvnot,bvneg :: (Embed m e,HasMonad a,
                MatchMonad a m,
                MonadResult a ~ e (BitVecType bw))
            => a -> m (e (BitVecType bw))
bvnot = bvun E.BVNot
bvneg = bvun E.BVNeg
{-# INLINEABLE bvnot #-}
{-# INLINEABLE bvneg #-}

select :: (Embed m e,HasMonad arr,MatchMonad arr m,MonadResult arr ~ e (ArrayType idx el),
           HasMonad i,MatchMonad i m,MonadResult i ~ List e idx)
       => arr -> i -> m (e el)
select arr idx = do
  arr' <- embedM arr
  idx' <- embedM idx
  ArrayRepr idxTp elTp <- embedTypeOf arr'
  embed (App (E.Select idxTp elTp) (arr' ::: idx'))
{-# INLINEABLE select #-}

select1 :: (Embed m e,HasMonad arr,HasMonad idx,
            MatchMonad arr m,MatchMonad idx m,
            MonadResult arr ~ e (ArrayType '[idx'] el),
            MonadResult idx ~ e idx')
        => arr -> idx -> m (e el)
select1 arr idx = do
  arr' <- embedM arr
  idx' <- embedM idx
  ArrayRepr (idxTp ::: Nil) elTp <- embedTypeOf arr'
  embed $ App (E.Select (idxTp ::: Nil) elTp) (arr' ::: idx' ::: Nil)
{-# INLINEABLE select1 #-}

store :: (Embed m e,HasMonad arr,MatchMonad arr m,MonadResult arr ~ e (ArrayType idx el),
          HasMonad i,MatchMonad i m,MonadResult i ~ List e idx,
          HasMonad nel,MatchMonad nel m,MonadResult nel ~ e el)
      => arr -> i -> nel -> m (e (ArrayType idx el))
store arr idx nel = do
  arr' <- embedM arr
  idx' <- embedM idx
  nel' <- embedM nel
  ArrayRepr idxTp elTp <- embedTypeOf arr'
  embed (App (E.Store idxTp elTp) (arr' ::: nel' ::: idx'))
{-# INLINEABLE store #-}

store1 :: (Embed m e,HasMonad arr,HasMonad idx,HasMonad el,
           MatchMonad arr m,MatchMonad idx m,MatchMonad el m,
           MonadResult arr ~ e (ArrayType '[idx'] el'),
           MonadResult idx ~ e idx',
           MonadResult el ~ e el')
        => arr -> idx -> el -> m (e (ArrayType '[idx'] el'))
store1 arr idx el = do
  arr' <- embedM arr
  idx' <- embedM idx
  el' <- embedM el
  ArrayRepr (idxTp ::: Nil) elTp <- embedTypeOf arr'
  embed $ App (E.Store (idxTp ::: Nil) elTp) (arr' ::: el' ::: idx' ::: Nil)
{-# INLINEABLE store1 #-}

constArray :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e tp)
           => List Repr idx -> a
           -> m (e (ArrayType idx tp))
constArray idx el = do
  el' <- embedM el
  tp <- embedTypeOf el'
  embed (App (E.ConstArray idx tp) (el' ::: Nil))
{-# INLINEABLE constArray #-}

concat' :: forall m e a b n1 n2.
           (Embed m e,HasMonad a,HasMonad b,
            MatchMonad a m,MatchMonad b m,
            MonadResult a ~ e (BitVecType n1),MonadResult b ~ e (BitVecType n2))
        => a -> b -> m (e (BitVecType (n1 + n2)))
concat' x y = do
  (x'::e (BitVecType n1)) <- embedM x
  (y'::e (BitVecType n2)) <- embedM y
  BitVecRepr bw1 <- embedTypeOf x'
  BitVecRepr bw2 <- embedTypeOf y'
  embed $ App (E.Concat bw1 bw2) (x' ::: y' ::: Nil)
{-# INLINEABLE concat' #-}

extract' :: forall m e a bw start len.
            (Embed m e,HasMonad a,MatchMonad a m,
             MonadResult a ~ e (BitVecType bw),
             ((start + len) <= bw) ~ True)
         => Natural start -> Natural len -> a
         -> m (e (BitVecType len))
extract' start len arg = do
  (arg'::e (BitVecType bw)) <- embedM arg
  BitVecRepr bw <- embedTypeOf arg'
  embed (App (E.Extract bw start len) (arg' ::: Nil))
{-# INLINEABLE extract' #-}

divisible :: (Embed m e,HasMonad a,MatchMonad a m,MonadResult a ~ e IntType)
          => Integer -> a -> m (e BoolType)
divisible n x = embedM x >>= embed.(Divisible n)
{-# INLINEABLE divisible #-}

true,false :: Embed m e => m (e BoolType)
true = embed $ E.Const (BoolValue True)
false = embed $ E.Const (BoolValue False)
{-# INLINEABLE true #-}
{-# INLINEABLE false #-}
