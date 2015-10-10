{-# LANGUAGE TemplateHaskell #-}
{- | Example usage: This program tries to find two numbers greater than zero which sum up to 5.

     @
import Language.SMTLib2
import Language.SMTLib2.Solver

program :: SMT (Integer,Integer)
program = do
  x <- var
  y <- var
  assert $ (plus [x,y]) .==. (constant 5)
  assert $ x .>. (constant 0)
  assert $ y .>. (constant 0)
  checkSat
  vx <- getValue x
  vy <- getValue y
  return (vx,vy)

main = withZ3 program >>= print
     @ -}
module Language.SMTLib2 (
  B.Backend(SMTMonad,ClauseId),
  L.withBackend,
  SMT(),SMTExpr(),Type(..),analyze,L.setOption,B.SMTOption(..),
  declare,TH.expr,assert,assertId,L.CheckSatResult(..),L.checkSat,getValue,KnownNat(),
  L.Partition(..),
  assertPartition,
  interpolate,L.getUnsatCore,
  L.registerDatatype,
  -- * Expressions
  -- ** Constants
  constant,
  -- ** Comparison
  (.==.),(./=.),
  (.<.),(.<=.),(.>.),(.>=.),
  -- ** Basic logic
  ite,
  -- ** Arithmetic
  (.+.),(.-.),(.*.),abs'
  ) where

import qualified Language.SMTLib2.Internals.Backend as B
import qualified Language.SMTLib2.LowLevel as L
import Language.SMTLib2.Internals.Expression as E
import qualified Language.SMTLib2.Internals.TH as TH
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Monad

import Control.Monad.Identity (runIdentity)
import Control.Monad.State.Strict (get)
import qualified Data.IntMap as IMap
import Data.Type.Equality
import Data.GADT.Compare
import Data.GADT.Show
import Data.Proxy
import Data.Typeable
import Language.Haskell.TH.Quote

data AnyQVar b = forall t. GetType t => AnyQVar (B.QVar b t)

data SMTExpr b t where
  SMTExpr :: Expression (B.Var b)
                        (B.QVar b)
                        (B.Fun b)
                        (B.Constr b)
                        (B.Field b)
                        (B.FunArg b)
                        (SMTExpr b) t
          -> SMTExpr b t
  SpecialExpr :: SMTExpr' b t -> SMTExpr b t

data SMTExpr' b t where
  QVar' :: GetType t => Int -> !Int -> SMTExpr' b t
  Quantification' :: GetTypes arg => Quantifier -> Int -> Args Proxy arg
                  -> SMTExpr b BoolType
                  -> SMTExpr' b BoolType
  TestConstr :: IsDatatype dt => String -> Proxy (dt:: *) -> SMTExpr b (DataType dt) -> SMTExpr' b BoolType
  GetField :: (IsDatatype dt,GetType tp)
           => String -> String -> Proxy (dt :: *) -> Proxy tp
           -> SMTExpr b (DataType dt) -> SMTExpr' b tp
  Const' :: (ToSMT tp,FromSMT (ValueRepr tp),ValueType (ValueRepr tp) ~ tp)
         => tp -> SMTExpr' b (ValueRepr tp)

instance B.Backend b => Show (SMTExpr' b t) where
  showsPrec p (QVar' lvl n) = showParen (p>10) $
                              showString "QVar' " .
                              showsPrec 11 lvl .
                              showChar ' ' .
                              showsPrec 11 n
  showsPrec p (Quantification' q lvl args body)
    = showParen (p>10) $
      showString "Quantification' " .
      showsPrec 11 q . showChar ' ' .
      showsPrec 11 lvl . showChar ' ' .
      showsPrec 11 (length (argsToList (const ()) args)) . showChar ' ' .
      showsPrec 11 body
  showsPrec p (Const' c) = showParen (p>10) $
                           showString "Const' " .
                           showsPrec 11 c

instance B.Backend b => GShow (SMTExpr' b) where
  gshowsPrec = showsPrec

instance B.Backend b => GEq (SMTExpr b) where
  geq (SMTExpr x) (SMTExpr y) = geq x y
  geq (SpecialExpr x) (SpecialExpr y) = geq x y
  geq _ _ = Nothing

instance B.Backend b => GEq (SMTExpr' b) where
  geq v1@(QVar' lvl1 nr1) v2@(QVar' lvl2 nr2)
    = if (lvl1,nr1) == (lvl2,nr2)
      then case v1 of
             (_::SMTExpr' b t1) -> case v2 of
               (_::SMTExpr' b t2) -> do
                 Refl <- eqT :: Maybe (t1 :~: t2)
                 return Refl
      else Nothing
  geq (Quantification' q1 lvl1 (_::Args Proxy args1) body1)
      (Quantification' q2 lvl2 (_::Args Proxy args2) body2)
    | (q1,lvl1) == (q2,lvl2) = do
        Refl <- geq (getTypes::Args Repr args1)
                    (getTypes::Args Repr args2)
        Refl <- geq body1 body2
        return Refl
    | otherwise = Nothing
  geq (TestConstr name1 _ body1) (TestConstr name2 _ body2)
    | name1==name2 = do
      Refl <- geq body1 body2
      return Refl
    | otherwise = Nothing
  geq (GetField cname1 fname1 _ (_::Proxy t1) body1)
      (GetField cname2 fname2 _ (_::Proxy t2) body2)
    | (cname1,fname1) == (cname2,fname2) = do
        Refl <- eqT :: Maybe (t1 :~: t2)
        Refl <- geq body1 body2
        return Refl
    | otherwise = Nothing
  geq (Const' c1 :: SMTExpr' b t1) (Const' c2 :: SMTExpr' b t2) = do
    Refl <- eqT :: Maybe (t1 :~: t2)
    if c1 == castWith Refl c2
      then Just Refl
      else Nothing
  geq _ _ = Nothing

instance B.Backend b => GCompare (SMTExpr b) where
  gcompare (SMTExpr x) (SMTExpr y) = gcompare x y
  gcompare (SMTExpr _) _ = GLT
  gcompare _ (SMTExpr _) = GGT
  gcompare (SpecialExpr e1) (SpecialExpr e2) = gcompare e1 e2

instance B.Backend b => GCompare (SMTExpr' b) where
  gcompare q1@(QVar' lvl1 nr1) q2@(QVar' lvl2 nr2)
    = case compare (lvl1,nr1) (lvl2,nr2) of
        EQ -> case q1 of
          (_::SMTExpr' b t1) -> case q2 of
            (_::SMTExpr' b t2) -> gcompare (getType::Repr t1)
                                           (getType::Repr t2)
        LT -> GLT
        GT -> GGT
  gcompare (QVar' _ _) _ = GLT
  gcompare _ (QVar' _ _) = GGT
  gcompare e1@(Quantification' q1 lvl1 args1 body1) e2@(Quantification' q2 lvl2 args2 body2)
    = case compare (q1,lvl1) (q2,lvl2) of
        EQ -> case e1 of
          (_::SMTExpr' b t1) -> case e2 of
            (_::SMTExpr' b t2) -> gcompare (getType::Repr t1)
                                           (getType::Repr t2)
        GT -> GGT
        LT -> GLT
  gcompare Quantification' {} _ = GLT
  gcompare _ Quantification' {} = GGT
  gcompare (TestConstr name1 _ body1) (TestConstr name2 _ body2) = case compare name1 name2 of
    EQ -> case gcompare body1 body2 of
      GEQ -> GEQ
      GLT -> GLT
      GGT -> GGT
    LT -> GLT
    GT -> GGT
  gcompare TestConstr {} _ = GLT
  gcompare _ TestConstr {} = GGT
  gcompare (GetField cname1 fname1 _ (Proxy::Proxy t1) body1)
           (GetField cname2 fname2 _ (Proxy::Proxy t2) body2)
    = case compare (cname1,fname1) (cname2,fname2) of
        EQ -> case gcompare body1 body2 of
          GEQ -> case eqT :: Maybe (t1 :~: t2) of
            Just Refl -> GEQ
          GLT -> GLT
          GGT -> GGT
        LT -> GLT
        GT -> GGT
  gcompare GetField {} _ = GLT
  gcompare _ GetField {} = GGT
  gcompare (Const' c1 :: SMTExpr' b t1) (Const' c2 :: SMTExpr' b t2)
    = case eqT :: Maybe (t1 :~: t2) of
      Just Refl -> case compare c1 (castWith Refl c2) of
        EQ -> GEQ
        LT -> GLT
        GT -> GGT
      Nothing -> case compare (typeOf c1) (typeOf c2) of
        LT -> GLT
        GT -> GGT

instance B.Backend b => Show (SMTExpr b t) where
  showsPrec p (SMTExpr e) = showsPrec p e
  showsPrec p (SpecialExpr e) = showsPrec p e

instance B.Backend b => GShow (SMTExpr b) where
  gshowsPrec = showsPrec

instance B.Backend b => Embed (SMTExpr b) where
  type EmbedBackend (SMTExpr b) = b
  type EmbedSub (SMTExpr b) = SMTExpr' b
  embed = SMTExpr
  embedQuantifier q (f::Args (SMTExpr b) arg -> SMTExpr b BoolType)
    = SpecialExpr (Quantification' q level qargs body)
    where
      body = f args
      level = getLevel body
      --level = 0
      args = mkArg 0 (getTypes::Args Repr arg)
      qargs = runIdentity $ mapArgs (\_ -> return Proxy) args

      mkArg :: Int -> Args Repr arg' -> Args (SMTExpr b) arg'
      mkArg n NoArg = NoArg
      mkArg n (Arg _ xs) = Arg (SpecialExpr $ QVar' level n) (mkArg (n+1) xs)

      getLevel :: SMTExpr b t -> Int
      getLevel (SMTExpr (App _ args)) = maximum $ argsToList getLevel args
      getLevel (SMTExpr (Let bind body))
        = maximum $ getLevel body:argsToList (getLevel . letExpr) bind
      getLevel (SpecialExpr e) = case e of
        Quantification' _ lvl _ _ -> lvl+1
        TestConstr _ _ dt -> getLevel dt
        GetField _ _ _ _ dt -> getLevel dt
        _ -> 0
      getLevel _ = 0
  embedConstant = SpecialExpr . Const'
  embedConstrTest name pr e = SpecialExpr (TestConstr name pr e)
  embedGetField name conName prDt prTp e = SpecialExpr (GetField name conName prDt prTp e)
  extract (SMTExpr e) = Left e
  extract (SpecialExpr e) = Right e

  encodeSub pr e = encode' pr IMap.empty (SpecialExpr e)
    where
      encode' :: (Embed e,GetType tp)
              => Proxy e
              -> IMap.IntMap [AnyQVar (EmbedBackend e)]
              -> SMTExpr (EmbedBackend e) tp
              -> SMT (EmbedBackend e) (B.Expr (EmbedBackend e) tp)
      encode' pr mp (SpecialExpr (Quantification' q lvl vars body)) = do
        (lst,qarg) <- declareQVars pr vars
        let nmp = IMap.insert lvl lst mp
        body' <- encode' pr nmp body
        L.updateBackend $ \b -> B.toBackend b (Quantification q qarg body')
      encode' _ mp (SpecialExpr (QVar' lvl nr)) = case IMap.lookup lvl mp of
        Just vars -> case vars!!nr of
          AnyQVar qv -> case gcast qv of
            Just qv' -> L.updateBackend $ \b -> B.toBackend b (QVar qv')
      encode' pr mp (SpecialExpr (TestConstr con dt expr)) = do
        st <- get
        lookupDatatypeCon dt con (datatypes st) $
          \rcon -> do
               expr' <- encode' pr mp expr
               let res = App (Test $ B.bconRepr rcon) (Arg expr' NoArg)
               L.updateBackend $ \b -> B.toBackend b res
      encode' pr mp (SpecialExpr (GetField field con dt (_::Proxy tp) expr)) = do
        st <- get
        lookupDatatypeField dt con field (datatypes st) $
          \rfield -> case gcast rfield of
             Just rfield' -> do
               expr' <- encode' pr mp expr
               let res = App (E.Field $ B.bfieldRepr rfield') (Arg expr' NoArg)
               L.updateBackend $ \b -> B.toBackend b res
      encode' pr mp (SpecialExpr (Const' c)) = do
        st <- get
        L.updateBackend $ \b -> B.toBackend b (Const $ toValue (datatypes st) c)
      encode' pr mp (SMTExpr e) = do
        e' <- L.mapSubExpressions (encode' pr mp) e
        L.updateBackend $ \b -> B.toBackend b e'

      declareQVars :: Embed e => Proxy e -> Args Proxy arg
                   -> SMT (EmbedBackend e) ([AnyQVar (EmbedBackend e)],
                                            Args (B.QVar (EmbedBackend e)) arg)
      declareQVars _ NoArg = return ([],NoArg)
      declareQVars pr (Arg _ args) = do
        qvar <- L.updateBackend (`B.createQVar` Nothing)
        (lst,args') <- declareQVars pr args
        return (AnyQVar qvar:lst,Arg qvar args')

  extractSub _ = return Nothing

assert :: B.Backend b => SMTExpr b BoolType -> SMT b ()
assert = L.assert

assertId :: B.Backend b => SMTExpr b BoolType -> SMT b (L.ClauseId b)
assertId = L.assertId

assertPartition :: B.Backend b => SMTExpr b BoolType -> L.Partition -> SMT b ()
assertPartition = L.assertPartition

interpolate :: B.Backend b => SMT b (SMTExpr b BoolType)
interpolate = L.interpolate

analyze :: (B.Backend b,GetType tp) => SMTExpr b tp -> E.Expression (B.Var b) (B.QVar b) (B.Fun b) (B.Constr b) (B.Field b) (B.FunArg b) (SMTExpr b) tp
analyze e = case L.extract e of
  Left e' -> e'
  Right sub -> error $ "smtlib2: Cannot analyze embedded object "++show sub++" using this API. Use the LowLevel module."

getValue :: (B.Backend b,L.FromSMT repr) => SMTExpr b repr -> SMT b (L.ValueType repr)
getValue = L.getValue

declare :: QuasiQuoter
declare = TH.declare' (Just $ \tp -> [t| forall b. B.Backend b => SMT b (SMTExpr b $(tp)) |])

constant :: (L.ToSMT t,L.FromSMT (L.ValueRepr t),L.ValueType (L.ValueRepr t) ~ t)  => t -> SMTExpr b (L.ValueRepr t)
constant v = SpecialExpr (Const' v)

(.==.) :: GetType t => SMTExpr b t -> SMTExpr b t -> SMTExpr b BoolType
(.==.) x y = SMTExpr (L.App L.Eq (Arg x (Arg y NoArg)))

(./=.) :: GetType t => SMTExpr b t -> SMTExpr b t -> SMTExpr b BoolType
(./=.) x y = SMTExpr (L.App L.Distinct (Arg x (Arg y NoArg)))

(.<.),(.<=.),(.>.),(.>=.) :: L.SMTOrd t => SMTExpr b t -> SMTExpr b t -> SMTExpr b BoolType
(.<.) x y = SMTExpr (L.App L.lt (Arg x (Arg y NoArg)))
(.<=.) x y = SMTExpr (L.App L.le (Arg x (Arg y NoArg)))
(.>.) x y = SMTExpr (L.App L.gt (Arg x (Arg y NoArg)))
(.>=.) x y = SMTExpr (L.App L.ge (Arg x (Arg y NoArg)))

(.+.),(.-.),(.*.) :: L.SMTArith t => SMTExpr b t -> SMTExpr b t -> SMTExpr b t
(.+.) x y = SMTExpr (L.App L.plus (Arg x (Arg y NoArg)))
(.-.) x y = SMTExpr (L.App L.minus (Arg x (Arg y NoArg)))
(.*.) x y = SMTExpr (L.App L.mult (Arg x (Arg y NoArg)))

abs' :: L.SMTArith t => SMTExpr b t -> SMTExpr b t
abs' x = SMTExpr (L.App L.abs' (Arg x NoArg))

ite :: GetType a => SMTExpr b BoolType -> SMTExpr b a -> SMTExpr b a -> SMTExpr b a
ite c ifT ifF = SMTExpr $ L.App L.ITE (Arg c (Arg ifT (Arg ifF NoArg)))

instance Num (SMTExpr b IntType) where
  (+) = (.+.)
  (-) = (.-.)
  (*) = (.*.)
  negate x = SMTExpr (L.App L.minus (Arg x NoArg))
  abs = abs'
  fromInteger x = SMTExpr (Const (L.IntValue x))
  signum x = ite (x .==. 0) 0 (ite (x .<. 0) (-1) 1)
