{-# LANGUAGE GADTs,RankNTypes,ImpredicativeTypes,ViewPatterns #-}
module Language.SMTLib2.Views where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators

import Data.Typeable (cast)

asVar :: SMTType t => SMTExpr t -> Maybe (Integer,SMTAnnotation t)
asVar (Var idx ann) = Just (idx,ann)
asVar _ = Nothing

asConst :: SMTType t => SMTExpr t -> Maybe (t,SMTAnnotation t)
asConst (Const c ann) = Just (c,ann)
asConst _ = Nothing

asApp :: (Args arg,SMTType res) => SMTExpr t -> Maybe (SMTFunction arg res,arg)
asApp (App fun xs) = cast (fun,xs)
asApp _ = Nothing

asAnyApp :: (forall arg. Args arg => SMTFunction arg res -> arg -> Maybe p)
            -> SMTExpr res -> Maybe p
asAnyApp f (App fun xs) = f fun xs
asAnyApp _ _ = Nothing

asAppArgs :: (Args arg,SMTType res) => SMTFunction arg res -> SMTExpr res -> Maybe arg
asAppArgs f (App f' args) = case cast (f',args) of
  Just (f'',args') -> if f==f''
                      then Just args'
                      else Nothing
asAppArgs _ _ = Nothing

asEq :: SMTType a => SMTExpr t -> Maybe [SMTExpr a]
asEq (App SMTEq xs) = cast xs
asEq _ = Nothing

asCompare :: SMTType a => SMTExpr t -> Maybe (SMTOrdOp,SMTExpr a,SMTExpr a)
asCompare (App (SMTOrd op) arg) = case cast arg of
  Just (x,y) -> Just (op,x,y)
  Nothing -> Nothing
asCompare _ = Nothing

asSum :: SMTType a => SMTExpr a -> Maybe [SMTExpr a]
asSum (App (SMTArith Plus) args) = Just args
asSum _ = Nothing

asProduct :: SMTType a => SMTExpr a -> Maybe [SMTExpr a]
asProduct (App (SMTArith Mult) args) = Just args
asProduct _ = Nothing

asMinus :: SMTType a => SMTExpr a -> Maybe (SMTExpr a,SMTExpr a)
asMinus (App SMTMinus arg) = Just arg
asMinus _ = Nothing

asDiv :: SMTType a => SMTExpr a -> Maybe (SMTExpr Integer,SMTExpr Integer)
asDiv (App (SMTIntArith Div) arg) = Just arg
asDiv _ = Nothing

asMod :: SMTType a => SMTExpr a -> Maybe (SMTExpr Integer,SMTExpr Integer)
asMod (App (SMTIntArith Mod) arg) = Just arg
asMod _ = Nothing

asRem :: SMTType a => SMTExpr a -> Maybe (SMTExpr Integer,SMTExpr Integer)
asRem (App (SMTIntArith Rem) arg) = Just arg
asRem _ = Nothing

asDivide :: SMTType a => SMTExpr a -> Maybe (SMTExpr Rational,SMTExpr Rational)
asDivide (App SMTDivide arg) = Just arg
asDivide _ = Nothing

asNeg :: SMTType a => SMTExpr a -> Maybe (SMTExpr a)
asNeg (App SMTNeg x) = Just x
asNeg _ = Nothing

asAbs :: SMTType a => SMTExpr a -> Maybe (SMTExpr a)
asAbs (App SMTAbs x) = Just x
asAbs _ = Nothing

asNot :: SMTType a => SMTExpr a -> Maybe (SMTExpr Bool)
asNot (App SMTNot x) = Just x
asNot _ = Nothing

asAnd :: SMTType a => SMTExpr a -> Maybe [SMTExpr Bool]
asAnd (App (SMTLogic And) xs) = Just xs
asAnd _ = Nothing

asOr :: SMTType a => SMTExpr a -> Maybe [SMTExpr Bool]
asOr (App (SMTLogic Or) xs) = Just xs
asOr _ = Nothing

asXOr :: SMTType a => SMTExpr a -> Maybe [SMTExpr Bool]
asXOr (App (SMTLogic XOr) xs) = Just xs
asXOr _ = Nothing

asImplies :: SMTType a => SMTExpr a -> Maybe [SMTExpr Bool]
asImplies (App (SMTLogic Implies) xs) = Just xs
asImplies _ = Nothing

asDistinct :: (SMTType a,SMTType t) => SMTExpr a -> Maybe [SMTExpr t]
asDistinct (App SMTDistinct xs) = cast xs
asDistinct _ = Nothing

asToReal :: SMTType a => SMTExpr a -> Maybe (SMTExpr Integer)
asToReal (App SMTToReal x) = Just x
asToReal _ = Nothing

asToInt :: SMTType a => SMTExpr a -> Maybe (SMTExpr Rational)
asToInt (App SMTToInt x) = Just x
asToInt _ = Nothing

asITE :: SMTType a => SMTExpr a -> Maybe (SMTExpr Bool,SMTExpr a,SMTExpr a)
asITE (App SMTITE x) = Just x
asITE _ = Nothing

asBVComp :: (IsBitVector t,SMTType a) => SMTBVCompOp -> SMTExpr a -> Maybe (SMTExpr (BitVector t),SMTExpr (BitVector t))
asBVComp op (App (SMTBVComp op') x) = if op==op'
                                      then cast x
                                      else Nothing
asBVComp _ _ = Nothing
