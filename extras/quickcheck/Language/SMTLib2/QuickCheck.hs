{-# LANGUAGE KindSignatures,DataKinds,GADTs,ScopedTypeVariables,RankNTypes,TypeOperators,FlexibleContexts #-}
module Language.SMTLib2.QuickCheck where

import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Expression hiding (AnyFunction)
import Language.SMTLib2.Internals.Type
import Language.SMTLib2.Internals.Type.List (List(..))
import qualified Language.SMTLib2.Internals.Type.List as List
import Language.SMTLib2.Internals.Type.Nat

import Test.QuickCheck hiding (Args)
import Test.QuickCheck.Monadic
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Proxy
import Data.Functor.Identity
import Data.GADT.Show
import Data.GADT.Compare
import Control.Monad.State.Strict
import qualified GHC.TypeLits as TL

data ExprGen m b var qvar fun farg lvar e tp
  = ExprGen ((forall t. Expression var qvar fun farg lvar e t
              -> b -> m (e t,b))
             -> b
             -> m (e tp,b))

type BackendExprGen b tp = ExprGen (B.SMTMonad b) b (B.Var b) (B.QVar b) (B.Fun b) (B.FunArg b) (B.LVar b) (B.Expr b) tp

newtype VarSet v (tp :: Type) = VarSet (Set (v tp))

data GenContext var qvar fun
  = GenCtx { allVars :: DMap Repr (VarSet var)
           , allQVars :: DMap Repr (VarSet qvar)
           , allFuns :: DMap Repr (VarSet (AnyFunction fun))
           }

data AnyFunction f (tp :: Type)
  = forall (arg::[Type]). AnyFunction (f '(arg,tp))

data AnyType = forall tp. AnyType (Repr tp)

data AnyTypes = forall tps. AnyTypes (List Repr tps)

data AnyNatural = forall n. AnyNatural (Natural n)

data TestExpr var qvar fun farg lvar tp
  = TestExpr (Expression var qvar fun farg lvar (TestExpr var qvar fun farg lvar) tp)

type TestExprGen var qvar fun farg lvar tp
  = ExprGen Identity () var qvar fun farg lvar (TestExpr var qvar fun farg lvar) tp

emptyContext :: GenContext var qvar fun
emptyContext = GenCtx { allVars = DMap.empty
                      , allQVars = DMap.empty
                      , allFuns = DMap.empty }

roundTripTest :: (B.Backend b,B.SMTMonad b ~ IO)
              => GenContext (B.Var b) (B.QVar b) (B.Fun b)
              -> IO b
              -> Property
roundTripTest ctx (cb::IO b) = monadicIO $ do
  AnyType tp <- pick genType
  expr <- pick (genTestExpr tp ctx)
  cond <- run $ do
    b <- cb
    (expr1,nb) <- encodeTestExpr expr b
    let expr2 = decodeTestExpr expr1 nb
    return $ expr2==expr
  assert cond

{-roundTripTest :: B.Backend b => GenContext (B.Var b) (B.QVar b) (B.Fun b)
              -> PropertyM (StateT b (B.SMTMonad b)) ()
roundTripTest ctx = do
  AnyType (_::Proxy tp) <- pick genType
  expr1 <- pick (genTestExpr ctx)
  b <- lift get
  (expr2,nb) <- lift $ lift $ encodeTestExpr expr1 b
  lift $ put nb
  let expr3 = decodeTestExpr expr2 nb
  assert $ expr1 == expr3-}

encodeTestExpr :: (B.Backend b)
               => TestExpr (B.Var b) (B.QVar b) (B.Fun b) (B.FunArg b) (B.LVar b) tp
               -> b
               -> B.SMTMonad b (B.Expr b tp,b)
encodeTestExpr e b = runStateT (encode' e) b
  where
    encode' :: (B.Backend b)
            => TestExpr (B.Var b) (B.QVar b) (B.Fun b) (B.FunArg b) (B.LVar b) tp
            -> StateT b (B.SMTMonad b) (B.Expr b tp)
    encode' (TestExpr e) = do
      e' <- mapExpr return return return return return encode' e
      b <- get
      (ne,nb) <- lift $ B.toBackend e' b
      put nb
      return ne

decodeTestExpr :: (B.Backend b)
               => B.Expr b tp
               -> b
               -> TestExpr (B.Var b) (B.QVar b) (B.Fun b) (B.FunArg b) (B.LVar b) tp
decodeTestExpr e b
  = TestExpr $ runIdentity $ mapExpr return return return return return
    (\e' -> return (decodeTestExpr e' b)) (B.fromBackend b e)

genTestExpr :: (GetFunType fun)
            => Repr tp -> GenContext var qvar fun
            -> Gen (TestExpr var qvar fun farg lvar tp)
genTestExpr tp ctx = do
  ExprGen egen <- genExpr tp ctx
  return $ fst $ runIdentity (egen (\e _ -> return (TestExpr e,())) ())

genExpr :: (Monad m,GetFunType fun)
        => Repr t -> GenContext var qvar fun
        -> Gen (ExprGen m b var qvar fun farg lvar e t)
genExpr tp ctx = sized $ \sz -> if sz==0
                                then oneof [ gen | Just gen <- [genVar tp
                                                               ,genQVar tp
                                                               ,Just $ genConst tp] ]
                                else resize (sz `div` 2) $ oneof
                                     [genApp tp]
  where
    genVar tp = do
      VarSet vs <- DMap.lookup tp (allVars ctx)
      if Set.null vs
        then Nothing
        else return $ elements [ ExprGen (\f -> f (Var v))
                               | v <- Set.toList vs ]
    genQVar tp = do
      VarSet vs <- DMap.lookup tp (allQVars ctx)
      if Set.null vs
        then Nothing
        else return $ elements [ ExprGen (\f -> f (QVar v))
                               | v <- Set.toList vs ]
    genConst :: (Monad m) => Repr t
             -> Gen (ExprGen m b var qvar fun farg lvar e t)
    genConst tp = case tp of
      BoolRepr -> do
        val <- arbitrary
        return $ ExprGen $ \f -> f (Const $ BoolValue val)
      IntRepr -> do
        val <- arbitrary
        return $ ExprGen $ \f -> f (Const $ IntValue val)
      RealRepr -> do
        val <- arbitrary
        return $ ExprGen $ \f -> f (Const $ RealValue val)
      BitVecRepr bw -> do
        val <- choose (0,2^(bwSize bw)-1)
        return $ ExprGen $ \f -> f (Const $ BitVecValue val bw)
      ArrayRepr idx el -> do
        ExprGen c <- genConst el
        return $ ExprGen $ \f b -> do
          (rel,b1) <- c f b
          f (App (ConstArray idx el) (rel ::: Nil)) b1

    --genApp :: (Monad m) => Repr tp
    --       -> Gen (ExprGen m b var qvar fun con field farg lvar e tp)
    genApp tp = do
      AnyFunction fun <- genFunction tp ctx
      let (args,_) = getFunType fun
      args' <- List.mapM (\tp -> genExpr tp ctx) args
      return $ ExprGen $ \f b -> do
        (nb,rargs) <- List.mapAccumM (\b (ExprGen g) -> do
                                         (expr,nb) <- g f b
                                         return (nb,expr)
                                     ) b args'
        f (App fun rargs) nb

genFunction :: Repr tp
            -> GenContext var qvar fun
            -> Gen (AnyFunction (Function fun) tp)
genFunction tp ctx = oneof [ gen | Just gen <- [genFun
                                               ,genBuiltin tp] ]
  where
    genFun = do
      VarSet funs <- DMap.lookup tp (allFuns ctx)
      if Set.null funs
        then Nothing
        else return $ elements [ AnyFunction (Fun f)
                               | AnyFunction f <- Set.toList funs ]
    genBuiltin :: Repr t -> Maybe (Gen (AnyFunction (Function fun) t))
    genBuiltin tp = case tp of
      BoolRepr -> Just $ oneof
                  [do
                      AnyType tp <- genType
                      AnyNatural sz <- genNatural
                      elements [AnyFunction (Eq tp sz)
                               ,AnyFunction (Distinct tp sz)]
                  ,do
                      op <- elements [Ge,Gt,Le,Lt]
                      return $ AnyFunction (Ord NumInt op)
                  ,do
                      op <- elements [Ge,Gt,Le,Lt]
                      return $ AnyFunction (Ord NumReal op)
                  ,return $ AnyFunction Not
                  ,do
                      AnyNatural sz <- genNatural
                      op <- elements [And,Or,XOr,Implies]
                      return (AnyFunction (Logic op sz))
                  ,return $ AnyFunction (ITE tp)
                  ,do
                      op <- elements [BVULE,BVULT,BVUGE,BVUGT,BVSLE,BVSLT,BVSGE,BVSGT]
                      sz <- arbitrarySizedNatural
                      case TL.someNatVal sz of
                        Just (TL.SomeNat sz') -> return $ AnyFunction
                                                 (BVComp op (bw sz'))
                  ,do
                      AnyTypes idx <- genTypes
                      return $ AnyFunction (Select idx tp)
                  ]
      IntRepr -> Just $ oneof
                 [do
                     AnyNatural len <- genNatural
                     op <- elements [Plus,Mult,Minus]
                     return (AnyFunction (Arith NumInt op len))
                 ,do
                     op <- elements [Div,Mod,Rem]
                     return $ AnyFunction (ArithIntBin op)
                 ,return $ AnyFunction (Abs NumInt)
                 ,return $ AnyFunction (ITE tp)
                 ,return $ AnyFunction ToInt
                 ,do
                     AnyTypes idx <- genTypes
                     return $ AnyFunction (Select idx tp)
                 ]
      RealRepr -> Just $ oneof
                  [do
                      AnyNatural sz <- genNatural
                      op <- elements [Plus,Mult,Minus]
                      return (AnyFunction (Arith NumReal op sz))
                  ,return $ AnyFunction Divide
                  ,return $ AnyFunction (Abs NumReal)
                  ,return $ AnyFunction ToReal
                  ,return $ AnyFunction (ITE tp)
                  ,do
                      AnyTypes idx <- genTypes
                      return $ AnyFunction (Select idx tp)
                  ]
      (BitVecRepr bw)
        -> Just $ oneof
           [return $ AnyFunction (ITE tp)
           ,do
               op <- elements [BVAdd,BVSub,BVMul,BVURem,BVSRem,BVUDiv,BVSDiv,BVSHL,BVLSHR,BVASHR,BVXor,BVAnd,BVOr]
               return $ AnyFunction (BVBin op bw)
           ,do
               op <- elements [BVNot,BVNeg]
               return $ AnyFunction (BVUn op bw)
           ,do
               AnyTypes idx <- genTypes
               return $ AnyFunction (Select idx tp)
               --TODO: Concat, Extract
           ]
      ArrayRepr idx el
        -> Just $ oneof
           [return $ AnyFunction (ITE tp)
           ,do
               AnyTypes idx' <- genTypes
               return $ AnyFunction (Select idx' tp)
           ,return $ AnyFunction (Store idx el)
           ,return $ AnyFunction (ConstArray idx el)]
      _ -> Nothing

genType :: Gen AnyType
genType = sized $ \sz -> oneof $ [return $ AnyType BoolRepr
                                 ,return $ AnyType IntRepr
                                 ,return $ AnyType RealRepr
                                 ,do
                                     sz <- arbitrarySizedNatural
                                     case TL.someNatVal sz of
                                       Just (TL.SomeNat sz')
                                         -> return $ AnyType (BitVecRepr (bw sz'))]++
                         (if sz>0
                          then [do
                                   AnyTypes tps <- resize (sz `div` 2) genTypes
                                   AnyType tp <- resize (sz `div` 2) genType
                                   return $ AnyType (ArrayRepr tps tp)
                               ]
                          else [])

genTypes :: Gen AnyTypes
genTypes = sized $ \len -> gen' len
  where
    gen' 0 = return $ AnyTypes Nil
    gen' n = do
      AnyTypes tps <- gen' (n-1)
      AnyType tp <- genType
      return $ AnyTypes (tp ::: tps)

genNatural :: Gen AnyNatural
genNatural = sized $ \len -> reifyNat (fromIntegral len) (return.AnyNatural)

withAllEqLen :: Repr tp -> Int
             -> (forall tps. List Repr (tp ': tps) -> a)
             -> a
withAllEqLen tp 0 f = f (tp ::: Nil)
withAllEqLen tp n f
  = withAllEqLen tp (n-1) $
    \tps -> f (tp ::: tps)

instance (GShow var,GShow qvar,GShow fun,GShow farg,GShow lvar)
         => GShow (TestExpr var qvar fun farg lvar) where
  gshowsPrec n (TestExpr e) = gshowsPrec n e

instance (GShow var,GShow qvar,GShow fun,GShow farg,GShow lvar)
         => Show (TestExpr var qvar fun farg lvar tp) where
  showsPrec = gshowsPrec

instance Show AnyType where
  show (AnyType tp) = show tp

instance (GEq var,GEq qvar,GEq fun,GEq farg,GEq lvar)
         => GEq (TestExpr var qvar fun farg lvar) where
  geq (TestExpr x) (TestExpr y) = geq x y

instance (GEq var,GEq qvar,GEq fun,GEq farg,GEq lvar)
         => Eq (TestExpr var qvar fun farg lvar tp) where
  (==) (TestExpr x) (TestExpr y) = x==y
