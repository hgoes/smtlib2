{-# LANGUAGE KindSignatures,DataKinds,GADTs,ScopedTypeVariables,RankNTypes,TypeOperators,FlexibleContexts #-}
module Language.SMTLib2.QuickCheck where

import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Expression hiding (AnyFunction)
import Language.SMTLib2.Internals.Type
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

data ExprGen m b var qvar fun con field farg e tp
  = ExprGen ((forall t. GetType t
              => Expression var qvar fun con field farg e t
              -> b -> m (e t,b))
             -> b
             -> m (e tp,b))

type BackendExprGen b tp = ExprGen (B.SMTMonad b) b (B.Var b) (B.QVar b) (B.Fun b) (B.Constr b) (B.Field b) (B.FunArg b) (B.Expr b) tp

newtype VarSet v (tp :: Type) = VarSet (Set (v tp))

data GenContext var qvar fun
  = GenCtx { allVars :: DMap Repr (VarSet var)
           , allQVars :: DMap Repr (VarSet qvar)
           , allFuns :: DMap Repr (VarSet (AnyFunction fun))
           }

data AnyFunction f (tp :: Type)
  = forall arg. GetTypes arg
    => AnyFunction (f '(arg,tp))

data AnyType = forall tp. GetType tp => AnyType (Proxy tp)

data AnyTypes = forall tps. GetTypes tps => AnyTypes (Proxy tps)

data TestExpr var qvar fun con field farg tp
  = TestExpr (Expression var qvar fun con field farg (TestExpr var qvar fun con field farg) tp)

type TestExprGen var qvar fun con field farg tp
  = ExprGen Identity () var qvar fun con field farg (TestExpr var qvar fun con field farg) tp

emptyContext :: GenContext var qvar fun
emptyContext = GenCtx { allVars = DMap.empty
                      , allQVars = DMap.empty
                      , allFuns = DMap.empty }

roundTripTest :: (B.Backend b,B.SMTMonad b ~ IO)
              => GenContext (B.Var b) (B.QVar b) (B.Fun b)
              -> IO b
              -> Property
roundTripTest ctx (cb::IO b) = monadicIO $ do
  AnyType (_::Proxy tp) <- pick genType
  expr <- pick (genTestExpr ctx)
  cond <- run $ do
    b <- cb
    (expr1,nb) <- encodeTestExpr expr b
    let expr2 = decodeTestExpr (expr1::B.Expr b tp) nb
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

encodeTestExpr :: (B.Backend b,GetType tp)
               => TestExpr (B.Var b) (B.QVar b) (B.Fun b) (B.Constr b) (B.Field b) (B.FunArg b) tp
               -> b
               -> B.SMTMonad b (B.Expr b tp,b)
encodeTestExpr e b = runStateT (encode' e) b
  where
    encode' :: (B.Backend b,GetType tp)
            => TestExpr (B.Var b) (B.QVar b) (B.Fun b) (B.Constr b) (B.Field b) (B.FunArg b) tp
            -> StateT b (B.SMTMonad b) (B.Expr b tp)
    encode' (TestExpr e) = do
      e' <- mapExpr return return return return return return encode' e
      b <- get
      (ne,nb) <- lift $ B.toBackend e' b
      put nb
      return ne

decodeTestExpr :: (B.Backend b,GetType tp)
               => B.Expr b tp
               -> b
               -> TestExpr (B.Var b) (B.QVar b) (B.Fun b) (B.Constr b) (B.Field b) (B.FunArg b) tp
decodeTestExpr e b
  = TestExpr $ runIdentity $ mapExpr return return return return return return
    (\e' -> return (decodeTestExpr e' b)) (B.fromBackend b e)

genTestExpr :: GetType tp => GenContext var qvar fun
            -> Gen (TestExpr var qvar fun con field farg tp)
genTestExpr ctx = do
  ExprGen egen <- genExpr ctx
  return $ fst $ runIdentity (egen (\e _ -> return (TestExpr e,())) ())

genExpr :: (Monad m,GetType t)
        => GenContext var qvar fun
        -> Gen (ExprGen m b var qvar fun con field farg e t)
genExpr ctx = sized $ \sz -> if sz==0
                             then oneof [ gen | Just gen <- [genVar
                                                            ,genQVar
                                                            ,Just $ genConst Proxy] ]
                             else resize (sz `div` 2) $ oneof
                                  [genApp]
                                  
  where
    genVar = do
      VarSet vs <- DMap.lookup getType (allVars ctx)
      if Set.null vs
        then Nothing
        else return $ elements [ ExprGen (\f -> f (Var v))
                               | v <- Set.toList vs ]
    genQVar = do
      VarSet vs <- DMap.lookup getType (allQVars ctx)
      if Set.null vs
        then Nothing
        else return $ elements [ ExprGen (\f -> f (QVar v))
                               | v <- Set.toList vs ]
    genConst :: (GetType t,Monad m) => Proxy t
             -> Gen (ExprGen m b var qvar fun con field farg e t)
    genConst (_::Proxy t) = case getType :: Repr t of
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
        val <- choose (0,2^bw-1)
        return $ ExprGen $ \f -> f (Const $ BitVecValue val)
      ArrayRepr _ (_::Repr el) -> do
        ExprGen c <- genConst (Proxy::Proxy el)
        return $ ExprGen $ \f b -> do
          (rel,b1) <- c f b
          f (App ConstArray (Arg rel NoArg)) b1

    genApp = do
      AnyFunction fun <- genFunction ctx
      args <- withArgs (genExpr ctx)
      return $ ExprGen $ \f b -> do
        (nb,rargs) <- mapAccumArgs (\b (ExprGen g) -> do
                                       (expr,nb) <- g f b
                                       return (nb,expr)
                                   ) b args
        f (App fun rargs) nb

genFunction :: GetType tp
            => GenContext var qvar fun
            -> Gen (AnyFunction (Function fun con field) tp)
genFunction ctx = oneof [ gen | Just gen <- [genFun
                                            ,genBuiltin Proxy] ]
  where
    genFun = do
      VarSet funs <- DMap.lookup getType (allFuns ctx)
      if Set.null funs
        then Nothing
        else return $ elements [ AnyFunction (Fun f)
                               | AnyFunction f <- Set.toList funs ]
    genBuiltin :: GetType t => Proxy t -> Maybe (Gen (AnyFunction (Function fun con field) t))
    genBuiltin (_::Proxy t) = case getType :: Repr t of
      BoolRepr -> Just $ oneof
                  [sized $
                   \len -> do
                     AnyType (tp::Proxy tp) <- genType
                     withAllEqLen tp len $
                       \(_::Proxy (tp ': arg))
                       -> elements [AnyFunction (Eq::Function fun con field '(tp ': arg,BoolType))
                                   ,AnyFunction (Distinct::Function fun con field '(tp ': arg,BoolType))]
                  ,do
                      op <- elements [Ge,Gt,Le,Lt]
                      return $ AnyFunction (OrdInt op)
                  ,do
                      op <- elements [Ge,Gt,Le,Lt]
                      return $ AnyFunction (OrdReal op)
                  ,return $ AnyFunction Not
                  ,sized $
                   \len -> withAllEqLen (Proxy::Proxy BoolType) len $
                           \(_::Proxy (BoolType ': arg)) -> do
                             op <- elements [And,Or,XOr,Implies]
                             return (AnyFunction (Logic op::Function fun con field '(BoolType ': arg,BoolType)))
                  ,return $ AnyFunction ITE
                  ,do
                      op <- elements [BVULE,BVULT,BVUGE,BVUGT,BVSLE,BVSLT,BVSGE,BVSGT]
                      sz <- arbitrarySizedNatural
                      reifyNat (sz::Integer) $
                        \(_::Proxy bw)
                        -> return $ AnyFunction (BVComp op::Function fun con field
                                                            '( '[BitVecType bw,BitVecType bw],
                                                               BoolType))
                  ,do
                      AnyTypes (_::Proxy idx) <- genTypes
                      return $ AnyFunction (Select::Function fun con field
                                                    '(ArrayType idx BoolType ': idx,BoolType))
                  ]
      IntRepr -> Just $ oneof
                 [sized $
                  \len -> withAllEqLen (Proxy::Proxy IntType) len $
                          \(_::Proxy (IntType ': arg)) -> do
                            op <- elements [Plus,Mult,Minus]
                            return (AnyFunction (ArithInt op::Function fun con field
                                                              '(IntType ': arg,IntType)))
                 ,do
                     op <- elements [Div,Mod,Rem]
                     return $ AnyFunction (ArithIntBin op)
                 ,return $ AnyFunction AbsInt
                 ,return $ AnyFunction ITE
                 ,return $ AnyFunction ToInt
                 ,do
                     AnyTypes (_::Proxy idx) <- genTypes
                     return $ AnyFunction (Select::Function fun con field
                                                   '(ArrayType idx IntType ': idx,IntType))
                 ]
      RealRepr -> Just $ oneof
                  [sized $
                   \len -> withAllEqLen (Proxy::Proxy RealType) len $
                           \(_::Proxy (RealType ': arg)) -> do
                             op <- elements [Plus,Mult,Minus]
                             return (AnyFunction (ArithReal op::Function fun con field
                                                                '(RealType ': arg,RealType)))
                  ,return $ AnyFunction Divide
                  ,return $ AnyFunction AbsReal
                  ,return $ AnyFunction ToReal
                  ,return $ AnyFunction ITE
                  ,do
                      AnyTypes (_::Proxy idx) <- genTypes
                      return $ AnyFunction (Select::Function fun con field
                                                    '(ArrayType idx RealType ': idx,RealType))
                  ]
      (BitVecRepr _::Repr t)
        -> Just $ oneof
           [return $ AnyFunction ITE
           ,do
               op <- elements [BVAdd,BVSub,BVMul,BVURem,BVSRem,BVUDiv,BVSDiv,BVSHL,BVLSHR,BVASHR,BVXor,BVAnd,BVOr]
               return $ AnyFunction (BVBin op)
           ,do
               op <- elements [BVNot,BVNeg]
               return $ AnyFunction (BVUn op)
           ,do
               AnyTypes (_::Proxy idx) <- genTypes
               return $ AnyFunction (Select::Function fun con field
                                             '(ArrayType idx t ': idx,t))
               --TODO: Concat, Extract
           ]
      ArrayRepr (_::Args Repr idx) (_::Repr el)
        -> Just $ oneof
           [return $ AnyFunction ITE
           ,do
               AnyTypes (_::Proxy idx') <- genTypes
               return $ AnyFunction (Select::Function fun con field
                                             '(ArrayType idx' (ArrayType idx el) ': idx',
                                               ArrayType idx el))
           ,return $ AnyFunction Store
           ,return $ AnyFunction ConstArray]
      _ -> Nothing

genType :: Gen AnyType
genType = sized $ \sz -> oneof $ [return $ AnyType (Proxy::Proxy BoolType)
                                 ,return $ AnyType (Proxy::Proxy IntType)
                                 ,return $ AnyType (Proxy::Proxy RealType)
                                 ,do
                                     sz <- arbitrarySizedNatural
                                     reifyNat sz $ \(_::Proxy bw)
                                                   -> return $ AnyType (Proxy::Proxy (BitVecType bw))]++
                         (if sz>0
                          then [do
                                   AnyTypes (_::Proxy tps) <- resize (sz `div` 2) genTypes
                                   AnyType (_::Proxy tp) <- resize (sz `div` 2) genType
                                   return $ AnyType (Proxy::Proxy (ArrayType tps tp))
                               ]
                          else [])

genTypes :: Gen AnyTypes
genTypes = sized $ \len -> gen' len
  where
    gen' 0 = return $ AnyTypes (Proxy::Proxy ('[]::[Type]))
    gen' n = do
      AnyTypes (_::Proxy tps) <- gen' (n-1)
      AnyType (_::Proxy tp) <- genType
      return $ AnyTypes (Proxy::Proxy (tp ': tps))

withAllEqLen :: GetType tp => Proxy tp -> Int
             -> (forall tps. (AllEq (tp ': tps),SameType (tp ': tps) ~ tp)
                 => Proxy (tp ': tps) -> a)
             -> a
withAllEqLen (_::Proxy tp) 0 f = f (Proxy::Proxy '[tp])
withAllEqLen (p::Proxy tp) n f
  = withAllEqLen p (n-1) $
    \(_::Proxy (tp ': tps)) -> f (Proxy::Proxy (tp ': tp ': tps))

instance (GShow var,GShow qvar,GShow fun,GShow con,GShow field,GShow farg)
         => GShow (TestExpr var qvar fun con field farg) where
  gshowsPrec n (TestExpr e) = gshowsPrec n e

instance (GShow var,GShow qvar,GShow fun,GShow con,GShow field,GShow farg)
         => Show (TestExpr var qvar fun con field farg tp) where
  showsPrec = gshowsPrec

instance Show AnyType where
  show (AnyType (_::Proxy tp)) = show (getType::Repr tp)

instance (GEq var,GEq qvar,GEq fun,GEq con,GEq field,GEq farg)
         => GEq (TestExpr var qvar fun con field farg) where
  geq (TestExpr x) (TestExpr y) = geq x y

instance (GEq var,GEq qvar,GEq fun,GEq con,GEq field,GEq farg)
         => Eq (TestExpr var qvar fun con field farg tp) where
  (==) (TestExpr x) (TestExpr y) = x==y
