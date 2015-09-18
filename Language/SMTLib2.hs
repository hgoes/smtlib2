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
module Language.SMTLib2 
       where

import qualified Language.SMTLib2.Internals.Type as T
import qualified Language.SMTLib2.Internals.Type.Nat as T
import Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Expression as E

import Control.Monad.State
import Data.Typeable
import Data.Constraint
import Data.IntMap (IntMap)
import qualified Data.IntMap as IMap
#if __GLASGOW_HASKELL__ < 710
import Control.Applicative (Applicative(..))
#endif

newtype Backend b => SMT' b a = SMT' (StateT b (SMTMonad b) a)

instance Backend b => Functor (SMT' b) where
  fmap f (SMT' act) = SMT' (fmap f act)

instance Backend b => Applicative (SMT' b) where
  pure x = SMT' (pure x)
  (<*>) (SMT' fun) (SMT' arg) = SMT' (fun <*> arg)

instance Backend b => Monad (SMT' b) where
  (>>=) (SMT' act) app = SMT' (act >>= (\res -> case app res of
                                                  SMT' p -> p))

instance Backend b => MonadState b (SMT' b) where
  get = SMT' get
  put x = SMT' (put x)
  state act = SMT' (state act)

liftSMT :: Backend b => SMTMonad b a -> SMT' b a
liftSMT act = SMT' (lift act)

data SMTArray idx t = SMTArray deriving (Typeable)
data SMTBV = SMTBV Integer deriving (Typeable,Show,Eq,Ord)

class (Typeable t) => SMTType t where
  type SMTRepr t :: Either T.Type *
  getRepr :: (SMTRepr t ~ Right ann)
          => Proxy t -> ann
          -> (forall t'. T.GetType t' => Proxy t' -> a)
          -> a
  getRepr p = error $ "smtlib2: getRepr not implemented for type "++show (typeRep p)
  getAnnotation :: (SMTRepr t ~ Right ann,T.GetType repr)
                => Proxy t -> Proxy repr -> ann
  getAnnotation p = error $ "smtlib2: getAnnotation not implemented for type "++show (typeRep p)
  typeContext :: Proxy t -> TypeInfo t

data TypeInfo t = forall (el::T.Type). TypeInfoS { proxyS :: Proxy el
                                                 , contextS :: Dict (SMTRepr t ~ Left el,T.GetType el) }
                | forall (ann:: *). TypeInfoD { proxyD :: Proxy ann
                                              , contextD :: Dict (SMTRepr t ~ Right ann) }

class SMTType t => SMTValue b t where
  fromValue :: SMTRepr t ~ Left tp => Proxy b -> T.Value (Constr b) tp -> t
  fromValue _ _ = error $ "smtlib2: fromValue not implemented for type "++
                          show (typeRep (Proxy::Proxy t)) :: t
  toValue :: SMTRepr t ~ Left tp => Proxy b -> t -> T.Value (Constr b) tp
  toValue _ (_::t) = error $ "smtlib2: toValue not implemented for type "++
                             show (typeRep (Proxy::Proxy t))
  fromDynValue :: SMTRepr t ~ Right ann
               => Proxy b -> T.Value (Constr b) repr
               -> t
  fromDynValue _ _ = error $ "smtlib2: fromDynValue not implemented for type "++
                             show (typeRep (Proxy::Proxy t)) :: t
  toDynValue :: SMTRepr t ~ Right ann
               => Proxy b -> t -> ann
               -> (forall repr. T.GetType repr => T.Value (Constr b) repr -> a)
               -> a
  toDynValue _ (_::t) _ _ = error $ "smtlib2: fromDynValue not implemented for type "++
                                    show (typeRep (Proxy::Proxy t))

data Lst (a :: [*]) where
  Nil :: Lst '[]
  Cons :: t -> Lst ts -> Lst (t ': ts)

data ArgLst (e :: * -> *) (arg :: [*]) where
  ArgNil :: ArgLst e '[]
  ArgCons :: e t -> ArgLst e ts -> ArgLst e (t ': ts)

class (Typeable arg,Backend (ArgBackend arg)) => Args arg where
  type ArgBackend arg :: *
  type ArgRepr arg :: Either [T.Type] *
  getArgRepr :: (ArgRepr arg ~ Right ann)
             => Proxy arg -> ann
             -> (forall arg'. T.Liftable arg' => Proxy arg' -> a)
             -> a
  getArgRepr p = error $ "smtlib2: getArgRepr not implemented for type "++show (typeRep p)
  toArgs :: (ArgRepr arg ~ Left arg') => arg -> T.Args (SMTExpr' (ArgBackend arg)) arg'
  toArgs (_::arg) = error $ "smtlib2: toArgs not implemented for type "++
                            show (typeRep (Proxy::Proxy arg))
  withArgs :: (ArgRepr arg ~ Right ann) => arg
           -> (forall arg'. T.Liftable arg' => T.Args (SMTExpr' (ArgBackend arg)) arg' -> ann -> a)
           -> a
  argAnnotation :: (ArgRepr arg ~ Right ann) => arg -> ann
  argAnnotation (_::arg) = error $ "smtlib2: argAnnotation not implemented for type "++
                                   show (typeRep (Proxy::Proxy arg))
  argContext :: Proxy arg -> ArgInfo arg

data ArgInfo t = forall (el::[T.Type]). ArgInfoS { argProxyS :: Proxy el
                                                 , argContextS :: Dict (ArgRepr t ~ Left el,T.Liftable el) }
               | forall (ann:: *). ArgInfoD { argProxyD :: Proxy ann
                                            , argContextD :: Dict (ArgRepr t ~ Right ann) }


instance SMTType Bool where
  type SMTRepr Bool = Left T.BoolType
  typeContext _ = TypeInfoS Proxy Dict

instance SMTValue b Bool where
  fromValue _ (T.BoolValue v) = v
  toValue _ v = T.BoolValue v

instance SMTType Integer where
  type SMTRepr Integer = Left T.IntType
  typeContext _ = TypeInfoS Proxy Dict

instance SMTValue b Integer where
  fromValue _ (T.IntValue v) = v
  toValue _ v = T.IntValue v

instance SMTType SMTBV where
  type SMTRepr SMTBV = Right Integer
  getRepr _ w f = T.reifyNat w $ \(_::Proxy n) -> f (Proxy::Proxy (T.BitVecType n))
  getAnnotation _ x = case T.getType x of
    T.BitVecRepr n -> n
  typeContext _ = TypeInfoD Proxy Dict

instance SMTValue b SMTBV where
  fromDynValue _ (T.BitVecValue val) = SMTBV val
  toDynValue (_::Proxy b) (SMTBV val) ann f
    = T.reifyNat ann $ \(_::Proxy n)
       -> f (T.BitVecValue val :: T.Value (Constr b) (T.BitVecType n))

class (Args idx,ArgRepr idx ~ idx',SMTType el,SMTRepr el ~ el')
      => SMTArray' idx el (idx' :: Either [T.Type] *) (el' :: Either T.Type *) where
  type ArrayRepr idx' el' :: Either T.Type *
#if __GLASGOW_HASKELL__ >= 710
  getArrayRepr :: (ArrayRepr idx' el' ~ Right ann)
               => Proxy '(idx',el') -> Proxy (SMTArray idx el) -> ann
               -> (forall idx'' el''. (T.Liftable idx'',T.GetType el'')
                   => Proxy (T.ArrayType idx'' el'') -> a)
               -> a
#else
  getArrayRepr :: (ArrayRepr idx' el' ~ Right ann)
               => Proxy '(idx',el') -> Proxy (SMTArray idx el) -> ann
               -> (forall tp. (T.GetType tp)
                   => Proxy tp -> a)
               -> a
#endif
  getArrayRepr = error $ "smtlib2: getArrayRepr not implemented."
  arrayContext :: Proxy (SMTArray idx el) -> TypeInfo (SMTArray idx el)

-- Both arguments static
instance (Args idx,SMTType el,
          ArgRepr idx ~ Left idx',SMTRepr el ~ Left el',
          T.Liftable idx',T.GetType el')
         => SMTArray' idx el (Left idx') (Left el') where
  type ArrayRepr (Left idx') (Left el') = Left (T.ArrayType idx' el')
  arrayContext _ = TypeInfoS Proxy Dict

-- Index static, element dynamic
instance (Args idx,SMTType el,
          ArgRepr idx ~ Left idx',SMTRepr el ~ Right el',T.Liftable idx')
         => SMTArray' idx el (Left idx') (Right el') where
  type ArrayRepr (Left idx') (Right el') = Right el'
  getArrayRepr (_::Proxy '(Left idx',Right el')) (_::Proxy (SMTArray idx el)) eann f
    = getRepr (Proxy::Proxy el) eann $
      \(Proxy::Proxy tel) -> f (Proxy::Proxy (T.ArrayType idx' tel))
  arrayContext _ = TypeInfoD Proxy Dict

-- Index dynamic, element static
instance (Args idx,SMTType el,
          ArgRepr idx ~ Right idx',SMTRepr el ~ Left el',T.GetType el')
         => SMTArray' idx el (Right idx') (Left el') where
  type ArrayRepr (Right idx') (Left el') = Right idx'
  getArrayRepr (_::Proxy '(Right idx',Left el')) (_::Proxy (SMTArray idx el)) iann f
    = getArgRepr (Proxy::Proxy idx) iann $
      \(Proxy::Proxy tidx) -> f (Proxy::Proxy (T.ArrayType tidx el'))
  arrayContext _ = TypeInfoD Proxy Dict

-- Both arguments dynamic
instance (Args idx,SMTType el,
          ArgRepr idx ~ Right idx',SMTRepr el ~ Right el')
         => SMTArray' idx el (Right idx') (Right el') where
  type ArrayRepr (Right idx') (Right el') = Right (idx',el')
  getArrayRepr _ (_::Proxy (SMTArray idx el)) (iann,eann) f
    = getArgRepr (Proxy::Proxy idx) iann $
      \(_::Proxy tidx) -> getRepr (Proxy::Proxy el) eann $
      \(_::Proxy tel) -> f (Proxy::Proxy (T.ArrayType tidx tel))
  arrayContext _ = TypeInfoD Proxy Dict

instance (Args idx,SMTType el,
          SMTArray' idx el (ArgRepr idx) (SMTRepr el))
         => SMTType (SMTArray idx el) where
  type SMTRepr (SMTArray idx el) = ArrayRepr (ArgRepr idx) (SMTRepr el)
  getRepr pr@(_::Proxy (SMTArray idx el))
    = getArrayRepr (Proxy::Proxy '(ArgRepr idx,SMTRepr el)) pr
  typeContext = arrayContext

data QVar' (t::T.Type) = QVar' !Int !Int

data SMTExpr' b t where
  SMTExpr' :: Expression (Var b) QVar' (Fun b) (B.Constr b) (B.Field b) (FunArg b) (SMTExpr' b) t
           -> SMTExpr' b t
  Quantification' :: T.GetTypes arg => Quantifier -> Int -> T.Args Proxy arg
                  -> SMTExpr' b T.BoolType
                  -> SMTExpr' b T.BoolType

#if __GLASGOW_HASKELL__ < 710
instance (Typeable b,T.GetType t) => Typeable (SMTExpr' b t) where
  typeOf (_::Proxy (SMTExpr' b t))
    = mkTyConApp
      (mkTyCon3 "smtlib2" "Language.SMTLib2" "SMTExpr'")
      [typeOf (Proxy::Proxy b)
      ,typeOfType (Proxy::Proxy t)]
#endif

data SMTExpr b t where
  SExpr :: (SMTType t,SMTRepr t ~ Left repr,T.GetType repr)
        => SMTExpr' b repr -> SMTExpr b t
  DExpr :: (SMTType t,SMTRepr t ~ Right ann,T.GetType repr)
        => SMTExpr' b repr -> ann -> SMTExpr b t
  deriving (Typeable)

withSMTExpr :: SMTExpr b t -> (forall repr. T.GetType repr => SMTExpr' b repr -> a) -> a
withSMTExpr (SExpr e) f = f e
withSMTExpr (DExpr e _) f = f e

class (SMTType tp,SMTRepr tp ~ tp',
       BoundedLst tps,
       BoundedLstRepr tps ~ lst)
      => AddArg tp tp' (tps :: [*]) (lst :: Either [T.Type] *) where
  type AddedArg tp' lst :: Either [T.Type] *
  getAddedArg :: (AddedArg tp' lst ~ Right anns)
              => Proxy tp -> Proxy tp' -> Proxy tps -> Proxy lst -> anns
                 -> (forall (arg :: [T.Type]). T.Liftable arg => Proxy arg -> a)
                 -> a
  getAddedArg pr = error $ "smtlib2: getAddedArg not implemented for "++show (typeRep pr)
  toAddedArg :: (AddedArg tp' lst ~ Left tps')
             => ArgLst (SMTExpr b) (tp ': tps)
             -> T.Args (SMTExpr' b) tps'
  toAddedArg (_::ArgLst (SMTExpr b) (tp ': tps))
    = error $ "smtlib2: toAddedArg not implemented for "++
              show (typeRep (Proxy::Proxy tp))++" and "++
#if __GLASGOW_HASKELL__ >= 710
              show (typeRep (Proxy::Proxy tps))
#else
              show (typeOfBoundedLst (Proxy::Proxy tps))
#endif
  addedArgAnn :: (AddedArg (SMTRepr tp) (BoundedLstRepr tps) ~ Right ann)
              => ArgLst (SMTExpr b) (tp ': tps)
              -> ann
  addedArgAnn (_::ArgLst (SMTExpr b) (tp ': tps))
    = error $ "smtlib2: addedArgAnn not implemented for "++
              show (typeRep (Proxy::Proxy tp))++" and "++
#if __GLASGOW_HASKELL__ >= 710
              show (typeRep (Proxy::Proxy tps))
#else
              show (typeOfBoundedLst (Proxy::Proxy tps))
#endif
  withAddedArgs :: (AddedArg (SMTRepr tp) (BoundedLstRepr tps) ~ Right ann)
                => ArgLst (SMTExpr b) (tp ': tps)
                -> (forall arg'. T.Liftable arg' => T.Args (SMTExpr' b) arg' -> ann -> a)
                -> a
  withAddedArgs (_::ArgLst (SMTExpr b) (tp ': tps)) _
    = error $ "smtlib2: withAddedArgs not implemented for "++
              show (typeRep (Proxy::Proxy tp))++" and "++
#if __GLASGOW_HASKELL__ >= 710
              show (typeRep (Proxy::Proxy tps))
#else
              show (typeOfBoundedLst (Proxy::Proxy tps))
#endif
  addedArgContext :: Proxy tp -> Proxy tps -> BoundedLstInfo (tp ': tps)
#if __GLASGOW_HASKELL__ < 710
  typeOfAddArg :: Proxy (tp ': tps) -> TypeRep
#endif

#if __GLASGOW_HASKELL__ >= 710
class (Typeable tps)
      => BoundedLst (tps :: [*]) where
#else
class BoundedLst (tps :: [*]) where
#endif
  type BoundedLstRepr tps :: Either [T.Type] *
  getBoundedRepr :: (BoundedLstRepr tps ~ Right anns)
                 => Proxy tps -> anns
                 -> (forall (arg :: [T.Type]). T.Liftable arg => Proxy arg -> a)
                 -> a
  getBoundedRepr pr
    = error $ "smtlib2: getBoundedRepr not implemented for "++
#if __GLASGOW_HASKELL__ >= 710
              show (typeRep pr)
#else
              show (typeOfBoundedLst pr)
#endif
  toBoundedArgs :: (BoundedLstRepr tps ~ Left tps')
                => ArgLst (SMTExpr b) tps
                -> T.Args (SMTExpr' b) tps'
  toBoundedArgs (_::ArgLst (SMTExpr b) tps)
    = error $ "smtlib2: toBoundedArgs not implemented for "++
#if __GLASGOW_HASKELL__ >= 710
              show (typeRep (Proxy::Proxy tps))
#else
              show (typeOfBoundedLst (Proxy::Proxy tps))
#endif
  boundedArgAnn :: (BoundedLstRepr tps ~ Right ann)
                => ArgLst (SMTExpr b) tps
                -> ann
  boundedArgAnn (_::ArgLst (SMTExpr b) tps)
    = error $ "smtlib2: boundedArgAnn not implemented for "++
#if __GLASGOW_HASKELL__ >= 710
              show (typeRep (Proxy::Proxy tps))
#else
              show (typeOfBoundedLst (Proxy::Proxy tps))
#endif
  withBoundedArgs :: (BoundedLstRepr tps ~ Right ann)
                  => ArgLst (SMTExpr b) tps
                  -> (forall arg'. T.Liftable arg' => T.Args (SMTExpr' b) arg' -> ann -> a)
                  -> a
  withBoundedArgs (_::ArgLst (SMTExpr b) tps) _
    = error $ "smtlib2: withBoundedArgs not implemented for type "++
#if __GLASGOW_HASKELL__ >= 710
              show (typeRep (Proxy::Proxy tps))
#else
              show (typeOfBoundedLst (Proxy::Proxy tps))
#endif
  boundedLstContext :: Proxy tps -> BoundedLstInfo tps
#if __GLASGOW_HASKELL__ < 710
  typeOfBoundedLst :: Proxy tps -> TypeRep
#endif

data BoundedLstInfo (tps :: [*])
  = forall (el::[T.Type]). BoundedLstInfoS { bndProxyS :: Proxy el
                                           , bndContextS :: Dict (BoundedLstRepr tps ~ Left el,
                                                                  T.Liftable el) }
  | forall (ann:: *). BoundedLstInfoD { bndProxyD :: Proxy ann
                                      , bndContextD :: Dict (BoundedLstRepr tps ~ Right ann) }

instance BoundedLst '[] where
  type BoundedLstRepr '[] = Left '[]
  toBoundedArgs _ = T.NoArg
  boundedLstContext _ = BoundedLstInfoS Proxy Dict
#if __GLASGOW_HASKELL__ < 710
  typeOfBoundedLst _ = mkTyConApp
                       (mkTyCon3 "smtlib2" "Language.SMTLib2" "'[]")
                       []
#endif

instance (BoundedLst tps,
          AddArg tp tp' tps (BoundedLstRepr tps))
         => BoundedLst (tp ': tps) where
  type BoundedLstRepr (tp ': tps) = AddedArg (SMTRepr tp) (BoundedLstRepr tps)
  getBoundedRepr (_::Proxy (tp ': tps)) anns f
    = getAddedArg (Proxy::Proxy tp)
                  (Proxy::Proxy (SMTRepr tp))
                  (Proxy::Proxy tps)
                  (Proxy::Proxy (BoundedLstRepr tps)) anns f
  toBoundedArgs = toAddedArg
  boundedArgAnn = addedArgAnn
  withBoundedArgs = withAddedArgs
  boundedLstContext (_::Proxy (tp ': tps)) = addedArgContext (Proxy::Proxy tp) (Proxy::Proxy tps)
#if __GLASGOW_HASKELL__ < 710
  typeOfBoundedLst = typeOfAddArg
#endif

instance (SMTType tp,SMTRepr tp ~ Left tp',
          BoundedLst tps,BoundedLstRepr tps ~ Left tps',
          T.Liftable tps',T.GetType tp')
         => AddArg tp (Left tp') tps (Left tps') where
  type AddedArg (Left tp') (Left tps') = Left (tp' ': tps')
  toAddedArg (ArgCons (SExpr x) xs) = T.Arg x (toBoundedArgs xs)
  addedArgContext _ _ = BoundedLstInfoS Proxy Dict
#if __GLASGOW_HASKELL__ < 710
  typeOfAddArg (_::Proxy (tp ': tps))
    = mkTyConApp
      (mkTyCon3 "smtlib2" "Language.SMTLib2" "':")
      [typeOf (Proxy::Proxy tp)
      ,typeOfBoundedLst (Proxy::Proxy tps)]
#endif

instance (SMTType tp,SMTRepr tp ~ Left tp',T.GetType tp',
          BoundedLst tps,BoundedLstRepr tps ~ Right (Lst anns))
         => AddArg tp (Left tp') tps (Right (Lst anns)) where
  type AddedArg (Left tp') (Right (Lst anns)) = Right (Lst anns)
  getAddedArg _ (_::Proxy (Left tp')) prTps _ anns f
    = getBoundedRepr prTps anns $
      \(_::Proxy arg) -> f (Proxy::Proxy (tp' ': arg))
  addedArgAnn (ArgCons _ xs) = boundedArgAnn xs
  withAddedArgs (ArgCons (SExpr x) xs) f = withBoundedArgs xs $
                                           \xs' ann -> f (T.Arg x xs') ann
  addedArgContext _ _ = BoundedLstInfoD Proxy Dict

argLstToArgs :: ArgLst (SMTExpr b) arg
             -> (forall repr. T.Liftable repr => T.Args (SMTExpr' b) repr -> a)
             -> a
argLstToArgs ArgNil f = f T.NoArg
argLstToArgs (ArgCons (SExpr x) xs) f
  = argLstToArgs xs (\xs' -> f (T.Arg x xs'))
argLstToArgs (ArgCons (DExpr x _) xs) f
  = argLstToArgs xs (\xs' -> f (T.Arg x xs'))

instance (SMTType tp,SMTRepr tp ~ Right ann,
          BoundedLst tps,BoundedLstRepr tps ~ Left tps',T.Liftable tps')
         => AddArg tp (Right ann) tps (Left tps') where
  type AddedArg (Right ann) (Left tps') = Right (Lst '[ann])
  getAddedArg prTp _ (_::Proxy tps) (_::Proxy (Left tps')) (Cons ann Nil) f
    = getRepr prTp ann $
      \(_::Proxy tp') -> f (Proxy::Proxy (tp' ': tps'))
  addedArgAnn (ArgCons (DExpr _ ann) _) = Cons ann Nil
  withAddedArgs (ArgCons (DExpr x ann) xs) f = f (T.Arg x (toBoundedArgs xs)) (Cons ann Nil)
  addedArgContext _ _ = BoundedLstInfoD Proxy Dict
#if __GLASGOW_HASKELL__ < 710
  typeOfAddArg (_::Proxy (tp ': tps))
    = mkTyConApp
      (mkTyCon3 "smtlib2" "Language.SMTLib2" "':")
      [typeOf (Proxy::Proxy tp)
      ,typeOfBoundedLst (Proxy::Proxy tps)]
#endif

instance (SMTType tp,SMTRepr tp ~ Right ann,
          BoundedLst tps,BoundedLstRepr tps ~ Right (Lst anns))
         => AddArg tp (Right ann) tps (Right (Lst anns)) where
  type AddedArg (Right ann) (Right (Lst anns)) = Right (Lst (ann ': anns))
  getAddedArg prTp _ (prTps::Proxy tps) _ (Cons ann anns) f
    = getRepr prTp ann $
      \(_::Proxy tp') -> getBoundedRepr prTps anns $
      \(_::Proxy tps') -> f (Proxy::Proxy (tp' ': tps'))
  addedArgAnn (ArgCons (DExpr _ ann) xs) = Cons ann (boundedArgAnn xs)
  withAddedArgs (ArgCons (DExpr x ann) xs) f
    = withBoundedArgs xs $ \xs' ann' -> f (T.Arg x xs') (Cons ann ann')
  addedArgContext _ _ = BoundedLstInfoD Proxy Dict
#if __GLASGOW_HASKELL__ < 710
  typeOfAddArg (_::Proxy (tp ': tps))
    = mkTyConApp
      (mkTyCon3 "smtlib2" "Language.SMTLib2" "':")
      [typeOf (Proxy::Proxy tp)
      ,typeOfBoundedLst (Proxy::Proxy tps)]
#endif

instance (Backend b,SMTType tp,BoundedLst '[tp])
         => Args (SMTExpr b tp) where
  type ArgBackend (SMTExpr b tp) = b
  type ArgRepr (SMTExpr b tp) = BoundedLstRepr '[tp]
  getArgRepr (_::Proxy (SMTExpr b tp)) ann f
    = getBoundedRepr (Proxy::Proxy '[tp]) ann f
  argAnnotation e = boundedArgAnn (ArgCons e ArgNil)
  argContext (_::Proxy (SMTExpr b tp))
    = case boundedLstContext (Proxy::Proxy '[tp]) of
        BoundedLstInfoS pr Dict -> ArgInfoS pr Dict
        BoundedLstInfoD pr Dict -> ArgInfoD pr Dict
  toArgs x = toBoundedArgs (ArgCons x ArgNil)
  withArgs x = withBoundedArgs (ArgCons x ArgNil)

instance (Backend b,
          SMTType t1,SMTType t2,
          BoundedLst '[t1,t2])
         => Args (SMTExpr b t1,SMTExpr b t2) where
  type ArgBackend (SMTExpr b t1,SMTExpr b t2) = b
  type ArgRepr (SMTExpr b t1,SMTExpr b t2) = BoundedLstRepr '[t1,t2]
  getArgRepr (_::Proxy (SMTExpr b t1,SMTExpr b t2)) ann f
    = getBoundedRepr (Proxy::Proxy '[t1,t2]) ann f
  argAnnotation (e1,e2) = boundedArgAnn (ArgCons e1 (ArgCons e2 ArgNil))
  argContext (_::Proxy (SMTExpr b t1,SMTExpr b t2))
    = case boundedLstContext (Proxy::Proxy '[t1,t2]) of
        BoundedLstInfoS pr Dict -> ArgInfoS pr Dict
        BoundedLstInfoD pr Dict -> ArgInfoD pr Dict
  toArgs (x1,x2) = toBoundedArgs (ArgCons x1 (ArgCons x2 ArgNil))
  withArgs (x1,x2) = withBoundedArgs (ArgCons x1 (ArgCons x2 ArgNil))

instance (Backend b,
          SMTType t1,SMTType t2,SMTType t3,
          BoundedLst '[t1,t2,t3])
         => Args (SMTExpr b t1,SMTExpr b t2,SMTExpr b t3) where
  type ArgBackend (SMTExpr b t1,SMTExpr b t2,SMTExpr b t3) = b
  type ArgRepr (SMTExpr b t1,SMTExpr b t2,SMTExpr b t3) = BoundedLstRepr '[t1,t2,t3]
  getArgRepr (_::Proxy (SMTExpr b t1,SMTExpr b t2,SMTExpr b t3)) ann f
    = getBoundedRepr (Proxy::Proxy '[t1,t2,t3]) ann f
  argAnnotation (e1,e2,e3) = boundedArgAnn (ArgCons e1 (ArgCons e2 (ArgCons e3 ArgNil)))
  argContext (_::Proxy (SMTExpr b t1,SMTExpr b t2,SMTExpr b t3))
    = case boundedLstContext (Proxy::Proxy '[t1,t2,t3]) of
        BoundedLstInfoS pr Dict -> ArgInfoS pr Dict
        BoundedLstInfoD pr Dict -> ArgInfoD pr Dict
  toArgs (x1,x2,x3) = toBoundedArgs (ArgCons x1 (ArgCons x2 (ArgCons x3 ArgNil)))
  withArgs (x1,x2,x3) = withBoundedArgs (ArgCons x1 (ArgCons x2 (ArgCons x3 ArgNil)))

class (SMTType tp,SMTRepr tp ~ tp',ArgListRepr tp tp' ~ repr) => ArgList tp tp' repr where
  type ArgListRepr tp tp'
  getArgListRepr :: Proxy tp -> Proxy tp' -> repr
                 -> (forall arg. T.Liftable arg => Proxy arg -> a)
                 -> a
  mkArgListRepr :: [SMTExpr b tp]
                -> (forall repr. T.Liftable repr => T.Args (SMTExpr' b) repr
                                                 -> ArgListRepr tp tp' -> a)
                -> a

instance (SMTType tp,SMTRepr tp ~ Left tp',T.GetType tp')
         => ArgList tp (Left tp') Integer where
  type ArgListRepr tp (Left tp') = Integer
  getArgListRepr _ (_::Proxy (Left tp')) len f
    = g len f
    where
      g :: Integer -> (forall arg. T.Liftable arg => Proxy arg -> a) -> a
      g 0 f = f (Proxy::Proxy ('[]::[T.Type]))
      g n f = g (n-1) (\(_::Proxy tps) -> f (Proxy::Proxy (tp' ': tps)))
  mkArgListRepr [] f = f T.NoArg 0
  mkArgListRepr ((SExpr x):xs) f = mkArgListRepr xs (\xs' n -> f (T.Arg x xs') (n+1))

instance (SMTType tp,SMTRepr tp ~ Right ann) => ArgList tp (Right ann) (ann,Integer) where
  type ArgListRepr tp (Right ann) = (ann,Integer)
  getArgListRepr prTp (_::Proxy (Right ann)) (ann,len) f
    = getRepr prTp ann $
      \pr -> g pr len f
    where
      g :: T.GetType tp' => Proxy (tp'::T.Type) -> Integer -> (forall arg. T.Liftable arg => Proxy arg -> a) -> a
      g _ 0 f = f (Proxy::Proxy ('[]::[T.Type]))
      g pr@(_::Proxy tp') n f = g pr (n-1) (\(_::Proxy tps) -> f (Proxy::Proxy (tp' ': tps)))
  mkArgListRepr [DExpr x ann] f = f (T.Arg x T.NoArg) (ann,0)
  mkArgListRepr (DExpr x _:xs) f = mkArgListRepr xs (\xs' (ann,n) -> f (T.Arg x xs') (ann,n+1))

instance (Backend b,Typeable tp,ArgList tp (SMTRepr tp) repr) => Args [SMTExpr b tp] where
  type ArgBackend [SMTExpr b tp] = b
  type ArgRepr [SMTExpr b t] = Right (ArgListRepr t (SMTRepr t))
  getArgRepr (Proxy::Proxy [SMTExpr b t]) ann f
    = getArgListRepr (Proxy::Proxy t) (Proxy::Proxy (SMTRepr t)) ann f
  withArgs = mkArgListRepr
  argContext _ = ArgInfoD Proxy Dict

and' :: Backend b => [SMTExpr b Bool] -> SMTExpr b Bool
and' (xs::[SMTExpr b Bool])
  = allEqFromList
    (fmap (\(SExpr e) -> e) xs :: [SMTExpr' b T.BoolType])
    (SExpr . SMTExpr' . App (Logic And))

(.&&.) :: Backend b => SMTExpr b Bool -> SMTExpr b Bool -> SMTExpr b Bool
(.&&.) (SExpr x) (SExpr y) = SExpr (SMTExpr' (App (Logic And) (T.Arg x (T.Arg y T.NoArg))))

not' :: Backend b => SMTExpr b Bool -> SMTExpr b Bool
not' (SExpr x) = SExpr (SMTExpr' (App Not (T.Arg x T.NoArg)))

(.==.) :: (Backend b,SMTType t) => SMTExpr b t -> SMTExpr b t -> SMTExpr b Bool
(.==.) (SExpr e1) (SExpr e2)
  = SExpr (SMTExpr' $ App Eq (T.Arg e1 (T.Arg e2 T.NoArg)))
(.==.) (DExpr e1 _) (DExpr e2 _)
  = SExpr (SMTExpr' $ App Eq (T.Arg e1
                              (T.Arg (mkEqual e1 e2) T.NoArg)))
  where
    mkEqual :: (Backend b,T.GetType t1,T.GetType t2)
            => SMTExpr' b t1 -> SMTExpr' b t2 -> SMTExpr' b t1
#if __GLASGOW_HASKELL__ >= 710
    mkEqual _ e2 = case gcast e2 of
      Just r -> r
#else
    mkEqual _ e2 = case cast e2 of
      Just r -> r
#endif

eq :: (Backend b,SMTType t) => [SMTExpr b t] -> SMTExpr b Bool
eq xs@(SExpr _:_)
  = allEqFromList
    (fmap getExpr xs)
    (SExpr . SMTExpr' . App Eq)
  where
    getExpr :: SMTRepr t ~ Left tp => SMTExpr b t -> SMTExpr' b tp
    getExpr (SExpr e) = e
eq xs@(DExpr x ann:_)
  = allEqFromList
    (fmap (getExpr x) xs)
    (SExpr . SMTExpr' . App Eq)
  where
    getExpr :: (T.GetType t1) => SMTExpr' b t1 -> SMTExpr b t2 -> SMTExpr' b t1
    getExpr _ (DExpr e _) = case gcast e of
      Just e' -> e'

allEqOfList :: T.GetType t => Proxy t
            -> Integer
            -> (forall arg. (AllEq (t ': arg),SameType (t ': arg) ~ t)
                => Proxy (t ': arg) -> a)
            -> a
allEqOfList (_::Proxy t) 1 f = f (Proxy::Proxy ('[t]::[T.Type]))
allEqOfList pr@(_::Proxy t) n f
  = allEqOfList pr (n-1) $
    \(_::Proxy (t ': ts)) -> f (Proxy::Proxy (t ': t ': ts))

checkSat :: Backend b => SMT' b B.CheckSatResult
checkSat = do
  b <- get
  (res,nb) <- liftSMT $ B.checkSat b Nothing (B.CheckSatLimits Nothing Nothing)
  put nb
  return res

toBackendExpr :: (Backend b,SMTType t,SMTRepr t ~ Left tp,T.GetType tp)
              => SMTExpr b t
              -> SMT' b (Expr b tp)
toBackendExpr (SExpr e) = evalStateT (toBackendExpr' e) IMap.empty

data AnyQVar b = forall t. T.GetType t => AnyQVar (QVar b t)

toBackendExpr' :: (Backend b,T.GetType tp) => SMTExpr' b tp
               -> StateT (IntMap [AnyQVar b]) (SMT' b) (Expr b tp)
toBackendExpr' (SMTExpr' e::SMTExpr' b tp) = do
  e1 <- mapExpr return
        (\(QVar' lvl n::QVar' t) -> do
           mp <- get
           case IMap.lookup lvl mp of
             Just vars -> case vars!!n of
               AnyQVar qv -> case gcast qv of
                 Just qv' -> return (qv'::QVar b t))
        return return return return
        toBackendExpr' e
  b <- lift get
  (e2,nb) <- lift $ liftSMT $ B.toBackend b e1
  lift $ put nb
  return e2
--toBackendExpr' (Quantification' q lvl vars body)

assert :: Backend b => SMTExpr b Bool -> SMT' b ()
assert e = do
  e' <- toBackendExpr e
  b <- get
  nb <- liftSMT $ B.assert b e'
  put nb

var :: (Backend b,SMTType t,SMTRepr t ~ Left tp,T.GetType tp) => SMT' b (SMTExpr b t)
var = do
  b <- get
  (v,nb) <- liftSMT $ B.declareVar b Nothing
  put nb
  return $ SExpr (SMTExpr' (Var v))

varAnn :: (Backend b,SMTType t,SMTRepr t ~ Right ann) => ann -> SMT' b (SMTExpr b t)
varAnn ann = with $ \pr -> do
  (b::b) <- get
  getRepr pr ann $
    \(_::Proxy t') -> do
       (v::Var b t',nb) <- liftSMT $ B.declareVar b Nothing
       put (nb::b)
       return (DExpr (SMTExpr' (Var v) :: SMTExpr' b t') ann)
  where
    with :: (Proxy t -> SMT' b (SMTExpr b t)) -> SMT' b (SMTExpr b t)
    with f = f Proxy

constant :: (Backend b,SMTValue b t,SMTRepr t ~ Left tp,T.GetType tp) => t -> SMTExpr b t
constant x = with $ \pr -> SExpr (SMTExpr' (Const (toValue pr x)))
  where
    with :: (Proxy b -> SMTExpr b t) -> SMTExpr b t
    with f = f Proxy

constantAnn :: (Backend b,SMTValue b t,SMTRepr t ~ Right ann) => t -> ann -> SMTExpr b t
constantAnn x ann = with $ \pr -> toDynValue pr x ann $ \val -> DExpr (SMTExpr' (Const val)) ann
  where
    with :: (Proxy b -> SMTExpr b t) -> SMTExpr b t
    with f = f Proxy

getValue :: (Backend b,SMTValue b t) => SMTExpr b t -> SMT' b t
getValue (SExpr e :: SMTExpr b t) = do
  e' <- evalStateT (toBackendExpr' e) IMap.empty
  b <- get
  (val,nb) <- liftSMT $ B.getValue b e'
  put nb
  return $ fromValue (Proxy::Proxy b) val
getValue (DExpr e ann :: SMTExpr b t) = do
  e' <- evalStateT (toBackendExpr' e) IMap.empty
  b <- get
  (val,nb) <- liftSMT $ B.getValue b e'
  put nb
  return $ fromDynValue (Proxy::Proxy b) val

constArray :: (Backend b,SMTType t,Args idx,ArgBackend idx ~ b,
               ArgRepr idx ~ Left tps,T.Liftable tps)
           => SMTExpr b t -> SMTExpr b (SMTArray idx t)
constArray (SExpr x) = SExpr $ SMTExpr' $ App ConstArray (T.Arg x T.NoArg)
constArray (DExpr (x::SMTExpr' b el) ann)
  = with $ \(_::Proxy tps)
    -> DExpr (SMTExpr' $ App ConstArray (T.Arg x T.NoArg)
              :: SMTExpr' b (T.ArrayType tps el)) ann
  where
    with :: ArgRepr idx ~ Left tps
         => (Proxy tps -> SMTExpr b (SMTArray idx t))
         -> SMTExpr b (SMTArray idx t)
    with f = f Proxy

select :: (Backend b,Args idx,ArgBackend idx ~ b,
           SMTType el,SMTRepr el ~ el',ArgRepr idx ~ idx',
           SMTArray' idx el idx' el')
       => SMTExpr b (SMTArray idx el) -> idx -> SMTExpr b el
select (arr :: SMTExpr b (SMTArray idx el)) idx = case typeContext (Proxy::Proxy el) of
  TypeInfoS { proxyS = _::Proxy el'
            , contextS = Dict } -> case argContext (Proxy::Proxy idx) of
    ArgInfoS { argContextS = Dict } -> case arr of
      SExpr arr' -> SExpr (SMTExpr' (App Select (T.Arg arr' (toArgs idx))))
    ArgInfoD { argContextD = Dict } -> case arr of
      DExpr arr ann -> withArgs idx $
                       \(idx'::T.Args (SMTExpr' b) idx') ann' -> case gcast arr of
                          Just arr' -> SExpr (SMTExpr' (App Select (T.Arg (arr' :: SMTExpr' b (T.ArrayType idx' el')) idx')))
  TypeInfoD { contextD = Dict } -> case argContext (Proxy::Proxy idx) of
    ArgInfoS { argProxyS = _::Proxy idx'
             , argContextS = Dict } -> case arr of
      DExpr arr ann -> getRepr (Proxy::Proxy el) ann $
                       \(_::Proxy el') -> case gcast arr of
        Just arr' -> DExpr (SMTExpr' (App Select (T.Arg (arr' :: SMTExpr' b (T.ArrayType idx' el')) (toArgs idx)))) ann
    ArgInfoD { argContextD = Dict } -> case arr of
      DExpr arr' (_,annEl)
        -> withArgs idx $
           \(idx'::T.Args (SMTExpr' b) idx') annIdx -> getRepr (Proxy::Proxy el) annEl $
           \(_::Proxy el') -> case gcast arr' of
             Just arr'' -> DExpr (SMTExpr' (App Select (T.Arg (arr''::SMTExpr' b (T.ArrayType idx' el')) idx'))) annEl

store :: (Backend b,Args idx,ArgBackend idx ~ b,
          SMTType el,SMTRepr el ~ el',ArgRepr idx ~ idx',
          SMTArray' idx el idx' el')
      => SMTExpr b (SMTArray idx el) -> idx -> SMTExpr b el -> SMTExpr b (SMTArray idx el)
store (arr :: SMTExpr b (SMTArray idx el)) idx val = case typeContext (Proxy::Proxy el) of
  TypeInfoS { proxyS = _::Proxy el'
            , contextS = Dict } -> case val of
    SExpr val' -> case argContext (Proxy::Proxy idx) of
      ArgInfoS { argContextS = Dict } -> case arr of
        SExpr arr' -> SExpr (SMTExpr' (App Store (T.Arg arr' (T.Arg val' (toArgs idx)))))
      ArgInfoD { argContextD = Dict } -> case arr of
        DExpr arr' ann -> withArgs idx $
                          \(idx'::T.Args (SMTExpr' b) idx') ann'
                          -> case gcast arr' of
          Just arr'' -> DExpr (SMTExpr' (App Store
                                         (T.Arg (arr'' :: SMTExpr' b (T.ArrayType idx' el'))
                                          (T.Arg val' idx')))) ann
  TypeInfoD { contextD = Dict } -> case val of
    DExpr val' _ -> case argContext (Proxy::Proxy idx) of
      ArgInfoS { argProxyS = _::Proxy idx'
               , argContextS = Dict } -> case arr of
        DExpr arr' ann -> getRepr (Proxy::Proxy el) ann $
                        \(_::Proxy el') -> case gcast arr' of
          Just arr'' -> case gcast val' of
            Just val'' -> DExpr (SMTExpr' (App Store
                                           (T.Arg (arr'' :: SMTExpr' b (T.ArrayType idx' el'))
                                            (T.Arg val'' (toArgs idx))))) ann
      ArgInfoD { argContextD = Dict } -> case arr of
        DExpr arr' ann@(annIdx,annEl)
          -> withArgs idx $
             \(idx'::T.Args (SMTExpr' b) idx') annIdx -> getRepr (Proxy::Proxy el) annEl $
             \(_::Proxy el') -> case gcast arr' of
          Just arr'' -> case gcast val' of
            Just val'' -> DExpr (SMTExpr' (App Store
                                           (T.Arg (arr'' :: SMTExpr' b (T.ArrayType idx' el'))
                                            (T.Arg val'' idx')))) ann

data SMTFunction b arg res where
  SFunS :: (Args arg,SMTType res,ArgBackend arg ~ b,
            ArgRepr arg ~ Left arg',SMTRepr res ~ Left res',
            T.Liftable arg',T.GetType res')
        => Function (Fun b) (Constr b) (Field b) arg' res'
        -> SMTFunction b arg res
  SFunD :: (Args arg,SMTType res,ArgBackend arg ~ b,
            ArgRepr arg ~ Left arg',SMTRepr res ~ Right res',
            T.Liftable arg',T.GetType res'')
        => res' -> Function (Fun b) (Constr b) (Field b) arg' res''
        -> SMTFunction b arg res
  DFunS :: (Args arg,SMTType res,ArgBackend arg ~ b,
            ArgRepr arg ~ Right arg',SMTRepr res ~ Left res',
            T.Liftable arg'',T.GetType res')
        => arg' -> Function (Fun b) (Constr b) (Field b) arg'' res'
        -> SMTFunction b arg res
  DFunD :: (Args arg,SMTType res,ArgBackend arg ~ b,
            ArgRepr arg ~ Right arg',SMTRepr res ~ Right res',
            T.Liftable arg'',T.GetType res'')
        => arg' -> res' -> Function (Fun b) (Constr b) (Field b) arg'' res''
        -> SMTFunction b arg res
  OFunS :: (Args arg,SMTType res,ArgBackend arg ~ b,
            ArgRepr arg ~ Right arg',SMTRepr res ~ Left res',
            T.GetType res')
        => String
        -> (forall a. arg' -> (forall arg''. T.Liftable arg''
                               => Function (Fun b) (Constr b) (Field b) arg'' res'
                               -> a) -> a)
        -> SMTFunction b arg res
  OFunD :: (Args arg,SMTType res,ArgBackend arg ~ b,
            ArgRepr arg ~ Right arg',SMTRepr res ~ Right res')
        => String
        -> (forall a. arg' -> (forall arg'' res''. (T.Liftable arg'',T.GetType res'')
                               => res'
                               -> Function (Fun b) (Constr b) (Field b) arg'' res''
                               -> a) -> a)
        -> SMTFunction b arg res

app :: SMTFunction b arg res -> arg -> SMTExpr b res
app (SFunS fun) arg = SExpr (SMTExpr' (App fun (toArgs arg)))
app (SFunD ann fun) arg = DExpr (SMTExpr' (App fun (toArgs arg))) ann
app (DFunS ann fun) arg
  = withArgs arg $
    \arg' ann' -> case gcast arg' of
       Just arg'' -> SExpr (SMTExpr' (App fun arg''))
app (DFunD annArg annRes fun) arg
  = withArgs arg $
    \arg' ann' -> case gcast arg' of
       Just arg'' -> DExpr (SMTExpr' (App fun arg'')) annRes
app (OFunS _ fun) arg
  = withArgs arg $
    \arg' ann -> fun ann $ \fun' -> case gcast arg' of
       Just arg'' -> SExpr (SMTExpr' (App fun' arg''))
app (OFunD _ fun) arg
  = withArgs arg $
    \arg' ann -> fun ann $ \ann' fun' -> case gcast arg' of
       Just arg'' -> DExpr (SMTExpr' (App fun' arg'')) ann'

fun :: (Args arg,SMTType res,ArgRepr arg ~ Left arg',SMTRepr res ~ Left res',
        T.Liftable arg',T.GetType res',ArgBackend arg ~ b)
    => SMT' b (SMTFunction b arg res)
fun = do
  b <- get
  (fun,nb) <- liftSMT $ declareFun b Nothing
  put nb
  return (SFunS (Fun fun))

funAnnRet :: (Args arg,SMTType res,
              ArgRepr arg ~ Left arg',SMTRepr res ~ Right res',
              T.Liftable arg',ArgBackend arg ~ b)
          => res' -> SMT' b (SMTFunction b arg res)
funAnnRet annRes
  = with $ \(_::Proxy b) (_::Proxy arg') prRes
    -> getRepr prRes annRes $ \(_::Proxy rRes)
    -> do
       b <- get
       (fun::Fun b arg' rRes,nb)
         <- liftSMT $ declareFun b Nothing
       put nb
       return (SFunD annRes (Fun fun))
  where
    with :: (ArgRepr arg ~ Left arg') => (Proxy b -> Proxy arg' -> Proxy res -> SMT' b (SMTFunction b arg res))
         -> SMT' b (SMTFunction b arg res)
    with f = f Proxy Proxy Proxy

funAnnArg :: (Args arg,SMTType res,
              ArgRepr arg ~ Right arg',SMTRepr res ~ Left res',
              T.GetType res',ArgBackend arg ~ b)
          => arg' -> SMT' b (SMTFunction b arg res)
funAnnArg argAnn
  = with $ \(_::Proxy b) prArg (_::Proxy res')
    -> getArgRepr prArg argAnn $ \(_::Proxy rArg)
    -> do
       b <- get
       (fun::Fun b rArg res',nb)
         <- liftSMT $ declareFun b Nothing
       put nb
       return (DFunS argAnn (Fun fun))
  where
    with :: (SMTRepr res ~ Left res') => (Proxy b -> Proxy arg -> Proxy res' -> SMT' b (SMTFunction b arg res))
         -> SMT' b (SMTFunction b arg res)
    with f = f Proxy Proxy Proxy

funAnn :: (Args arg,SMTType res,
           ArgRepr arg ~ Right arg',SMTRepr res ~ Right res',
           ArgBackend arg ~ b)
       => arg' -> res' -> SMT' b (SMTFunction b arg res)
funAnn annArg annRes
  = with $ \(_::Proxy b) prArg prRes
    -> getArgRepr prArg annArg $ \(_::Proxy rArg)
    -> getRepr prRes annRes $ \(_::Proxy rRes)
    -> do
       b <- get
       (fun::Fun b rArg rRes,nb)
         <- liftSMT $ declareFun b Nothing
       put nb
       return (DFunD annArg annRes (Fun fun))
  where
    with :: (Proxy b -> Proxy arg -> Proxy res -> SMT' b (SMTFunction b arg res))
         -> SMT' b (SMTFunction b arg res)
    with f = f Proxy Proxy Proxy

asArray :: SMTFunction b arg res -> SMTExpr b (SMTArray arg res)
asArray (SFunS fun) = SExpr (SMTExpr' (AsArray fun))
asArray (SFunD ann fun) = DExpr (SMTExpr' (AsArray fun)) ann
asArray (DFunS ann fun) = DExpr (SMTExpr' (AsArray fun)) ann
asArray (DFunD annArg annRes fun) = DExpr (SMTExpr' (AsArray fun)) (annArg,annRes)
asArray (OFunS name _) = error $ "smtlib2: Cannot use overloaded function "++show name++
                                   " as an argument of asArray."
asArray (OFunD name _) = error $ "smtlib2: Cannot use overloaded function "++show name++
                                 " as an argument of asArray."

sig :: (ArgRepr arg ~ Right arg')
    => SMTFunction b arg res -> arg' -> SMTFunction b arg res
sig (OFunD _ f) annArg = f annArg $ \annRes fun -> DFunD annArg annRes fun
sig (OFunS _ f) annArg = f annArg $ \fun -> DFunS annArg fun
sig fun _ = fun

--forall :: (Args arg,ArgRepr arg ~ Left arg') => (arg -> SMTExpr b Bool) -> SMTExpr b Bool
--forall f = 

fNot :: Backend b => SMTFunction b (SMTExpr b Bool) Bool
fNot = SFunS Not

fPlus :: Backend b => SMTFunction b [SMTExpr b Integer] Integer
fPlus = OFunS "+" (\len f -> allEqOfList (Proxy::Proxy T.IntType) len $
                   \(_::Proxy (T.IntType ': arg))
                   -> f (ArithInt Plus :: Function fun con field (T.IntType ': arg) T.IntType))

withBackend :: Backend b => b -> SMT' b a -> SMTMonad b a
withBackend b (SMT' act) = do
  (res,nb) <- runStateT act b
  return res
