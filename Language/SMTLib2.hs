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
       ()
       where

import qualified Language.SMTLib2.Internals.Type as T
import Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Expression as E

import Control.Monad.State
import Control.Monad.Identity
import Data.Typeable

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

data SMTArray idx t = SMTArray
data SMTBV = SMTBV

class (Typeable t) => SMTType b t where
  type SMTRepr t :: Either T.Type *
  getRepr :: (SMTRepr t ~ Right ann)
          => Proxy b -> Proxy t -> ann
          -> (forall t'. T.GetType t' => Proxy t' -> a)
          -> a
  getRepr _ p = error $ "smtlib2: getRepr not implemented for type "++show (typeRep p)

data Lst (a :: [*]) where
  Nil :: Lst '[]
  Cons :: t -> Lst ts -> Lst (t ': ts)

data ArgLst (e :: * -> *) (arg :: [*]) where
  ArgNil :: ArgLst e '[]
  ArgCons :: e t -> ArgLst e ts -> ArgLst e (t ': ts)

class (Typeable arg) => Args b arg where
  type ArgRepr arg :: Either [T.Type] *
  getArgRepr :: (ArgRepr arg ~ Right ann)
             => Proxy b -> Proxy arg -> ann
             -> (forall arg'. T.Liftable arg' => Proxy arg' -> a)
             -> a
  getArgRepr _ p = error $ "smtlib2: getArgRepr not implemented for type "++show (typeRep p)
  mkArgs :: arg -> SMTArgs b arg
  toArgs :: (ArgRepr arg ~ Left arg') => arg -> T.Args (SMTExpr' b) arg'
  toArgs (_::arg) = error $ "smtlib2: toArgs not implemented for type "++
                            show (typeRep (Proxy::Proxy arg))
  argAnnotation :: (ArgRepr arg ~ Right ann) => arg -> ann
  argAnnotation (_::arg) = error $ "smtlib2: argAnnotation not implemented for type "++
                                   show (typeRep (Proxy::Proxy arg))

instance SMTType b Bool where
  type SMTRepr Bool = Left T.BoolType

class SMTArray' b idx el (idx' :: Either [T.Type] *) (el' :: Either T.Type *) where
  type ArrayRepr idx' el' :: Either T.Type *
  getArrayRepr :: (ArrayRepr idx' el' ~ Right ann)
               => Proxy '(idx',el') -> Proxy b -> Proxy (SMTArray idx el) -> ann
               -> (forall idx'' el''. (T.Liftable idx'',T.GetType el'')
                   => Proxy (T.ArrayType idx'' el'') -> a)
               -> a
  getArrayRepr = error $ "smtlib2: getArrayRepr not implemented."


-- Both arguments static
instance (Args b idx,SMTType b el,ArgRepr idx ~ Left idx',SMTRepr el ~ Left el')
         => SMTArray' b idx el (Left idx') (Left el') where
  type ArrayRepr (Left idx') (Left el') = Left (T.ArrayType idx' el')

-- Index static, element dynamic
instance (Args b idx,SMTType b el,ArgRepr idx ~ Left idx',SMTRepr el ~ Right el',T.Liftable idx')
         => SMTArray' b idx el (Left idx') (Right el') where
  type ArrayRepr (Left idx') (Right el') = Right el'
  getArrayRepr (_::Proxy '(Left idx',Right el')) prB (_::Proxy (SMTArray idx el)) eann f
    = getRepr prB (Proxy::Proxy el) eann $
      \(Proxy::Proxy tel) -> f (Proxy::Proxy (T.ArrayType idx' tel))

-- Index dynamic, element static
instance (Args b idx,SMTType b el,ArgRepr idx ~ Right idx',SMTRepr el ~ Left el',T.GetType el')
         => SMTArray' b idx el (Right idx') (Left el') where
  type ArrayRepr (Right idx') (Left el') = Right idx'
  getArrayRepr (_::Proxy '(Right idx',Left el')) prB (_::Proxy (SMTArray idx el)) iann f
    = getArgRepr prB (Proxy::Proxy idx) iann $
      \(Proxy::Proxy tidx) -> f (Proxy::Proxy (T.ArrayType tidx el'))

-- Both arguments dynamic
instance (Args b idx,SMTType b el,ArgRepr idx ~ Right idx',SMTRepr el ~ Right el')
         => SMTArray' b idx el (Right idx') (Right el') where
  type ArrayRepr (Right idx') (Right el') = Right (idx',el')
  getArrayRepr _ prB (_::Proxy (SMTArray idx el)) (iann,eann) f
    = getArgRepr prB (Proxy::Proxy idx) iann $
      \(_::Proxy tidx) -> getRepr prB (Proxy::Proxy el) eann $
      \(_::Proxy tel) -> f (Proxy::Proxy (T.ArrayType tidx tel))

instance (Args b idx,SMTType b el,SMTArray' b idx el (ArgRepr idx) (SMTRepr el))
         => SMTType b (SMTArray idx el) where
  type SMTRepr (SMTArray idx el) = ArrayRepr (ArgRepr idx) (SMTRepr el)
  getRepr pB pr@(_::Proxy (SMTArray idx el))
    = getArrayRepr (Proxy::Proxy '(ArgRepr idx,SMTRepr el)) pB pr

newtype SMTExpr' b t = SMTExpr' (Expression (Var b) (QVar b) (Fun b) (B.Constr b) (B.Field b) (FunArg b) (SMTExpr' b) t)

data SMTExpr b t where
  SExpr :: (SMTType b t,SMTRepr t ~ Left repr,T.GetType repr) => SMTExpr' b repr -> SMTExpr b t
  DExpr :: (SMTType b t,SMTRepr t ~ Right ann,T.GetType repr) => SMTExpr' b repr -> ann -> SMTExpr b t

withSMTExpr :: SMTExpr b t -> (forall repr. T.GetType repr => SMTExpr' b repr -> a) -> a
withSMTExpr (SExpr e) f = f e
withSMTExpr (DExpr e _) f = f e

class (SMTType b tp,SMTRepr tp ~ tp',BoundedLst b tps,BoundedLstRepr tps ~ lst)
      => AddArg b tp tp' (tps :: [*]) (lst :: Either [T.Type] *) where
  type AddedArg tp' lst :: Either [T.Type] *
  getAddedArg :: (AddedArg tp' lst ~ Right anns)
              => Proxy b -> Proxy tp -> Proxy tp' -> Proxy tps -> Proxy lst -> anns
                 -> (forall (arg :: [T.Type]). T.Liftable arg => Proxy arg -> a)
                 -> a
  getAddedArg _ pr = error $ "smtlib2: getAddedArg not implemented for "++show (typeRep pr)
  toAddedArg :: (AddedArg tp' lst ~ Left tps')
             => ArgLst (SMTExpr b) (tp ': tps)
             -> T.Args (SMTExpr' b) tps'
  toAddedArg (_::ArgLst (SMTExpr b) (tp ': tps))
    = error $ "smtlib2: toAddedArg not implemented for "++
              show (typeRep (Proxy::Proxy tp))++" and "++
              show (typeRep (Proxy::Proxy tps))
  withAddedArg :: ArgLst (SMTExpr b) (tp ': tps)
               -> (forall repr. (AddedArg (SMTRepr tp) (BoundedLstRepr tps) ~ Left repr,
                                 T.Liftable repr)
                   => T.Args (SMTExpr' b) repr -> a)
               -> (forall ann repr. (AddedArg (SMTRepr tp) (BoundedLstRepr tps) ~ Right ann,
                                     T.Liftable repr)
                   => T.Args (SMTExpr' b) repr -> ann -> a)
               -> a
  addedArgAnn :: (AddedArg (SMTRepr tp) (BoundedLstRepr tps) ~ Right ann)
              => ArgLst (SMTExpr b) (tp ': tps)
              -> ann
  addedArgAnn (_::ArgLst (SMTExpr b) (tp ': tps))
    = error $ "smtlib2: addedArgAnn not implemented for "++
              show (typeRep (Proxy::Proxy tp))++" and "++
              show (typeRep (Proxy::Proxy tps))

class Typeable tps => BoundedLst b (tps :: [*]) where
  type BoundedLstRepr tps :: Either [T.Type] *
  getBoundedRepr :: (BoundedLstRepr tps ~ Right anns)
                 => Proxy b -> Proxy tps -> anns
                 -> (forall (arg :: [T.Type]). T.Liftable arg => Proxy arg -> a)
                 -> a
  getBoundedRepr _ pr
    = error $ "smtlib2: getBoundedRepr not implemented for "++show (typeRep pr)
  toBoundedArgs :: (BoundedLstRepr tps ~ Left tps')
                => ArgLst (SMTExpr b) tps -> T.Args (SMTExpr' b) tps'
  toBoundedArgs (_::ArgLst (SMTExpr b) tps)
    = error $ "smtlib2: toBoundedArgs not implemented for "++
              show (typeRep (Proxy::Proxy tps))
  withBoundedArgs :: ArgLst (SMTExpr b) tps
                  -> (forall repr. (BoundedLstRepr tps ~ Left repr,
                                    T.Liftable repr)
                      => T.Args (SMTExpr' b) repr -> a)
                  -> (forall ann repr. (BoundedLstRepr tps ~ Right ann,T.Liftable repr)
                      => T.Args (SMTExpr' b) repr -> ann -> a)
                  -> a
  boundedArgAnn :: (BoundedLstRepr tps ~ Right ann)
                => ArgLst (SMTExpr b) tps
                -> ann
  boundedArgAnn (_::ArgLst (SMTExpr b) tps)
    = error $ "smtlib2: boundedArgAnn not implemented for "++
               show (typeRep (Proxy::Proxy tps))

instance BoundedLst b '[] where
  type BoundedLstRepr '[] = Left '[]
  toBoundedArgs _ = T.NoArg
  withBoundedArgs _ f _ = f T.NoArg

instance (BoundedLst b tps,AddArg b tp tp' tps (BoundedLstRepr tps))
         => BoundedLst b (tp ': tps) where
  type BoundedLstRepr (tp ': tps) = AddedArg (SMTRepr tp) (BoundedLstRepr tps)
  getBoundedRepr prB (_::Proxy (tp ': tps)) anns f
    = getAddedArg prB (Proxy::Proxy tp)
                      (Proxy::Proxy (SMTRepr tp))
                      (Proxy::Proxy tps)
                      (Proxy::Proxy (BoundedLstRepr tps)) anns f
  toBoundedArgs = toAddedArg
  withBoundedArgs = withAddedArg
  boundedArgAnn = addedArgAnn

instance (SMTType b tp,SMTRepr tp ~ Left tp',
          BoundedLst b tps,BoundedLstRepr tps ~ Left tps',T.Liftable tps')
         => AddArg b tp (Left tp') tps (Left tps') where
  type AddedArg (Left tp') (Left tps') = Left (tp' ': tps')
  toAddedArg (ArgCons (SExpr x) xs) = T.Arg x (toBoundedArgs xs)
  withAddedArg (ArgCons (SExpr x) xs) f g
    = f (T.Arg x (toBoundedArgs xs))

instance (SMTType b tp,SMTRepr tp ~ Left tp',T.GetType tp',
          BoundedLst b tps,BoundedLstRepr tps ~ Right (Lst anns))
         => AddArg b tp (Left tp') tps (Right (Lst anns)) where
  type AddedArg (Left tp') (Right (Lst anns)) = Right (Lst anns)
  getAddedArg prB _ (_::Proxy (Left tp')) prTps _ anns f
    = getBoundedRepr prB prTps anns $
      \(_::Proxy arg) -> f (Proxy::Proxy (tp' ': arg))
  withAddedArg (ArgCons (SExpr x) xs) f g
    = argLstToArgs xs (\xs' -> g (T.Arg x xs') (boundedArgAnn xs))
  addedArgAnn (ArgCons _ xs) = boundedArgAnn xs

argLstToArgs :: ArgLst (SMTExpr b) arg
             -> (forall repr. T.Liftable repr => T.Args (SMTExpr' b) repr -> a)
             -> a
argLstToArgs ArgNil f = f T.NoArg
argLstToArgs (ArgCons (SExpr x) xs) f
  = argLstToArgs xs (\xs' -> f (T.Arg x xs'))
argLstToArgs (ArgCons (DExpr x _) xs) f
  = argLstToArgs xs (\xs' -> f (T.Arg x xs'))

instance (SMTType b tp,SMTRepr tp ~ Right ann,
          BoundedLst b tps,BoundedLstRepr tps ~ Left tps',T.Liftable tps')
         => AddArg b tp (Right ann) tps (Left tps') where
  type AddedArg (Right ann) (Left tps') = Right (Lst '[ann])
  getAddedArg prB prTp _ _ (_::Proxy (Left tps')) (Cons ann Nil) f
    = getRepr prB prTp ann $
      \(_::Proxy tp') -> f (Proxy::Proxy (tp' ': tps'))
  withAddedArg (ArgCons (DExpr x ann) xs) f g
    = g (T.Arg x (toBoundedArgs xs)) (Cons ann Nil)
  addedArgAnn (ArgCons (DExpr _ ann) _) = Cons ann Nil

instance (SMTType b tp,SMTRepr tp ~ Right ann,
          BoundedLst b tps,BoundedLstRepr tps ~ Right (Lst anns))
         => AddArg b tp (Right ann) tps (Right (Lst anns)) where
  type AddedArg (Right ann) (Right (Lst anns)) = Right (Lst (ann ': anns))
  getAddedArg prB prTp _ prTps _ (Cons ann anns) f
    = getRepr prB prTp ann $
      \(_::Proxy tp') -> getBoundedRepr prB prTps anns $
      \(_::Proxy tps') -> f (Proxy::Proxy (tp' ': tps'))
  withAddedArg (ArgCons (DExpr x ann) xs) f g
    = argLstToArgs xs $
      \xs' -> g (T.Arg x xs') (Cons ann (boundedArgAnn xs))
  addedArgAnn (ArgCons (DExpr _ ann) xs) = Cons ann (boundedArgAnn xs)

instance Args b () where
  type ArgRepr () = Left '[]
  toArgs _ = T.NoArg
  mkArgs _ = SArg T.NoArg

instance (Typeable b,SMTType b tp,BoundedLst b '[tp]) => Args b (SMTExpr b tp) where
  type ArgRepr (SMTExpr b tp) = BoundedLstRepr '[tp]
  getArgRepr prB (_::Proxy (SMTExpr b tp)) ann f
    = getBoundedRepr prB (Proxy::Proxy '[tp]) ann f
  mkArgs x = withBoundedArgs (ArgCons x ArgNil) SArg DArg
  argAnnotation e = boundedArgAnn (ArgCons e ArgNil)

instance (Typeable b,
          SMTType b t1,SMTType b t2,
          BoundedLst b '[t1,t2])
         => Args b (SMTExpr b t1,SMTExpr b t2) where
  type ArgRepr (SMTExpr b t1,SMTExpr b t2) = BoundedLstRepr '[t1,t2]
  getArgRepr prB (_::Proxy (SMTExpr b t1,SMTExpr b t2)) ann f
    = getBoundedRepr prB (Proxy::Proxy '[t1,t2]) ann f
  mkArgs (x1,x2) = withBoundedArgs (ArgCons x1
                                    (ArgCons x2
                                     ArgNil)) SArg DArg
  argAnnotation (e1,e2) = boundedArgAnn (ArgCons e1 (ArgCons e2 ArgNil))

instance (Typeable b,
          SMTType b t1,SMTType b t2,SMTType b t3,
          BoundedLst b '[t1,t2,t3])
         => Args b (SMTExpr b t1,SMTExpr b t2,SMTExpr b t3) where
  type ArgRepr (SMTExpr b t1,SMTExpr b t2,SMTExpr b t3) = BoundedLstRepr '[t1,t2,t3]
  getArgRepr prB (_::Proxy (SMTExpr b t1,SMTExpr b t2,SMTExpr b t3)) ann f
    = getBoundedRepr prB (Proxy::Proxy '[t1,t2,t3]) ann f
  mkArgs (x1,x2,x3)
    = withBoundedArgs (ArgCons x1
                       (ArgCons x2
                        (ArgCons x3
                         ArgNil))) SArg DArg
  argAnnotation (e1,e2,e3) = boundedArgAnn (ArgCons e1 (ArgCons e2 (ArgCons e3 ArgNil)))

class (SMTType b tp,SMTRepr tp ~ tp',ArgListRepr tp tp' ~ repr) => ArgList b tp tp' repr where
  type ArgListRepr t tp'
  getArgListRepr :: Proxy b -> Proxy tp -> Proxy tp' -> repr
                 -> (forall arg. T.Liftable arg => Proxy arg -> a)
                 -> a

instance (SMTType b tp,SMTRepr tp ~ Left tp',T.GetType tp')
         => ArgList b tp (Left tp') Integer where
  type ArgListRepr tp (Left tp') = Integer
  getArgListRepr prB _ (_::Proxy (Left tp')) len f
    = g len f
    where
      g :: Integer -> (forall arg. T.Liftable arg => Proxy arg -> a) -> a
      g 0 f = f (Proxy::Proxy ('[]::[T.Type]))
      g n f = g (n-1) (\(_::Proxy tps) -> f (Proxy::Proxy (tp' ': tps)))

instance (SMTType b tp,SMTRepr tp ~ Right ann) => ArgList b tp (Right ann) (ann,Integer) where
  type ArgListRepr tp (Right ann) = (ann,Integer)
  getArgListRepr prB prTp (_::Proxy (Right ann)) (ann,len) f
    = getRepr prB prTp ann $
      \pr -> g pr len f
    where
      g :: T.GetType tp' => Proxy (tp'::T.Type) -> Integer -> (forall arg. T.Liftable arg => Proxy arg -> a) -> a
      g _ 0 f = f (Proxy::Proxy ('[]::[T.Type]))
      g pr@(_::Proxy tp') n f = g pr (n-1) (\(_::Proxy tps) -> f (Proxy::Proxy (tp' ': tps)))

instance (Typeable b,Typeable tp,ArgList b tp (SMTRepr tp) repr) => Args b [SMTExpr b tp] where
  type ArgRepr [SMTExpr b t] = Right (ArgListRepr t (SMTRepr t))
  getArgRepr prB (Proxy::Proxy [SMTExpr b t]) ann f
    = getArgListRepr prB (Proxy::Proxy t) (Proxy::Proxy (SMTRepr t)) ann f
  {-mkArgs xs = fromLst xs DArg
    where
      fromLst :: [SMTExpr b t] -> (forall repr. T.Liftable repr => T.Args (SMTExpr' b) repr -> a) -> a
      fromLst [] f = f T.NoArg
      fromLst ((SExpr x):xs) f = fromLst xs (\xs' -> f (T.Arg x xs'))
      fromLst ((DExpr x _):xs) f = fromLst xs (\xs' -> f (T.Arg x xs'))-}
      
data SMTArgs b arg where
  SArg :: (Args b arg,ArgRepr arg ~ Left repr,T.Liftable repr)
          => T.Args (SMTExpr' b) repr -> SMTArgs b arg
  DArg :: (Args b arg,ArgRepr arg ~ Right ann,T.Liftable repr)
          => T.Args (SMTExpr' b) repr -> ann -> SMTArgs b arg

data SMTFun b arg t where
  SFunS :: (Args b arg,SMTType b t,ArgRepr arg ~ Left arg',SMTRepr t ~ Left t',
            T.Liftable arg',T.GetType t')
        => Function (Fun b) (Constr b) (Field b) arg' t'
        -> SMTFun b arg t
  SFunD :: (Args b arg,SMTType b t,ArgRepr arg ~ Left arg',SMTRepr t ~ Right tAnn,
            T.Liftable arg',T.GetType t')
        => Function (Fun b) (Constr b) (Field b) arg' t'
        -> tAnn
        -> SMTFun b arg t
  DFunS :: (Args b arg,SMTType b t,ArgRepr arg ~ Right argAnn,SMTRepr t ~ Left t',
            T.GetType t')
        => (forall tps. (T.Liftable tps)
            => argAnn -> Proxy tps
            -> Function (Fun b) (Constr b) (Field b) tps t')
        -> SMTFun b arg t
  DFunD :: (Args b arg,SMTType b t,ArgRepr arg ~ Right argAnn,SMTRepr t ~ Right tAnn)
           => (forall tps a. (T.Liftable tps)
               => argAnn -> Proxy tps
               -> (forall res. (T.GetType res)
                    => Function (Fun b) (Constr b) (Field b) tps res -> a)
               -> a)
           -> (argAnn -> tAnn)
           -> SMTFun b arg t

app :: Args b arg => SMTFun b arg t -> arg -> SMTExpr b t
app fun args = app' fun (mkArgs args)

app' :: SMTFun b arg t -> SMTArgs b arg -> SMTExpr b t
app' (SFunS fun) (SArg args)
  = SExpr (SMTExpr' (App fun args))
app' (SFunD fun ann) (SArg args) = DExpr (SMTExpr' (App fun args)) ann
app' (DFunS fun) (DArg (args::T.Args (SMTExpr' b) arg) ann)
  = SExpr (SMTExpr' (App (fun ann (Proxy::Proxy arg)) args))
app' (DFunD fun deriv) (DArg (args::T.Args (SMTExpr' b) arg) ann)
  = fun ann (Proxy::Proxy arg) $
    \rfun -> DExpr (SMTExpr' (App rfun args)) (deriv ann)

(.&&.) :: Backend b => SMTFun b (SMTExpr b Bool,SMTExpr b Bool) Bool
(.&&.) = SFunS (Logic And)

and' :: Backend b => SMTFun b [SMTExpr b Bool] Bool
and' = DFunS (\len _ -> allEqOfList (Proxy::Proxy T.BoolType) len $
                        \(_::Proxy (T.BoolType ': tps))
                         -> case cast (Logic And :: Function (Fun b) (Constr b) (Field b) (T.BoolType ': tps) T.BoolType) of
                           Just res -> res)

allEqOfList :: T.GetType t => Proxy t
            -> Integer
            -> (forall arg. (AllEq (t ': arg),SameType (t ': arg) ~ t)
                => Proxy (t ': arg) -> a)
            -> a
allEqOfList (_::Proxy t) 1 f = f (Proxy::Proxy ('[t]::[T.Type]))
allEqOfList pr@(_::Proxy t) n f
  = allEqOfList pr (n-1) $
    \(_::Proxy (t ': ts)) -> f (Proxy::Proxy (t ': t ': ts))
