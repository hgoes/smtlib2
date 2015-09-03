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

class (Typeable t,T.GetType (SMTRepr t)) => SMTType t where
  type SMTRepr t :: T.Type

class SMTType t => SMTValue t where
  toValue :: t -> T.Value con (SMTRepr t)
  fromValue :: T.Value con (SMTRepr t) -> t

class (Typeable args,T.Liftable (ArgRepr args '[])) => Args args where
  type ArgBackend args
  type ArgRepr args (oargs :: [T.Type]) :: [T.Type]
  toArgs :: args -> T.Args (SMTExpr' (ArgBackend args)) oargs -> T.Args (SMTExpr' (ArgBackend args)) (ArgRepr args oargs)
  fromArgs :: Proxy oargs -> T.Args (SMTExpr' (ArgBackend args)) (ArgRepr args oargs) -> (args,T.Args (SMTExpr' (ArgBackend args)) oargs)

class SMTDynType t where
  type SMTAnnotation t
  getSMTRepr :: Proxy t -> SMTAnnotation t
             -> (forall (q :: T.Type). T.GetType q => Proxy q -> a) -> a

class DynArgs args where
  type DynArgBackend args
  type ArgAnnotation args
  getArgRepr :: Proxy args -> ArgAnnotation args
             -> (forall (q :: [T.Type]). T.Liftable q => Proxy q -> a) -> a
  asArgs :: T.GetTypes oarg => args -> T.Args (SMTExpr' (DynArgBackend args)) oarg
         -> (forall arg. T.GetTypes arg => T.Args (SMTExpr' (DynArgBackend args)) arg -> a) -> a 


instance SMTType Bool where
  type SMTRepr Bool = T.BoolType

instance SMTValue Bool where
  toValue b = T.BoolValue b
  fromValue (T.BoolValue b) = b

instance SMTType Integer where
  type SMTRepr Integer = T.IntType

instance SMTValue Integer where
  toValue i = T.IntValue i
  fromValue (T.IntValue i) = i

instance (Typeable idx,Args idx,SMTType el,T.Liftable (ArgRepr idx '[]))
         => SMTType (SMTArray idx el) where
  type SMTRepr (SMTArray idx el) = T.ArrayType (ArgRepr idx '[]) (SMTRepr el)

instance (Typeable idx,Args idx,SMTDynType el,T.Liftable (ArgRepr idx '[]))
         => SMTDynType (SMTArray idx el) where
  type SMTAnnotation (SMTArray idx el) = SMTAnnotation el
  getSMTRepr (_::Proxy (SMTArray idx el)) ann f
    = getSMTRepr (Proxy::Proxy el) ann $
      \(_::Proxy eltp) -> f (Proxy::Proxy (T.ArrayType (ArgRepr idx '[]) eltp))

instance (Typeable b,SMTType t) => Args (SMTExpr b t) where
  type ArgBackend (SMTExpr b t) = b
  type ArgRepr (SMTExpr b t) as = (SMTRepr t) ': as
  toArgs (SMTExpr e) args = T.Arg e args
  fromArgs _ (T.Arg x xs) = (SMTExpr x,xs)

instance (Args a,Args b,ArgBackend a ~ ArgBackend b,
          T.Liftable (ArgRepr a (ArgRepr b '[])))
         => Args (a,b) where
  type ArgBackend (a,b) = ArgBackend a
  type ArgRepr (a,b) oarg = ArgRepr a (ArgRepr b oarg)
  toArgs (x,y) args = toArgs x (toArgs y args)
  fromArgs _ r0 = let (x,r1) = fromArgs Proxy r0
                      (y,r2) = fromArgs Proxy r1
                  in ((x,y),r2)

newtype SMTExpr' b t = SMTExpr' (Expression (Var b) (QVar b) (Fun b) (B.Constr b) (B.Field b) (FunArg b) (SMTExpr' b) t)

data SMTExpr b t where
  SMTExpr :: SMTType t => SMTExpr' b (SMTRepr t) -> SMTExpr b t
  SMTDynExpr :: (T.GetType a,SMTDynType t) => SMTExpr' b a -> SMTExpr b t

class SMTType' t where
  type SMTRepr' t :: Maybe T.Type
  type SMTAnnotation' t :: Maybe *
  getRepr' :: (SMTRepr' t ~ Nothing,SMTAnnotation' t ~ Just ann) => Proxy t -> ann -> (forall t'. T.GetType t' => Proxy t' -> a) -> a
  getRepr' = undefined

class Args' t where
  type ArgRepr' t :: Maybe [T.Type]
  type ArgAnnotation' t :: Maybe *
  getArgRepr' :: (ArgRepr' t ~ Nothing,ArgAnnotation' t ~ Just ann) => Proxy t -> ann -> (forall t'. T.GetTypes t' => Proxy t' -> a) -> a

instance SMTType' Bool where
  type SMTRepr' Bool = Just T.BoolType
  type SMTAnnotation' Bool = Nothing

--class (Args' args,SMTType' el) => LiftArray args el where
--  type LiftArray 

type family LiftArray (args :: Maybe [T.Type]) (tp :: Maybe T.Type) :: Maybe T.Type where
  LiftArray Nothing Nothing = Nothing
  LiftArray Nothing (Just a) = Nothing
  LiftArray (Just a) Nothing = Nothing
  LiftArray (Just arg) (Just tp) = Just (T.ArrayType arg tp)

type family LiftArrayAnn (args :: Maybe *) (tp :: Maybe *) :: Maybe * where
  LiftArrayAnn Nothing Nothing = Nothing
  LiftArrayAnn (Just arg) Nothing = Just arg
  LiftArrayAnn Nothing (Just tp) = Just tp
  LiftArrayAnn (Just arg) (Just tp) = Just (arg,tp)

instance (Args' arg,SMTType' el) => SMTType' (SMTArray arg el) where
  type SMTRepr' (SMTArray arg el) = LiftArray (ArgRepr' arg) (SMTRepr' el)
  type SMTAnnotation' (SMTArray arg el) = LiftArrayAnn (ArgAnnotation' arg) (SMTAnnotation' el)
  --getRepr' 

--instance (Args' arg,SMTType' el,ArgRepr' arg ~ Just arg',SMTRepr' el ~ Just el') => SMTType' (SMTArray arg el) where
--  type SMTRepr' (SMTArray arg el) = Just (arg',el')
--  type SMTAnnotation' (SMTArray arg el) = Nothing

app :: (Args arg,ArgRepr arg '[] ~ arg',SMTType res,SMTRepr res ~ res',ArgBackend arg ~ b)
    => Function (Fun b) (Constr b) (Field b) arg' res'
    -> arg -> SMTExpr b res
app f arg = SMTExpr (SMTExpr' (App f (toArgs arg T.NoArg)))

appDyn :: (Args arg,ArgRepr arg '[] ~ arg',SMTDynType res,T.GetType res',ArgBackend arg ~ b)
       => Function (Fun b) (Constr b) (Field b) arg' res'
       -> arg -> SMTExpr b res
appDyn f arg = SMTDynExpr (SMTExpr' (App f (toArgs arg T.NoArg)))

liftSMT :: Backend b => SMTMonad b a -> SMT' b a
liftSMT act = SMT' (lift act)

push :: Backend b => SMT' b ()
push = do
  b <- get
  nb <- liftSMT (B.push b)
  put nb

pop :: Backend b => SMT' b ()
pop = do
  b <- get
  nb <- liftSMT (B.pop b)
  put nb

var :: (Backend b,SMTType t) => SMT' b (SMTExpr b t)
var = do
  b <- get
  (v,nb) <- liftSMT (declareVar b Nothing)
  put nb
  return (SMTExpr (SMTExpr' (Var v)))

varAnn :: (Backend b,SMTDynType t) => SMTAnnotation t -> SMT' b (SMTExpr b t)
varAnn ann
  = with $ \pr -> getSMTRepr pr ann $
                  \(_::Proxy u) -> do
                    (b :: b) <- get
                    (v,nb) <- liftSMT (declareVar b Nothing)
                    put nb
                    return (SMTDynExpr (SMTExpr' (Var (v :: Var b u))))
  where
    with :: (Proxy t -> SMT' b (SMTExpr b t)) -> SMT' b (SMTExpr b t)
    with f = f Proxy

argVars :: (Backend b,Args arg,ArgBackend arg ~ b) => SMT' b arg
argVars = with $ \(_::Proxy arg) -> do
  args <- constr (T.getTypes (Proxy::Proxy (ArgRepr arg '[])))
  let (res,T.NoArg) = fromArgs (Proxy::Proxy ('[]::[T.Type])) args
  return res
  where
    with :: (Proxy arg -> SMT' b arg) -> SMT' b arg
    with f = f Proxy

    constr :: Backend b => T.Args T.Repr arg -> SMT' b (T.Args (SMTExpr' b) arg)
    constr T.NoArg = return T.NoArg
    constr (T.Arg (_::T.Repr t) xs) = do
      b <- get
      (v,nb) <- liftSMT (declareVar b Nothing)
      put nb
      rest <- constr xs
      return (T.Arg (SMTExpr' (Var v)) rest)

assert :: Backend b => SMTExpr b Bool -> SMT' b ()
assert expr = do
  expr' <- fromSMTExpr expr
  b <- get
  nb <- liftSMT (B.assert b expr')
  put nb

getProof :: Backend b => SMT' b (SMTExpr b Bool)
getProof = do
  b <- get
  (pr,nb) <- liftSMT (B.getProof b)
  put nb
  toSMTExpr pr

simplify :: (Backend b,SMTType t) => SMTExpr b t -> SMT' b (SMTExpr b t)
simplify e = do
  e' <- fromSMTExpr e
  b <- get
  (res,nb) <- liftSMT (B.simplify b e')
  put nb
  toSMTExpr res

(.==.) :: (Backend b,SMTType t) => SMTExpr b t -> SMTExpr b t -> SMTExpr b Bool
(.==.) (SMTExpr e1) (SMTExpr e2) = SMTExpr (SMTExpr' (App Eq (T.Arg e1 (T.Arg e2 T.NoArg))))

eq :: (Backend b,SMTType t) => [SMTExpr b t] -> SMTExpr b Bool
eq [] = error $ "smtlib2: eq called with empty list."
eq xs = allEqFromList [ x | SMTExpr x <- xs ]
        (\args -> SMTExpr (SMTExpr' (App Eq args)))

asEqOf :: (Backend b,SMTType u) => SMTExpr b Bool -> Maybe [SMTExpr b u]
asEqOf (SMTExpr (SMTExpr' e)) = case e of
  App Eq args -> do
    lst <- gcast (allEqToList args)
    return $ fmap SMTExpr lst
  _ -> Nothing

asEq :: Backend b => (forall u. SMTType u => [SMTExpr b u] -> a) -> SMTExpr b Bool -> Maybe a
asEq f (SMTExpr (SMTExpr' e)) = case e of
  App Eq args -> Just $ smtExprList (allEqToList args) f
  _ -> Nothing

ite :: SMTExpr b Bool -> SMTExpr b t -> SMTExpr b t -> SMTExpr b t
ite (SMTExpr c) (SMTExpr t) (SMTExpr f)
  = SMTExpr (SMTExpr' (App ITE (T.Arg c (T.Arg t (T.Arg f T.NoArg)))))
ite (SMTExpr c) (SMTDynExpr t) (SMTDynExpr f)
  = case gcast f of
    Just f' -> SMTDynExpr (SMTExpr' (App ITE (T.Arg c (T.Arg t (T.Arg f' T.NoArg)))))
    Nothing -> error $ "smtlib2: Type error in ite expression."

asITE :: SMTExpr b t -> Maybe (SMTExpr b Bool,SMTExpr b t,SMTExpr b t)
asITE (SMTExpr (SMTExpr' e)) = case e of
  App ITE (T.Arg c (T.Arg t (T.Arg f T.NoArg))) -> Just (SMTExpr c,SMTExpr t,SMTExpr f)
  _ -> Nothing
asITE (SMTDynExpr (SMTExpr' e)) = case e of
  App ITE (T.Arg c (T.Arg t (T.Arg f T.NoArg))) -> Just (SMTExpr c,SMTDynExpr t,SMTDynExpr f)
  _ -> Nothing

constant :: (Backend b,SMTValue t) => t -> SMTExpr b t
constant v = SMTExpr (SMTExpr' (Const (toValue v)))

asConstant :: SMTValue t => SMTExpr b t -> Maybe t
asConstant (SMTExpr (SMTExpr' e)) = case e of
  Const val -> Just $ fromValue val
  _ -> Nothing

forall :: (Args arg,b ~ ArgBackend arg,Backend b)
       => (arg -> SMTExpr b Bool)
       -> SMT' b (SMTExpr b Bool)
forall = quant False

exists :: (Args arg,b ~ ArgBackend arg,Backend b)
       => (arg -> SMTExpr b Bool)
       -> SMT' b (SMTExpr b Bool)
exists = quant True

asForallOf :: (Args args, b ~ ArgBackend args)
           => SMTExpr b Bool -> Maybe (args,SMTExpr b Bool)
asForallOf (SMTExpr (SMTExpr' e)) = case e of
  Forall arg body -> do
    arg' <- gcast arg
    let arg'' = runIdentity $ T.mapArgs (return . SMTExpr' . QVar) arg'
    return (fst $ fromArgs (Proxy::Proxy ('[]::[T.Type])) arg'',SMTExpr body)
  _ -> Nothing

asExistsOf :: (Args args, b ~ ArgBackend args)
           => SMTExpr b Bool -> Maybe (args,SMTExpr b Bool)
asExistsOf (SMTExpr (SMTExpr' e)) = case e of
  Exists arg body -> do
    arg' <- gcast arg
    let arg'' = runIdentity $ T.mapArgs (return . SMTExpr' . QVar) arg'
    return (fst $ fromArgs (Proxy::Proxy ('[]::[T.Type])) arg'',SMTExpr body)
  _ -> Nothing

select :: (Args idx,SMTType el,b ~ ArgBackend idx) => SMTExpr b (SMTArray idx el) -> idx -> SMTExpr b el
select (SMTExpr arr) idx
  = SMTExpr (SMTExpr' (App Select (T.Arg arr (toArgs idx T.NoArg))))

constArray :: (Args idx,b ~ ArgBackend idx)
           => SMTExpr b el -> SMTExpr b (SMTArray idx el)
constArray (SMTExpr el) = SMTExpr (SMTExpr' (App ConstArray (T.Arg el T.NoArg)))
constArray (SMTDynExpr (el :: SMTExpr' b el))
  = with (\(_::Proxy idx)
          -> SMTDynExpr (SMTExpr' (App ConstArray (T.Arg el T.NoArg))
                          :: SMTExpr' b (T.ArrayType (ArgRepr idx '[]) el)))
  where
    with :: (Proxy idx -> SMTExpr b (SMTArray idx el')) -> SMTExpr b (SMTArray idx el')
    with f = f Proxy

quant :: (Args arg,b ~ ArgBackend arg,Backend b)
       => Bool -> (arg -> SMTExpr b Bool)
       -> SMT' b (SMTExpr b Bool)
quant ex (f :: arg -> SMTExpr b Bool) = do
  args <- constr (T.getTypes (Proxy::Proxy (ArgRepr arg ('[]::[T.Type]))))
  args' <- T.mapArgs (return . SMTExpr' . QVar) args
  let (args'',T.NoArg) = fromArgs (Proxy::Proxy ('[]::[T.Type])) args'
      SMTExpr body = f args''
      app = if ex then Exists else Forall
  return (SMTExpr (SMTExpr' (app args body)))
  where
    constr :: Backend b => T.Args T.Repr args -> SMT' b (T.Args (QVar b) args)
    constr T.NoArg = return T.NoArg
    constr (T.Arg _ xs) = do
      b <- get
      (qv,nb) <- liftSMT (B.createQVar b Nothing)
      put b
      xs' <- constr xs
      return (T.Arg qv xs')

smtExprList :: (Backend b,T.GetType a) => [SMTExpr' b a]
            -> (forall c. SMTType c => [SMTExpr b c] -> r) -> r
smtExprList (lst::[SMTExpr' b a]) f
  = smtRepr (Proxy::Proxy b) (Proxy::Proxy a) $
    \(_::Proxy t) -> f [ SMTExpr e :: SMTExpr b t | e <- lst ]

smtRepr :: (Backend b,T.GetType t) => Proxy b -> e t
        -> (forall t'. (SMTType t',SMTRepr t' ~ t) => Proxy t' -> a)
        -> a
smtRepr prB pr f = case T.getType pr of
  T.BoolRepr -> f (Proxy::Proxy Bool) 
  T.IntRepr -> f (Proxy::Proxy Integer)
  T.ArrayRepr (_::T.Args T.Repr idx) (_::T.Repr el)
    -> argRepr prB (Proxy::Proxy idx) $
       \(_::Proxy idx') -> smtRepr prB (Proxy::Proxy el) $
       \(_::Proxy el') -> f (Proxy::Proxy (SMTArray idx' el'))

argRepr :: (Backend b,T.GetTypes arg) => Proxy b -> e arg
        -> (forall arg'. (Args arg',ArgRepr arg' '[] ~ arg,ArgBackend arg' ~ b)
            => Proxy arg' -> a)
        -> a
argRepr prB@(_::Proxy b) pr f = case T.getTypes pr of
  T.Arg (_::T.Repr x1)  T.NoArg
    -> smtRepr prB (Proxy::Proxy x1) $
       \(_::Proxy y1) -> f (Proxy::Proxy (SMTExpr b y1))
  T.Arg (_::T.Repr x1) (T.Arg (_::T.Repr x2) T.NoArg)
    -> smtRepr prB (Proxy::Proxy x1) $
       \(_::Proxy y1) -> smtRepr prB (Proxy::Proxy x2) $
       \(_::Proxy y2) -> f (Proxy::Proxy (SMTExpr b y1,SMTExpr b y2))

fromSMTExpr :: (Backend b,SMTType t) => SMTExpr b t -> SMT' b (Expr b (SMTRepr t))
fromSMTExpr (SMTExpr e) = fromSMTExpr' e
  where
    fromSMTExpr' :: Backend b => SMTExpr' b t -> SMT' b (Expr b t)
    fromSMTExpr' (SMTExpr' e) = do
      ne <- mapExpr return return return return return return fromSMTExpr' e
      b <- get
      (res,nb) <- liftSMT (toBackend b ne)
      put nb
      return res

toSMTExpr :: (Backend b,SMTType t) => Expr b (SMTRepr t) -> SMT' b (SMTExpr b t)
toSMTExpr expr = fmap SMTExpr (toSMTExpr' expr)
  where
    toSMTExpr' :: Backend b => Expr b t -> SMT' b (SMTExpr' b t)
    toSMTExpr' e = do
      b <- get
      (ne,nb) <- liftSMT (fromBackend b e)
      put nb
      ne' <- mapExpr return return return return return return toSMTExpr' ne
      return (SMTExpr' ne')
