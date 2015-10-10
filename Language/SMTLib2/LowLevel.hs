{-# LANGUAGE ViewPatterns,ConstraintKinds,QuasiQuotes #-}
module Language.SMTLib2.LowLevel (
  -- * SMT Monad
  Backend(Expr,Var,QVar,Fun,Constr,Field,FunArg,ClauseId),
  SMT(..),SMTState(..),withBackend,withBackendExitCleanly,updateBackend,updateBackend',toBackend,
  SMTOption(..),setOption,
  SMTInfo(..),getInfo,
  comment,
  registerDatatype,
  -- * Queries
  CheckSatResult(..),
  assert,checkSat,push,pop,stack,
  -- * Models
  getValue,
  getRawValue,
  -- * Unsatisfiable Core
  assertId,getUnsatCore,
  -- * Interpolation
  Partition(..),assertPartition,interpolate,
  -- * Types
  Type(..),Nat(..),GetType(..),GetTypes(..),AllEq(SameType),Fst,Snd,
  -- * Expressions
  FromSMT(..),ToSMT(..),DatatypeInfo,emptyDatatypeInfo,Embed(..),Expression(..),Function(..),mapSubExpressions,
  Args(..),
  -- ** Operators
  LogicOp(..),OrdOp(..),ArithOp(..),ArithOpInt(..),BVCompOp(..),BVBinOp(..),BVUnOp(..),
  -- ** Variables
  var,varNamed,
  -- ** Constants
  Value(..),
  constant,
  -- ** Comparison
  SMTOrd(..),
  -- ** Basic logic
  -- ** Arithmetic
  SMTArith(..),
  -- ** Functions
  fun,
  defFun,
  app,app',appLst,
  -- ** Arrays
  -- ** Bitvectors
  SMTBV(..)
  -- ** Accessors
  --asVar,asConstant,asEq
  ) where

import Language.SMTLib2.Internals.Expression
import Language.SMTLib2.Internals.Backend hiding (setOption,getInfo,comment,assert,
                                                  checkSat,getValue,push,pop,assertId,
                                                  getUnsatCore,interpolate,assertPartition,toBackend,
                                                  Constr,Field)
import qualified Language.SMTLib2.Internals.Backend as B
import Language.SMTLib2.Internals.Type hiding (Field)
import Language.SMTLib2.Internals.Type.Nat
import Language.SMTLib2.Internals.Embed
import Language.SMTLib2.Internals.Monad

import Data.Typeable
import Data.Type.Equality
import Control.Monad.State.Strict
import Control.Monad.Identity
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IMap
import Data.GADT.Compare
import Data.GADT.Show
import Control.Exception (bracket)
import Data.Constraint

withBackend :: Backend b => b -> SMT b a -> SMTMonad b a
withBackend b (SMT act) = do
  (res,nb) <- runStateT act (SMTState b Map.empty)
  exit (backend nb)
  return res

withBackendExitCleanly :: (Backend b,SMTMonad b ~ IO) => b -> SMT b a -> IO a
withBackendExitCleanly b (SMT act)
  = bracket
    (return b)
    (\b -> exit b)
    (\b -> do
        (res,nb) <- runStateT act (SMTState b Map.empty)
        return res)

app :: (Embed e,GetType tp,GetTypes arg)
    => Function (Fun (EmbedBackend e)) (B.Constr (EmbedBackend e)) (B.Field (EmbedBackend e)) '(arg,tp)
    -> Args e arg
    -> e tp
app f arg = embed (App f arg)

appLst :: (Embed e,GetType tp,GetType t,
           fun ~ Fun (EmbedBackend e),
           con ~ B.Constr (EmbedBackend e),field ~ B.Field (EmbedBackend e))
       => (forall arg. (AllEq arg,SameType arg ~ t) => Function fun con field '(arg,tp))
       -> [e t]
       -> e tp
appLst fun args = embed $ allEqFromList args $ App fun

map' :: (GetTypes arg,GetTypes idx,GetType res)
     => Function fun con field '(arg,res)
     -> Function fun con field '(Lifted arg idx,ArrayType idx res)
map' = Map

class GetType t => SMTOrd (t :: Type) where
  lt :: Function fun con field '( '[t,t],BoolType)
  le :: Function fun con field '( '[t,t],BoolType)
  gt :: Function fun con field '( '[t,t],BoolType)
  ge :: Function fun con field '( '[t,t],BoolType)

instance SMTOrd IntType where
  lt = OrdInt Lt
  le = OrdInt Le
  gt = OrdInt Gt
  ge = OrdInt Ge

instance SMTOrd RealType where
  lt = OrdReal Lt
  le = OrdReal Le
  gt = OrdReal Gt
  ge = OrdReal Ge

mapSubExpressions :: (Monad m,GetType tp)
                  => (forall t. GetType t => e t -> m (e' t))
                  -> Expression v qv fun con field fv e tp
                  -> m (Expression v qv fun con field fv e' tp)
mapSubExpressions f (Var v) = return $ Var v
mapSubExpressions f (QVar v) = return $ QVar v
mapSubExpressions f (FVar v) = return $ FVar v
mapSubExpressions f (App fun arg) = do
  arg' <- mapArgs f arg
  return (App fun arg')
mapSubExpressions f (Const c) = return $ Const c
mapSubExpressions f (AsArray fun) = return $ AsArray fun
mapSubExpressions f (Quantification q args body) = do
  body' <- f body
  return (Quantification q args body')
mapSubExpressions f (Let bnds body) = do
  bnds' <- mapArgs (\bnd -> do
                       ne <- f (letExpr bnd)
                       return (bnd { letExpr = ne })
                   ) bnds
  body' <- f body
  return (Let bnds' body')

updateBackend :: Backend b => (b -> SMTMonad b (a,b)) -> SMT b a
updateBackend act = do
  st <- get
  (res,nb) <- liftSMT $ act (backend st)
  put $ st { backend = nb }
  return res

updateBackend' :: Backend b => (b -> SMTMonad b b) -> SMT b ()
updateBackend' act = do
  st <- get
  nb <- liftSMT $ act (backend st)
  put $ st { backend = nb }

-- SMT functions
checkSat :: Backend b => SMT b B.CheckSatResult
checkSat = updateBackend (\b -> B.checkSat b Nothing (B.CheckSatLimits Nothing Nothing))

getUnsatCore :: Backend b => SMT b [ClauseId b]
getUnsatCore = updateBackend B.getUnsatCore

push :: Backend b => SMT b ()
push = updateBackend' B.push

pop :: Backend b => SMT b ()
pop = updateBackend' B.pop

stack :: Backend b => SMT b a -> SMT b a
stack act = do
  push
  res <- act
  pop
  return res

comment :: Backend b => String -> SMT b ()
comment str = updateBackend' $ \b -> B.comment b str

setOption :: Backend b => SMTOption -> SMT b ()
setOption opt = updateBackend' $ \b -> B.setOption b opt

getInfo :: Backend b => SMTInfo i -> SMT b i
getInfo inf = updateBackend $ \b -> B.getInfo b inf

toBackendExpr :: (Embed e,GetType tp)
              => e tp
              -> SMT (EmbedBackend e) (Expr (EmbedBackend e) tp)
toBackendExpr (e :: e tp) = case extract e of
  Left e' -> do
    e'' <- mapSubExpressions toBackendExpr e'
    updateBackend $ \b -> B.toBackend b e''
  Right sub -> encodeSub (Proxy::Proxy e) sub

fromBackendExpr :: (Embed e,GetType tp)
                => Expr (EmbedBackend e) tp -> SMT (EmbedBackend e) (e tp)
fromBackendExpr e = do
  sub <- extractSub e
  case sub of
    Just sub' -> return sub'
    Nothing -> do
      e' <- updateBackend $ \b -> B.fromBackend b e
      e'' <- mapSubExpressions fromBackendExpr e'
      return $ embed e''

toBackend :: (Backend b,GetType tp)
          => Expression (B.Var b) (B.QVar b) (B.Fun b) (B.Constr b) (B.Field b) (B.FunArg b) (B.Expr b) tp
          -> SMT b (B.Expr b tp)
toBackend e = updateBackend $ \b -> B.toBackend b e

assert :: (Embed e) => e BoolType -> SMT (EmbedBackend e) ()
assert e = do
  e' <- toBackendExpr e
  updateBackend' $ \b -> B.assert b e'

assertId :: (Embed e) => e BoolType -> SMT (EmbedBackend e) (ClauseId (EmbedBackend e))
assertId e = do
  e' <- toBackendExpr e
  updateBackend $ \b -> B.assertId b e'

assertPartition :: (Embed e) => e BoolType -> Partition -> SMT (EmbedBackend e) ()
assertPartition e part = do
  e' <- toBackendExpr e
  updateBackend' $ \b -> B.assertPartition b e' part

interpolate :: (Embed e) => SMT (EmbedBackend e) (e BoolType)
interpolate = do
  interp <- updateBackend B.interpolate
  fromBackendExpr interp

var :: (Embed e,GetType t) => SMT (EmbedBackend e) (e t)
var = do
  v <- updateBackend $ \b -> B.declareVar b Nothing
  return $ embed (Var v)

varNamed :: (Embed e,GetType t) => String -> SMT (EmbedBackend e) (e t)
varNamed name = do
  v <- updateBackend $ \b -> B.declareVar b (Just name)
  return $ embed (Var v)

constant :: (Embed e,GetType t) => Value (B.Constr (EmbedBackend e)) t -> e t
constant v = embed (Const v)

getValue :: (Embed e,FromSMT repr) => e repr -> SMT (EmbedBackend e) (ValueType repr)
getValue e = do
  val <- getRawValue e
  dtinfo <- gets datatypes
  return $ fromValue dtinfo val

getRawValue :: (Embed e,GetType tp) => e tp -> SMT (EmbedBackend e) (Value (B.Constr (EmbedBackend e)) tp)
getRawValue e = do
  e' <- toBackendExpr e
  updateBackend $ \b -> B.getValue b e'

fun :: (Backend b,GetTypes arg,GetType res) => SMT b (Function (Fun b) con field '(arg,res))
fun = do
  fun <- updateBackend $ \b -> declareFun b Nothing
  return (Fun fun)

defFun :: (Embed e,GetTypes arg,GetType res)
       => (Args e arg -> e res)
       -> SMT (EmbedBackend e) (Function (Fun (EmbedBackend e)) con field '(arg,res))
defFun (f :: Args e arg -> e res) = do
  args <- mapArgs (\_ -> updateBackend $ \b -> B.createFunArg b Nothing
                  ) (getTypes::Args Repr arg)
  fargs <- mapArgs (return . embed . FVar) args
  body <- toBackendExpr (f fargs)
  fun <- updateBackend $ \b -> B.defineFun b Nothing args body
  return (Fun fun)

class GetType t => SMTArith t where
  plus :: (AllEq arg, SameType arg ~ t)
       => Function fun con field '(arg,t)
  minus :: (AllEq arg,SameType arg ~ t)
        => Function fun con field '(arg,t)
  mult :: (AllEq arg, SameType arg ~ t)
       => Function fun con field '(arg,t)
  abs' :: Function fun con field '( '[t],t)

instance SMTArith IntType where
  plus = ArithInt Plus
  minus = ArithInt Minus
  mult = ArithInt Mult
  abs' = AbsInt

instance SMTArith RealType where
  plus = ArithReal Plus
  minus = ArithReal Minus
  mult = ArithReal Mult
  abs' = AbsReal

class (AppExpr' fun ~ e,
       AppRet' sig fun ~ res,
       AppFun' sig e res ~ fun
       --AppSig' fun ~ sig
      )
      => MkApp (sig :: [Type]) (e::Type -> *) res fun where
  type AppFun' sig e res
  type AppExpr' fun :: Type -> *
  type AppRet' sig fun
  --type AppSig' fun :: [Type]
  toApp :: (Args e sig -> res) -> fun

instance GetType t => MkApp '[t] e res (e t -> res) where
  type AppFun' '[t] e res = e t -> res
  type AppExpr' (e t -> res) = e
  type AppRet' '[t] (e t -> res) = res
  --type AppSig' (e t -> res) = '[t]
  toApp f x = f (Arg x NoArg)

instance (GetType x1,GetTypes xs,GetType x2,MkApp (x2 ': xs) e res fun)
         => MkApp (x1 ': x2 ': xs) e res (e x1 -> fun) where
  type AppFun' (x1 ': x2 ': xs) e res = e x1 -> AppFun' (x2 ': xs) e res
  type AppExpr' (e x1 -> fun) = e
  type AppRet' (x1 ': x2 ': xs) (e x1 -> fun) = AppRet' (x2 ': xs) fun
  --type AppSig' (e x1 -> fun) = x1 ': AppSig' fun
  toApp f p = toApp (\arg -> f (Arg p arg))

newtype SMTAction b t = SMTAction (SMT b (Expr b t))

instance (GShow (SMTAction b),Backend b) => Embed (SMTAction b) where
  type EmbedBackend (SMTAction b) = b
  type EmbedSub (SMTAction b) = NoVar
  embed e = SMTAction $ do
    rexpr <- mapExpr return return return return return return (\(SMTAction act) -> act) e
    updateBackend $ \b -> B.toBackend b rexpr

app' :: (Embed e,GetTypes sig,MkApp sig e (e ret) rfun,GetType ret)
    => Function (Fun (EmbedBackend e)) (B.Constr (EmbedBackend e)) (B.Field (EmbedBackend e)) '(sig,ret)
    -> rfun
app' fun = toApp (embed . App fun)
