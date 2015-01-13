{-# LANGUAGE ViewPatterns,GADTs,DeriveDataTypeable #-}
module Language.SMTLib2.DatatypeEmulator (emulateDataTypes) where

import Language.SMTLib2
import Language.SMTLib2.Internals hiding (Constr)
import qualified Language.SMTLib2.Internals as SMT
import Language.SMTLib2.Internals.Operators
import Language.SMTLib2.Internals.Instances

import Data.Fix
import Data.Proxy
import Control.Monad.Identity
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (genericIndex,genericLength,find)
import Data.IORef
import Control.Monad.Trans (MonadIO,liftIO)
import Control.Monad.Identity
import Data.Traversable (mapAccumL)
import Data.Typeable
import Data.Maybe (catMaybes)
import Debug.Trace

emulateDataTypes :: b -> DataTypeEmulator b
emulateDataTypes b = DataTypeEmulator b emptyDataTypeInfo 0 Map.empty Map.empty

data DataTypeEmulator b = DataTypeEmulator { emulatedBackend :: b
                                           , emulatedDataTypes :: DataTypeInfo
                                           , nextFreeVar :: Integer
                                           , varMapping :: Map Integer AnyTransVar
                                           , revMapping :: Map Integer AnyRevVar }

data TransVar a where
  NormalVar :: Integer -> SMTAnnotation a -> TransVar a
  AnyVar :: SMTAnnotation a -> TransVar a
  SingletonVar :: [TransField a TransVar] -> TransVar a
  ConstrVar :: [(TransConstr a Integer,[TransField a TransVar])] -> TransVar a
  UntypedVar :: SMTType t => TransVar t -> TransVar Untyped
  UntypedValueVar :: SMTValue t => TransVar t -> TransVar UntypedValue
  deriving (Typeable)

data AnyTransVar = forall a. SMTType a => AnyTransVar (TransVar a)

data TransExpr a where
  NormalExpr :: SMTExpr a -> TransExpr a
  AnyExpr :: SMTAnnotation a -> TransExpr a
  SingletonExpr :: [TransField a TransExpr] -> TransExpr a
  ConstrExpr :: [(TransConstr a (SMTExpr Bool),[TransField a TransExpr])] -> TransExpr a
  UntypedExprTrans :: SMTType t => TransExpr t -> TransExpr Untyped
  UntypedExprValueTrans :: SMTValue t => TransExpr t -> TransExpr UntypedValue
  deriving (Typeable)

data TransType a = NormalType (SMTAnnotation a)
                 | SingletonType [TransField a TransType]
                 | ConstrType [(TransConstr a (),[TransField a TransType])]
                 deriving (Typeable)

data AnyTransType = forall a. SMTType a => AnyTransType (TransType a)

--data AnyTransExpr = forall a. SMTType a => AnyTransExpr (TransExpr a)

data TransField a r = forall f. SMTType f => TransField (Field a f) (r f)

data TransConstr a r = forall arg. Args arg => TransConstr (Constructor arg a) r

data AnyRevVar = forall a. SMTType a => AnyRevVar (RevVar a)

data RevVar a where
  RevNormal :: Integer -> SMTAnnotation a -> RevVar a
  RevField :: SMTType p => RevVar p -> Field p a -> RevVar a
  RevConstr :: (Args arg,SMTType p) => RevVar p -> Constructor arg p -> RevVar Bool
  RevUntyped :: RevVar Untyped -> RevVar a
  RevUntypedValue :: RevVar UntypedValue -> RevVar a
  deriving Typeable

data TransArgs a = NormalArgs a
                 | LinearizedArgs [TransExpr Untyped]

data Trans a = Normal a
             | Singleton [Trans a]
             | Constr [[Trans a]]
             deriving (Show)

transVarToExpr :: SMTType a => Bool -> TransVar a -> TransExpr a
transVarToExpr False (NormalVar i ann) = NormalExpr (Var i ann)
transVarToExpr True  (NormalVar i ann) = NormalExpr (FunArg i ann)
transVarToExpr _ (AnyVar ann) = AnyExpr ann
transVarToExpr farg (SingletonVar fields) = SingletonExpr (fmap transField fields)
  where
    transField (TransField f e) = TransField f (transVarToExpr farg e)
transVarToExpr farg (ConstrVar cons)
  = ConstrExpr (fmap transConstr cons)
  where
    transConstr (TransConstr con act,fields) = (TransConstr con (if farg
                                                                 then FunArg act ()
                                                                 else Var act ()),
                                                fmap transField fields)
    transField (TransField f e) = TransField f (transVarToExpr farg e)
transVarToExpr farg (UntypedVar v) = UntypedExprTrans (transVarToExpr farg v)
transVarToExpr farg (UntypedValueVar v) = UntypedExprValueTrans (transVarToExpr farg v)

translateExpr :: SMTType t => DataTypeEmulator b
                 -> Map Integer AnyTransVar
                 -> SMTExpr t -> TransExpr t
translateExpr em _ (Var idx ann) = case Map.lookup idx (varMapping em) of
  Just (AnyTransVar var) -> case cast var of
    Just var' -> transVarToExpr False var'
translateExpr em argMp (FunArg idx ann) = case Map.lookup idx argMp of
  Just (AnyTransVar var) -> case cast var of
    Just var' -> transVarToExpr True var'
translateExpr em mp c@(Const (x::t) ann) = case (mangle::Mangling t) of
  PrimitiveMangling f -> case getSort (getUndef c) ann of
    Fix (NamedSort name pars)
      -> case Map.lookup name (datatypes $ emulatedDataTypes em) of
      Just (dt,_) -> case dataTypeConstructors dt of
        [con] -> SingletonExpr [ fieldGet f parTps x
                                 (\e ann -> case (asValueType e ann $
                                                  \e' ann' -> TransField (Field parTps dt con f)
                                                              (translateExpr em mp
                                                               (Const e' ann'))
                                                 ) of
                                            Just r -> r)
                               | f <- conFields con
                               ]
        cons -> ConstrExpr [ (TransConstr (Constructor parTps dt con
                                           ::Constructor () t) (constant act),
                              [ fieldGet f parTps x $
                                \fv fann -> case (asValueType fv fann $
                                                  \fv' fann'
                                                  -> TransField (Field parTps dt con f)
                                                     (if act
                                                      then translateExpr em mp
                                                           (Const fv' fann')
                                                      else AnyExpr fann')
                                                 ) of
                                             Just r -> r
                              | f <- conFields con ])
                           | con <- cons
                           , let act = conTest con parTps x ]
      where
        parTps = fmap (\s -> withSort (emulatedDataTypes em) s ProxyArg) pars
    _ -> NormalExpr c
  ComplexMangling f -> translateExpr em mp (f x ann)
translateExpr em mp (UntypedExpr (e::SMTExpr t))
  = UntypedExprTrans (translateExpr em mp e)
translateExpr em mp (UntypedExprValue (e::SMTExpr t))
  = UntypedExprValueTrans (translateExpr em mp e)
translateExpr em mp (App SMTEq xs)
  = NormalExpr $ translateEq $ fmap (translateExpr em mp) xs
  where
    translateEq :: SMTType a => [TransExpr a] -> SMTExpr Bool
    translateEq xs = case head xs of
      NormalExpr x -> App SMTEq [ y | NormalExpr y <- xs ]
      SingletonExpr fs -> app and' $
                          mkEq [ fs | SingletonExpr fs <- xs ]
      ConstrExpr cons -> app and' $
                         mkEqs [ cons | ConstrExpr cons <- xs ]
      UntypedExprTrans e
        -> translateEq (e:[ case cast y of
                             Just e' -> e' | UntypedExprTrans y <- tail xs ])
      UntypedExprValueTrans e
        -> translateEq (e:[ case cast y of
                             Just e' -> e' | UntypedExprValueTrans y <- tail xs ])
    mkEq :: SMTType t => [[TransField t TransExpr]] -> [SMTExpr Bool]
    mkEq ([]:_) = []
    mkEq (((TransField _ x):xs):rest)
      = (translateEq (x:fmap (\((TransField _ y):_) -> case cast y of
                               Just r -> r
                             ) rest)):
        mkEq (xs:(fmap tail rest))

    mkEqs :: SMTType t => [[(TransConstr t (SMTExpr Bool),[TransField t TransExpr])]]
          -> [SMTExpr Bool]
    mkEqs ([]:_) = []
    mkEqs (((TransConstr _ act,fs):xs):rest)
      = (App SMTEq (act:[ act' | ((TransConstr _ act',_):_) <- rest ])):
        (mkEq (fs:[ fs' | ((_,fs'):_) <- rest ]))++
        (mkEqs (xs:fmap tail rest))
translateExpr em mp (App (SMTConstructor (Constructor tps dt constr::Constructor arg res)) args)
  = dataTypeGetUndefined dt tps $
    \u _ -> case dataTypeConstructors dt of
    [con] -> SingletonExpr [ fieldGet f tps u $
                             \(_::f) _ -> TransField (Field tps dt con f::Field res f)
                                          (translateExpr em mp (castUntypedExpr arg))
                           | (f,arg) <- zip (conFields con) (fromArgs args) ]
    cons -> ConstrExpr [ conUndefinedArgs con tps $
                         \(_::arg') _ -> (TransConstr (Constructor tps dt con
                                                       ::Constructor arg' res) (constant act),
                                         [ fieldGet f tps u $
                                           \(_::f) ann -> TransField (Field tps dt con f::Field res f)
                                                          (if act
                                                           then translateExpr em mp (castUntypedExpr arg)
                                                           else AnyExpr ann)
                                         | (f,arg) <- zip (conFields con) (fromArgs args) ])
                       | con <- cons
                       , let act = conName con==conName constr]
translateExpr em mp (App (SMTFieldSel (Field tps dt constr field)) e)
  = case translateExpr em mp e of
  SingletonExpr exprs -> findField exprs
  ConstrExpr exprs -> findConstr exprs
  AnyExpr ann -> withSort (emulatedDataTypes em) tp $
                 \u ann -> case cast ann of
                            Just ann' -> AnyExpr ann'
  where
    tp = runIdentity $ argumentSortToSort
         (\idx -> return $ genericIndex tps' idx) (fieldSort field)
    tps' = [ getSort u ann
           | ProxyArg u ann <- tps ]
    findField :: SMTType a => [TransField t TransExpr] -> TransExpr a
    findField ((TransField (Field _ _ _ f) e):es)
      | fieldName f==fieldName field = case cast e of
        Just r -> r
      | otherwise = findField es
    findConstr ((TransConstr (Constructor _ _ c) _,e):es)
      | conName c==conName constr = findField e
      | otherwise = findConstr es
translateExpr em mp (App (SMTConTest (Constructor tps dt constr)) e)
  = case translateExpr em mp e of
  SingletonExpr _ -> NormalExpr (constant True)
  ConstrExpr exprs -> NormalExpr (findConstr exprs)
  AnyExpr _ -> AnyExpr ()
  where
    findConstr ((TransConstr (Constructor _ _ con) act,_):es)
      | conName con == conName constr = act
      | otherwise = findConstr es
translateExpr em mp (App (SMTFun var resAnn) args) = case Map.lookup var (varMapping em) of
  Just (AnyTransVar var) -> case cast var of
    Just var' -> mkCall var'
  where
    rargs = linearizeArgs em args
    mkCall :: SMTType t => TransVar t -> TransExpr t
    mkCall (NormalVar i ann) = NormalExpr (App (SMTFun i ann) rargs)
    mkCall (SingletonVar tps) = SingletonExpr (fmap mkCallField tps)
    mkCall (ConstrVar cons)
      = ConstrExpr $ fmap mkCallConstr cons
    mkCallField :: SMTType t => TransField t TransVar -> TransField t TransExpr
    mkCallField (TransField f e) = TransField f (mkCall e)
    mkCallConstr :: SMTType t => (TransConstr t Integer,[TransField t TransVar])
                 -> (TransConstr t (SMTExpr Bool),[TransField t TransExpr])
    mkCallConstr (TransConstr con act,fields)
      = (TransConstr con (App (SMTFun act ()) rargs),
         fmap mkCallField fields)
translateExpr em mp (App SMTITE (cond,ifT,ifF))
  = case translateExpr em mp cond of
  NormalExpr cond' -> mkITE cond' (translateExpr em mp ifT)
                      (translateExpr em mp ifF)
  where
    mkITE :: SMTType a => SMTExpr Bool -> TransExpr a -> TransExpr a -> TransExpr a
    mkITE c (NormalExpr l) (NormalExpr r)
      = NormalExpr (App SMTITE (c,l,r))
    mkITE c (SingletonExpr ls) (SingletonExpr rs)
      = SingletonExpr (zipWith (iteField c) ls rs)
    mkITE c (ConstrExpr ls) (ConstrExpr rs)
      = ConstrExpr $
        zipWith (iteConstr c) ls rs
    iteField :: SMTType a => SMTExpr Bool -> TransField a TransExpr -> TransField a TransExpr -> TransField a TransExpr
    iteField c (TransField f ifT) (TransField _ ifF) = case cast ifF of
      Just ifF' -> TransField f (mkITE c ifT ifF')

    iteConstr :: SMTType a => SMTExpr Bool
              -> (TransConstr a (SMTExpr Bool),[TransField a TransExpr])
              -> (TransConstr a (SMTExpr Bool),[TransField a TransExpr])
              -> (TransConstr a (SMTExpr Bool),[TransField a TransExpr])
    iteConstr c (TransConstr con actL,fieldL) (TransConstr _ actR,fieldR)
      = (TransConstr con (ite c actL actR),
         zipWith (iteField c) fieldL fieldR)
translateExpr em mp (App fun args) = NormalExpr (App fun nargs)
  where
    targs = fmap (translateExpr em mp) (fromArgs args)
    argAnn = extractArgAnnotation args
    Just (nargs,[]) = toArgs argAnn (fmap toNormalExpr targs)
translateExpr em mp expr = error $ "smtlib2-emulated-datatypes: Cannot translate expression: "++show expr

reTranslateExpr :: SMTType a => Map Integer AnyRevVar -> SMTExpr a -> SMTExpr a
reTranslateExpr mp (Var idx ann::SMTExpr t) = case Map.lookup idx mp of
  Just (AnyRevVar rv) -> case cast rv of
    Just rv' -> revVar rv'
  Nothing -> error $ "smtlib2-emulated-datatypes: No reverse mapping found for variable "++show idx
  where
    revVar :: SMTType a => RevVar a -> SMTExpr a
    revVar (RevNormal i ann) = Var i ann
    revVar (RevField par field) = App (SMTFieldSel field) (revVar par)
reTranslateExpr mp (App fun args) = App fun nargs
  where
    ((),nargs) = foldExprsId (\_ e _ -> ((),reTranslateExpr mp e)
                             ) () args (extractArgAnnotation args)
reTranslateExpr mp e = e

toNormalExpr :: SMTType a => TransExpr a -> SMTExpr a
toNormalExpr (NormalExpr x) = x
toNormalExpr (AnyExpr ann) = defaultExpr ann
toNormalExpr (UntypedExprTrans e) = UntypedExpr (toNormalExpr e)
toNormalExpr (UntypedExprValueTrans e) = UntypedExprValue (toNormalExpr e)
--toNormalExpr _ expr = error $ "toNormalExpr not defined for "++show expr

instance (Monad m,SMTBackend b m) => SMTBackend (DataTypeEmulator b) m where
  smtGetNames em = return (\idx -> escapeName (Right idx))
  smtNextName em = return (\_ -> escapeName (Right $ nextFreeVar em))
  smtHandle em SMTDeclaredDataTypes = return (emulatedDataTypes em,em)
  smtHandle em (SMTDeclareDataTypes tpc) = do
    let ndts = addDataTypeStructure tpc (emulatedDataTypes em)
    return ((),em { emulatedDataTypes = ndts })
  smtHandle em (SMTDeclareFun (FunInfo { funInfoProxy = (_::Proxy (arg,res))
                                       , funInfoArgAnn = argAnn
                                       , funInfoResAnn = resAnn })) = do
    (vars,nrev,nb) <- mkFuns (emulatedBackend em) (revMapping em)
                      (RevNormal (nextFreeVar em) resAnn) retTp
    return (nextFreeVar em,em { emulatedBackend = nb
                              , nextFreeVar = (nextFreeVar em)+1
                              , varMapping = Map.insert (nextFreeVar em) (AnyTransVar vars)
                                             (varMapping em)
                              , revMapping = nrev
                              })
    where
      argTps = [ prx
               | ProxyArg u ann <- getTypes (undefined::arg) argAnn
               , prx <- linearizeType (translateType' u ann) ]
      retTp = translateType' (undefined::res) resAnn
      mkFuns :: (SMTBackend b m,SMTType t) => b -> Map Integer AnyRevVar
             -> RevVar t -> TransType t
             -> m (TransVar t,Map Integer AnyRevVar,b)
      mkFuns b rev cur (NormalType ann::TransType t) = do
        (i,nb) <- smtHandle b (SMTDeclareFun
                               (FunInfo { funInfoProxy = Proxy::Proxy ([SMTExpr Untyped],t)
                                        , funInfoArgAnn = argTps
                                        , funInfoResAnn = ann
                                        , funInfoName = Nothing }))
        return (NormalVar i ann,Map.insert i (AnyRevVar cur) rev,nb)
      mkFuns b rev cur (SingletonType fields) = do
        (vars,nrev,nb) <- mkFuns' b rev cur fields
        return (SingletonVar vars,nrev,nb)
      mkFuns b rev cur (ConstrType cons) = do
        (cons',nrev,nb) <- mkCons' b rev cur cons
        return (ConstrVar cons',nrev,nb)
      mkFuns' :: (SMTBackend b m,SMTType t) => b -> Map Integer AnyRevVar
              -> RevVar t -> [TransField t TransType]
              -> m ([TransField t TransVar],Map Integer AnyRevVar,b)
      mkFuns' b rev cur [] = return ([],rev,b)
      mkFuns' b rev cur ((TransField f tp):tps) = do
        (var,rev1,b1) <- mkFuns b rev (RevField cur f) tp
        (vars,rev2,b2) <- mkFuns' b1 rev1 cur tps
        return ((TransField f var):vars,rev2,b2)
      mkCons' :: (SMTBackend b m,SMTType t) => b -> Map Integer AnyRevVar
              -> RevVar t -> [(TransConstr t (),[TransField t TransType])]
              -> m ([(TransConstr t Integer,[TransField t TransVar])],Map Integer AnyRevVar,b)
      mkCons' b rev cur [] = return ([],rev,b)
      mkCons' b rev cur ((TransConstr con (),fields):cons) = do
        (act,b1) <- smtHandle b (SMTDeclareFun
                                 (FunInfo { funInfoProxy = Proxy::Proxy ([SMTExpr Untyped],Bool)
                                          , funInfoArgAnn = argTps
                                          , funInfoResAnn = ()
                                          , funInfoName = Nothing }))
        let rev1 = Map.insert act (AnyRevVar $ RevConstr cur con) rev
        (vars,rev2,b2) <- mkFuns' b1 rev1 cur fields
        (cons',rev3,b3) <- mkCons' b2 rev2 cur cons
        return ((TransConstr con act,vars):cons',rev3,b3)
  smtHandle em (SMTAssert expr igrp cid) = do
    let dts = emulatedDataTypes em
    ((),nb) <- smtHandle (emulatedBackend em)
               (SMTAssert (toNormalExpr (translateExpr em Map.empty expr)) igrp cid)
    return ((),em { emulatedBackend = nb })
  smtHandle em (SMTDefineFun name (_::Proxy arg) argAnn (body::SMTExpr res)) = do
    (mp,rev,nb) <- mkFuns (emulatedBackend em)
                   (RevNormal (nextFreeVar em) (extractAnnotation body))
                   (revMapping em)
                   bodies
    return (nextFreeVar em,em { emulatedBackend = nb
                              , nextFreeVar = (nextFreeVar em)+1
                              , varMapping = Map.insert (nextFreeVar em)
                                             (AnyTransVar mp)
                                             (varMapping em)
                              , revMapping = rev
                              })
    where
      argTps = fmap translateType $
               getTypes (undefined::arg) argAnn
      (argMp,argLst) = mkArgMp 0 0 argTps Map.empty
      bodies = translateExpr em argMp body
      mkArgMp :: Integer -> Integer -> [AnyTransType] -> Map Integer AnyTransVar
              -> (Map Integer AnyTransVar,[ProxyArg])
      mkArgMp n m [] mp = (mp,[])
      mkArgMp n m (AnyTransType tp:tps) mp
        = let (vars,m',lst) = mkArgMp' m tp
              nmp = Map.insert n (AnyTransVar vars) mp
              (rmp,rlst) = mkArgMp (n+1) m' tps nmp
          in (rmp,lst++rlst)
      mkArgMp' :: SMTType t => Integer -> TransType t -> (TransVar t,Integer,[ProxyArg])
      mkArgMp' m (NormalType tp::TransType t)
        = (NormalVar m tp,m+1,[ProxyArg (undefined::t) tp])
      mkArgMp' m (SingletonType tps)
        = let (tps',m',lst) = mkArgMps m tps
          in (SingletonVar tps',m',lst)
      mkArgMp' m (ConstrType cons)
        = let (cons',m',lst) = mkConMp m cons
          in (ConstrVar cons',m',lst)
      mkArgMps :: SMTType t => Integer -> [TransField t TransType]
               -> ([TransField t TransVar],Integer,[ProxyArg])
      mkArgMps m [] = ([],m,[])
      mkArgMps m ((TransField f tp):tps)
        = let (tp',m1,lst1) = mkArgMp' m tp
              (tps',m2,lst2) = mkArgMps m1 tps
          in ((TransField f tp'):tps',m2,lst1++lst2)
      mkConMp :: SMTType t => Integer -> [(TransConstr t (),[TransField t TransType])]
              -> ([(TransConstr t Integer,[TransField t TransVar])],Integer,[ProxyArg])
      mkConMp m [] = ([],m,[])
      mkConMp m ((TransConstr con (),fields):cons)
        = let (fields',m1,lst1) = mkArgMps (m+1) fields
              (cons',m2,lst2) = mkConMp m1 cons
          in ((TransConstr con m,fields'):cons',m2,
              [ProxyArg (undefined::Bool) ()]++lst1++lst2)
      mkFuns :: (SMTBackend b m,SMTType t) => b -> RevVar t -> Map Integer AnyRevVar
             -> TransExpr t
             -> m (TransVar t,Map Integer AnyRevVar,b)
      mkFuns b cur rev (NormalExpr e) = do
        (idx,nb) <- smtHandle b
                    (SMTDefineFun Nothing (Proxy::Proxy [SMTExpr Untyped]) argLst e)
        return (NormalVar idx (extractAnnotation e),
                Map.insert idx (AnyRevVar cur) rev,nb)
      mkFuns b cur rev (SingletonExpr es) = do
        (funs,rev',nb) <- mkFuns' b cur rev es
        return (SingletonVar funs,rev',nb)
      mkFuns b cur rev (ConstrExpr es) = do
        (cons,rev',nb) <- mkCons' b cur rev es
        return (ConstrVar cons,rev',nb)
      mkFuns b cur rev (UntypedExprTrans e) = do
        (var,nrev,nb) <- mkFuns b (RevUntyped cur) rev e
        return (UntypedVar var,nrev,nb)
      mkFuns b cur rev (UntypedExprValueTrans e) = do
        (var,nrev,nb) <- mkFuns b (RevUntypedValue cur) rev e
        return (UntypedValueVar var,nrev,nb)
      mkFuns' :: (SMTBackend b m,SMTType t) => b -> RevVar t -> Map Integer AnyRevVar
              -> [TransField t TransExpr]
              -> m ([TransField t TransVar],Map Integer AnyRevVar,b)
      mkFuns' b cur rev [] = return ([],rev,b)
      mkFuns' b cur rev ((TransField f e):es) = do
        (e',rev1,b1) <- mkFuns b (RevField cur f) rev e
        (es',rev2,b2) <- mkFuns' b1 cur rev1 es
        return (TransField f e':es',rev2,b2)
      mkCons' :: (SMTBackend b m,SMTType t) => b -> RevVar t -> Map Integer AnyRevVar
              -> [(TransConstr t (SMTExpr Bool),[TransField t TransExpr])]
              -> m ([(TransConstr t Integer,[TransField t TransVar])],Map Integer AnyRevVar,b)
      mkCons' b cur rev [] = return ([],rev,b)
      mkCons' b cur rev ((TransConstr constr act,fields):cons) = do
        (iact,b1) <- smtHandle b (SMTDefineFun Nothing (Proxy::Proxy [SMTExpr Untyped]) argLst act)
        (fields',rev1,b2) <- mkFuns' b1 cur
                             (Map.insert iact (AnyRevVar $ RevConstr cur constr) rev)
                             fields
        (cons',rev2,b3) <- mkCons' b2 cur rev1 cons
        return ((TransConstr constr iact,fields'):cons',rev2,b3)
  smtHandle em (SMTGetValue (expr::SMTExpr t)) = case unmangle of
    ComplexUnmangling f -> do
      (res,nem) <- f (\em expr' ann -> smtHandle em (SMTGetValue expr')
                     ) em expr (extractAnnotation expr)
      case res of
       Just x -> return (x,nem)
       Nothing -> error $ "smtlib2-emulated-datatypes: Error while unmangling expression "++show expr++" to type "++show (typeOf (undefined::t))
    PrimitiveUnmangling f -> case asDataType (undefined::t) ann of
      Just (name,tc) -> case find (\dt -> dataTypeName dt==name) (dataTypes tc) of
        Just dt -> do
          (rv,nb) <- unm (emulatedBackend em) dt prx (translateExpr em Map.empty expr)
          case f rv ann of
           Just res -> return (res,em { emulatedBackend = nb })
      Nothing -> case translateExpr em Map.empty expr of
        NormalExpr e -> do
          (res,nb) <- smtHandle (emulatedBackend em) (SMTGetValue e)
          return (res,em { emulatedBackend = nb })
      where
        ann = extractAnnotation expr
        prx = getProxyArgs (undefined::t) ann
        unm :: (SMTBackend b m,SMTType a) => b -> DataType -> [ProxyArg] -> TransExpr a -> m (Value,b)
        unm b dt prx (NormalExpr e::TransExpr a)
          = case (asValueType (undefined::a) (extractAnnotation e) $
                  \(_::a') ann -> case cast e of
                  Just (e'::SMTExpr a') -> do
                    (res,nb) <- smtHandle b (SMTGetValue e')
                    case mangle of
                     PrimitiveMangling p -> return (p res ann,nb)) of
             Just res -> res
        unm b dt prx (SingletonExpr fields::TransExpr a)
          = case dataTypeConstructors dt of
             [con] -> do
               (fields',nb) <- unmFields b (undefined::a) prx fields
               return (ConstrValue (conName con) fields'
                       (Just (dataTypeName dt,[ getSort u ann | ProxyArg u ann <- prx ])),nb)
        unm b dt prx (ConstrExpr cons::TransExpr a) = do
          (name,fields,nb) <- unmConstr b (undefined::a) prx cons
          return (ConstrValue name fields
                  (Just (dataTypeName dt,[ getSort u ann | ProxyArg u ann <- prx ])),nb)
        unmFields :: (SMTBackend b m,SMTType a) => b -> a -> [ProxyArg]
                     -> [TransField a TransExpr]
                     -> m ([Value],b)
        unmFields b u prx [] = return ([],b)
        unmFields b u prx (TransField (Field _ _ _ f) e:es)
          = fieldGet f prx u
            (\(nu::q) nann -> case asDataType nu nann of
              Just (name,tc) -> case find (\dt -> dataTypeName dt==name) (dataTypes tc) of
                Just dt -> do
                  (v,b1) <- unm b dt (getProxyArgs nu nann) (case cast e of
                                                              Just e' -> e'::TransExpr q)
                  (vs,b2) <- unmFields b1 u prx es
                  return (v:vs,b2))
        unmConstr :: (SMTBackend b m,SMTType a) => b -> a -> [ProxyArg]
                  -> [(TransConstr a (SMTExpr Bool),[TransField a TransExpr])]
                  -> m (String,[Value],b)
        unmConstr b u prx ((TransConstr (Constructor _ _ con) act,fields):es) = do
          (val,b1) <- smtHandle b (SMTGetValue act)
          if val
            then (do
                     (fields',b2) <- unmFields b1 u prx fields
                     return (conName con,fields',b2))
            else unmConstr b1 u prx es
  smtHandle em (SMTGetInterpolant grps) = do
    (interp,nb) <- smtHandle (emulatedBackend em) (SMTGetInterpolant grps)
    return (reTranslateExpr (revMapping em) interp,em { emulatedBackend = nb })
  smtHandle em req = do
      (resp,nb) <- smtHandle (emulatedBackend em) req
      return (resp,em { emulatedBackend = nb })

linearizeArgs :: Args args => DataTypeEmulator b -> args -> [SMTExpr Untyped]
linearizeArgs em args = [ e
                        | arg <- fromArgs args
                        , e <- entype (linearize . translateExpr em Map.empty) arg ]

linearize :: SMTType t => TransExpr t -> [SMTExpr Untyped]
linearize (NormalExpr x) = [UntypedExpr x]
linearize (AnyExpr ann::TransExpr t) = [UntypedExpr (defaultExpr ann::SMTExpr t)]
linearize (SingletonExpr xs) = [ e'
                               | TransField f e <- xs
                               , e' <- linearize e ]
linearize (ConstrExpr cons) = [ e
                              | (TransConstr c act,fields) <- cons
                              , e <- (UntypedExpr act):
                                     [ e'
                                     | TransField f e <- fields
                                     , e' <- linearize e ] ]

{-linearizeVars :: TransVar Untyped -> [(Integer,ProxyArg)]
linearizeVars (NormalVar i ann) = [(i,ann)]
linearizeVars (SingletonVar vars)
  = concat $ fmap linearizeVars vars
linearizeVars (ConstrVar cons)
  = concat $ fmap (\(i,con) -> (i,ProxyArg (undefined::Bool) ()):
                               (concat $ fmap linearizeVars con)
                  ) cons

translateFunInfo :: FunInfo
                 -> ([ProxyArg],Trans ProxyArg)
translateFunInfo (FunInfo { funInfoProxy = (_::Proxy (arg,res))
                          , funInfoArgAnn = argAnn
                          , funInfoResAnn = resAnn })
  = (argTps',retTp)
  where
    argTps = fmap translateType $
             getTypes (undefined::arg) argAnn
    argTps' = concat $ fmap linearizeTrans argTps
    retTp = translateType (ProxyArg (undefined::res) resAnn)-}

translateType :: ProxyArg -> AnyTransType
translateType (ProxyArg u ann) = AnyTransType $ translateType' u ann

translateType' :: SMTType t => t -> SMTAnnotation t
               -> TransType t
translateType' (u::t) ann = case asDataType u ann of
  Nothing -> NormalType ann
  Just (name,tc)
    -> case [ dt | dt <- dataTypes tc
                 , dataTypeName dt == name ] of
        dt:_ -> case dataTypeConstructors dt of
          [con] -> SingletonType
                   [ fieldGet field prxs u
                     (\f fann -> TransField (Field prxs dt con field)
                                 (translateType' f fann))
                   | field <- conFields con ]
          cons -> ConstrType
                  [ conUndefinedArgs con prxs $
                    \(_::arg) _ -> (TransConstr (Constructor prxs dt con
                                                 ::Constructor arg t) (),
                                    [ fieldGet field prxs u
                                      (\f fann -> TransField (Field prxs dt con field)
                                                  (translateType' f fann))
                                    | field <- conFields con ])
                  | con <- cons ]
    where
      prxs = getProxyArgs u ann

linearizeType :: SMTType t => TransType t -> [ProxyArg]
linearizeType (NormalType ann::TransType t) = [ProxyArg (undefined::t) ann]
linearizeType (SingletonType fields)
  = [ prx
    | TransField _ tp <- fields
    , prx <- linearizeType tp ]
linearizeType (ConstrType cons)
  = [ prx
    | (_,fields) <- cons
    , prx <- (ProxyArg (undefined::Bool) ()):
             [ prx'
             | TransField _ tp <- fields
             , prx' <- linearizeType tp ] ]

removeUntyped :: ProxyArg -> ProxyArg
removeUntyped (ProxyArg u ann) = case cast (u,ann) of
  Just (_::Untyped,ann'::SMTAnnotation Untyped) -> removeUntyped ann'
  Nothing -> case cast (u,ann) of
    Just (_::UntypedValue,ProxyArgValue u ann)
      -> removeUntyped (ProxyArg u ann)
    Nothing -> ProxyArg u ann

linearizeTrans :: Trans a -> [a]
linearizeTrans (Normal tp) = [tp]
linearizeTrans (Singleton tps)
  = concat (fmap linearizeTrans tps)
linearizeTrans (Constr cons)
  = concat $ fmap (\tps -> concat $ fmap linearizeTrans tps
                  ) cons
