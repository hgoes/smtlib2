module Language.SMTLib2.Yices
       (YicesBackend()
       ,withYices
       ,yicesBackend) where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators

import Data.Int
import Data.Word

import Foreign.Ptr
import Foreign.C
import Foreign.Marshal.Array
import Foreign.Marshal.Alloc
import Foreign.Storable

import Data.IORef
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ratio
import Data.Fix
import Data.Foldable (foldlM)
import Data.Typeable (cast)
import Data.Bits
import Data.Proxy

#include <yices.h>

type Term = Int32
type Type = Int32

newtype CtxConfig = CtxConfig (Ptr CtxConfig)
newtype Context = Context (Ptr Context)
newtype Param = Param (Ptr Param)
newtype Model = Model (Ptr Model)

data YicesBackend = YicesBackend { yicesState :: IORef YicesState
                                 , yicesTypes :: IORef (Map String (Type,[String]))
                                 , yicesExprs :: IORef (Map Integer Term)
                                 }

data YicesState = NoContext CtxConfig
                | HasContext Context (Maybe Model)

withYices :: IO a -> IO a
withYices act = do
  yicesInit
  res <- act
  yicesExit
  return res

yicesBackend :: IO YicesBackend
yicesBackend = do
  cfg <- yicesNewConfig
  withCString "mode" $
    \mode -> withCString "push-pop" $
             \pp -> yicesSetConfig cfg mode pp
  state <- newIORef (NoContext cfg)
  tps <- newIORef Map.empty
  exprs <- newIORef Map.empty
  return (YicesBackend state tps exprs)

getContext :: YicesBackend -> Bool -> IO Context
getContext b discard = do
  state <- readIORef (yicesState b)
  case state of
    HasContext ctx Nothing -> return ctx
    HasContext ctx (Just mdl) -> if discard
                                 then (do
                                          yicesFreeModel mdl
                                          writeIORef (yicesState b) (HasContext ctx Nothing)
                                          return ctx)
                                 else return ctx
    NoContext cfg -> do
      ctx <- yicesNewContext cfg
      yicesFreeConfig cfg
      writeIORef (yicesState b) (HasContext ctx Nothing)
      return ctx

getConfig :: YicesBackend -> IO (Maybe CtxConfig)
getConfig b = do
  state <- readIORef (yicesState b)
  case state of
    NoContext cfg -> return (Just cfg)
    _ -> return Nothing

getModel :: YicesBackend -> IO (Maybe Model)
getModel b = do
  state <- readIORef (yicesState b)
  case state of
    HasContext ctx mdl -> case mdl of
      Just mdl' -> return (Just mdl')
      Nothing -> do
        mdl'@(Model ptr) <- yicesGetModel ctx 1
        if ptr==nullPtr
          then return Nothing
          else (do
                   writeIORef (yicesState b) (HasContext ctx (Just mdl'))
                   return (Just mdl'))
    _ -> return Nothing

getError :: IO String
getError = do
  code <- yicesErrorCode
  return $ case code of
    #{const NO_ERROR} -> "No error"
    #{const INVALID_TYPE} -> "Invalid type"
    #{const INVALID_TERM} -> "Invalid term"
    #{const INVALID_VAR_INDEX} -> "Invalid variable index"
    #{const INVALID_TUPLE_INDEX} -> "Invalid tuple index"
    #{const INVALID_RATIONAL_FORMAT} -> "Invalid rational format"
    #{const INVALID_FLOAT_FORMAT} -> "Invalid float format"
    _ -> "Unknown code "++show code

mkError :: String -> IO a
mkError msg = do
  msg2 <- getError
  error $ "smtlib2-yices: "++msg++" ("++msg2++")"

instance SMTBackend YicesBackend IO where
  smtHandle b _ (SMTSetLogic l) = do
    mcfg <- getConfig b
    case mcfg of
      Nothing -> mkError "Can't set logic after asserting formulas."
      Just cfg -> do
        res <- withCString l $ yicesDefaultConfigForLogic cfg
        if res < 0
          then mkError $ "Unsupported logic "++l
          else return ()
  smtHandle _ _ (SMTGetInfo SMTSolverName) = return "yices"
  smtHandle _ _ (SMTGetInfo SMTSolverVersion) = do
    ptr <- peek yicesVersion
    peekCString ptr
  smtHandle _ _ (SMTSetOption _) = return ()
  smtHandle b _ (SMTAssert f Nothing Nothing) = do
    tps <- readIORef (yicesTypes b)
    mp <- readIORef (yicesExprs b)
    ctx <- getContext b True
    f' <- exprToTerm tps mp 0 f
    res <- yicesAssertFormula ctx f'
    if res < 0
      then mkError $ "Error while asserting formula."
      else return ()
  smtHandle b _ (SMTCheckSat _ _) = do
    ctx <- getContext b False
    params <- yicesNewParamRecord
    -- TODO: Set parameters, maybe according to tactic
    res <- yicesCheckContext ctx params
    yicesFreeParamRecord params
    case res of
      #{const STATUS_SAT} -> return Sat
      #{const STATUS_UNSAT} -> return Unsat
      #{const STATUS_UNKNOWN} -> return Unknown
      #{const STATUS_INTERRUPTED} -> mkError "The check-sat query was interrupted."
  smtHandle b _ (SMTDeclareDataTypes tc)
    = if argCount tc > 0
      then error "smtlib2-yices: No support for parametrized data types."
      else do
        new_tps <- mapM (\dt -> do
                            cons <- mapM (\con -> case conFields con of
                                             _:_ -> error "smtlib2-yices: Only enumeration types supported."
                                             [] -> return $ conName con
                                         ) (dataTypeConstructors dt)
                            tp <- yicesNewScalarType (fromIntegral $ length cons)
                            return (dataTypeName dt,(tp,cons))
                        ) (dataTypes tc)
        modifyIORef (yicesTypes b) (Map.union (Map.fromList new_tps))
  smtHandle b _ (SMTDeclareSort name par)
    = if par > 0
      then error "smtlib2-yices: No support for parametrized data types."
      else do
        tp <- yicesNewUninterpretedType
        modifyIORef (yicesTypes b) (Map.insert name (tp,[]))
  smtHandle b _ SMTPush = do
    ctx <- getContext b False
    res <- yicesPush ctx
    if res < 0
      then mkError "Error while pushing to stack."
      else return ()
  smtHandle b _ SMTPop = do
    ctx <- getContext b True
    res <- yicesPop ctx
    if res < 0
      then mkError "Error while popping from stack."
      else return ()
  smtHandle b _ (SMTDefineFun fname args body) = do
    tps <- readIORef (yicesTypes b)
    mp <- readIORef (yicesExprs b)
    rargs <- mapM (\info -> do
                      tp <- sortToType tps (funInfoSort info)
                      arg <- yicesNewVariable tp
                      return (funInfoId info,arg)
                  ) args
    body <- exprToTerm tps (Map.union mp (Map.fromList rargs)) 0 body
    fun <- if null rargs
           then return body
           else withArrayLen (fmap snd rargs) $
                \len arr -> yicesLambda (fromIntegral len) arr body
    modifyIORef (yicesExprs b) (Map.insert (funInfoId fname) fun)
  smtHandle b _ (SMTDeclareFun fname) = do
    tps <- readIORef (yicesTypes b)
    argTps <- mapM (sortToType tps) (funInfoArgSorts fname)
    retTp <- sortToType tps (funInfoSort fname)
    funTp <- if null argTps
             then return retTp
             else withArrayLen argTps $
                  \len arr -> yicesFunctionType (fromIntegral len) arr retTp
    fun <- yicesNewUninterpretedTerm funTp
    modifyIORef (yicesExprs b) (Map.insert (funInfoId fname) fun)
  smtHandle b st (SMTGetValue (expr :: SMTExpr t)) = do
    mmdl <- getModel b
    case mmdl of
      Nothing -> error $ "smtlib2-yices: No model available."
      Just mdl -> do
        tps <- readIORef (yicesTypes b)
        mp <- readIORef (yicesExprs b)
        term <- exprToTerm tps mp 0 expr
        let sort = getSort (undefined::t) (extractAnnotation expr)
        case sort of
          Fix BoolSort -> alloca $ \res -> do
            yicesGetBoolValue mdl term res
            val <- peek res
            case cast (val/=0) of
              Just ret -> return ret
          Fix IntSort -> alloca $ \res -> do
            yicesGetInt64Value mdl term res
            val <- peek res
            case cast (toInteger val) of
              Just ret -> return ret
          Fix RealSort -> alloca $ \res1 ->
            alloca $ \res2 -> do
              yicesGetRational64Value mdl term res1 res2
              val1 <- peek res1
              val2 <- peek res2
              case cast ((toInteger val1) % (toInteger val2)) of
                Just ret -> return ret
          Fix (BVSort { bvSortWidth = w
                      , bvSortUntyped = unt }) -> allocaArray (fromIntegral w) $ \arr -> do
            yicesGetBVValue mdl term arr
            vals <- peekArray (fromIntegral w) arr
            let ret = fst $ foldl (\(cur,i) v -> (if v==1
                                                  then setBit cur i
                                                  else cur,i+1)
                                  ) (0,0) vals
            if unt
              then (case cast (BitVector ret :: BitVector BVUntyped) of
                       Just r -> return r)
              else (reifyNat w (\(_::Proxy bw) -> case cast (BitVector ret :: BitVector (BVTyped bw)) of
                                   Just r -> return r))
          Fix (NamedSort name []) -> alloca $ \res -> do
            yicesGetScalarValue mdl term res
            idx <- peek res
            case Map.lookup name (datatypes $ declaredDataTypes st) of
              Just (dt,_) -> do
                let constr = (dataTypeConstructors dt)!!(fromIntegral idx)
                construct constr [] [] $ \_ res _ -> do
                  case cast res of
                    Just ret -> return ret
  smtHandle _ _ SMTGetProof = error "smtlib2-yices: Proof extraction not supported."
  smtHandle _ _ SMTGetUnsatCore = error "smtlib2-yices: Unsat core extraction not supported."
  smtHandle _ _ (SMTSimplify expr) = return expr
  smtHandle _ _ (SMTGetInterpolant _) = error "smtlib2-yices: Interpolation not supported."
  smtHandle _ _ (SMTComment _) = return ()
  smtHandle b _ SMTExit = do
    state <- readIORef (yicesState b)
    case state of
      NoContext cfg -> yicesFreeConfig cfg
      HasContext ctx mdl -> do
        case mdl of
          Nothing -> return ()
          Just mdl' -> yicesFreeModel mdl'
        yicesFreeContext ctx
  smtHandle _ _ (SMTApply _) = error "smtlib2-yices: No support for tactics."
      

sortToType :: Map String (Type,[String]) -> Sort -> IO Type
sortToType _ (Fix BoolSort) = yicesBoolType
sortToType _ (Fix IntSort) = yicesIntType
sortToType _ (Fix RealSort) = yicesRealType
sortToType _ (Fix (BVSort w _)) = yicesBVType (fromInteger w)
sortToType tps (Fix (ArraySort idx val)) = do
  idxTypes <- mapM (sortToType tps) idx
  valType <- sortToType tps val
  withArrayLen idxTypes
    (\len ptr -> yicesFunctionType (fromIntegral len) ptr valType)
sortToType tps (Fix (NamedSort name [])) = case Map.lookup name tps of
    Just (tp,_) -> return tp
    Nothing -> error $ "smtlib2-yices: Named sort "++name++" not found."
sortToType _ (Fix (NamedSort name _))
  = error $ "smtlib2-yices: Named sorts with parameters unsupported."

findConstructor :: Map String (Type,[String]) -> String -> (String,Type,Int)
findConstructor mp cname = findCons (Map.toList mp)
  where
    findCons [] = error $ "smtlib2-yices: Constructor "++cname++" has no type."
    findCons ((tpName,(tp,cons)):rest) = case elemIndex cname cons of
      Just idx -> (tpName,tp,idx)
      Nothing -> findCons rest

exprToTerm :: SMTType a => Map String (Type,[String]) -> Map Integer Term -> Integer
              -> SMTExpr a
              -> IO Term
exprToTerm _ mp _ (Var name ann) = case Map.lookup name mp of
  Just t -> return t
exprToTerm tps _ _ (Const c ann) = do
  let val = mangle c ann
  case val of
    BoolValue True -> yicesTrue
    BoolValue False -> yicesFalse
    IntValue i -> yicesInt64 (fromInteger i)
    RealValue i -> yicesRational64
                   (fromInteger $ numerator i)
                   (fromInteger $ denominator i)
    BVValue w v -> yicesBVConst64 (fromInteger w) (fromInteger v)
    ConstrValue name _ sort -> case sort of
      Just (n,[]) -> case Map.lookup n tps of
        Just (tp,cons) -> case elemIndex name cons of
          Just idx -> yicesConstant tp (fromIntegral idx)
      Nothing -> do
        let (_,tp,num) = findConstructor tps name
        yicesConstant tp (fromIntegral num)
exprToTerm tps mp i (AsArray (SMTFun fname _) _) = case Map.lookup fname mp of
  Just fterm -> return fterm
exprToTerm tps mp i (AsArray fun ann) = do
  let (arg,names,ni,_) = createArgs ann i Map.empty
  vars <- mapM (\info -> do
                   tp <- sortToType tps (funInfoSort info)
                   var <- yicesNewVariable tp
                   return (funInfoId info,var)
               ) names
  let nmp = Map.union mp (Map.fromList vars)
  body <- exprToTerm tps nmp ni (App fun arg)
  withArrayLen (fmap snd vars) $
    \len arr -> yicesLambda (fromIntegral len) arr body
exprToTerm tps mp i (Forall ann f) = do
  let (arg,names,ni,_) = createArgs ann i Map.empty
  vars <- mapM (\info -> do
                   tp <- sortToType tps (funInfoSort info)
                   var <- yicesNewVariable tp
                   return (funInfoId info,var)
               ) names
  body <- exprToTerm tps (Map.union mp (Map.fromList vars)) ni (f arg)
  withArrayLen (fmap snd vars) (\len arr -> yicesForall (fromIntegral len) arr body)
exprToTerm tps mp i (Exists ann f) = do
  let (arg,names,ni,_) = createArgs ann i Map.empty
  vars <- mapM (\info -> do
                   tp <- sortToType tps (funInfoSort info)
                   var <- yicesNewVariable tp
                   return (funInfoId info,var)
               ) names
  body <- exprToTerm tps (Map.union mp (Map.fromList vars)) ni (f arg)
  withArrayLen (fmap snd vars) (\len arr -> yicesExists (fromIntegral len) arr body)
exprToTerm tps mp i (Let ann args f)
  = exprToTerm tps mp i (f args)
exprToTerm tps mp i (App SMTEq [x,y]) = do
  tx <- exprToTerm tps mp i x
  ty <- exprToTerm tps mp i y
  yicesEq tx ty
exprToTerm _ _ _ (App (SMTMap f) _)
  = error $ "smtlib2-yices: Mapping functions not supported."
exprToTerm tps mp i (App (SMTFun fname fann) args)
  = case Map.lookup fname mp of
  Just fun -> do
    let (acts,_) = unpackArgs (\expr _ _ -> (exprToTerm tps mp i expr,())) args undefined ()
    rargs <- sequence acts
    withArrayLen rargs (\len arr -> yicesApplication fun (fromIntegral len) arr)
exprToTerm tps mp i (App (SMTOrd op) (x,y)) = do
  tx <- exprToTerm tps mp i x
  ty <- exprToTerm tps mp i y
  (case op of
      Ge -> yicesArithGEqAtom
      Gt -> yicesArithGtAtom
      Le -> yicesArithLEqAtom
      Lt -> yicesArithLtAtom) tx ty
exprToTerm tps mp i (App (SMTArith op) args) = do
  x:xs <- mapM (exprToTerm tps mp i) args
  let f = case op of
        Plus -> yicesAdd
        Mult -> yicesMul
  foldlM f x xs
exprToTerm tps mp i (App SMTMinus (x,y)) = do
  tx <- exprToTerm tps mp i x
  ty <- exprToTerm tps mp i y
  yicesSub tx ty
exprToTerm tps mp i (App (SMTIntArith op) _)
  = error $ "smtlib2-yices: Integer operator "++show op++" not supported."
exprToTerm tps mp i (App SMTDivide _)
  = error $ "smtlib2-yices: Rational division not supported."
exprToTerm tps mp i (App SMTNeg x) = do
  tx <- exprToTerm tps mp i x
  yicesNeg tx
exprToTerm tps mp i (App SMTAbs x)
  = case cast x of
  Just x' -> exprToTerm tps mp i (App SMTITE
                                  (App (SMTOrd Ge) (x',Const (0::Integer) ()),
                                   x',
                                   App SMTNeg x'))
  Nothing -> case cast x of
    Just x' -> exprToTerm tps mp i (App SMTITE
                                    (App (SMTOrd Ge) (x',Const (0::Rational) ()),
                                     x',
                                     App SMTNeg x'))
exprToTerm tps mp i (App SMTNot x) = do
  tx <- exprToTerm tps mp i x
  yicesNot tx
exprToTerm tps mp i (App (SMTLogic op) args) = do
  rargs <- mapM (exprToTerm tps mp i) args
  case op of
    Implies -> case rargs of
      [x,y] -> yicesImplies x y
    _ -> withArrayLen rargs $
         \len arr -> (case op of
                         And -> yicesAnd
                         Or -> yicesOr
                         XOr -> yicesXor) (fromIntegral len) arr
exprToTerm tps mp i (App SMTDistinct args) = do
  rargs <- mapM (exprToTerm tps mp i) args
  withArrayLen rargs $
    \len arr -> yicesDistinct (fromIntegral len) arr
exprToTerm tps mp i (App SMTToReal _)
  = error "smtlib2-yices: to-real operation not supported."
exprToTerm tps mp i (App SMTToInt _)
  = error "smtlib2-yices: to-int operation not supported."
exprToTerm tps mp i (App SMTITE (c,x,y)) = do
  tc <- exprToTerm tps mp i c
  tx <- exprToTerm tps mp i x
  ty <- exprToTerm tps mp i y
  yicesITE tc tx ty
exprToTerm tps mp i (App (SMTBVComp op) (x,y)) = do
  tx <- exprToTerm tps mp i x
  ty <- exprToTerm tps mp i y
  (case op of
      BVULE -> yicesBVLeAtom
      BVULT -> yicesBVLtAtom
      BVUGE -> yicesBVGeAtom
      BVUGT -> yicesBVGtAtom
      BVSLE -> yicesBVSLeAtom
      BVSLT -> yicesBVSLtAtom
      BVSGE -> yicesBVSGeAtom
      BVSGT -> yicesBVSGtAtom) tx ty
exprToTerm tps mp i (App (SMTBVBin bin) (x,y)) = do
  tx <- exprToTerm tps mp i x
  ty <- exprToTerm tps mp i y
  (case bin of
      BVAdd -> yicesBVAdd
      BVSub -> yicesBVSub
      BVMul -> yicesBVMul
      BVURem -> yicesBVRem
      BVSRem -> yicesBVSRem
      BVUDiv -> yicesBVDiv
      BVSDiv -> yicesBVSDiv
      BVSHL -> yicesBVSHL
      BVLSHR -> yicesBVLSHR
      BVASHR -> yicesBVASHR
      BVXor -> yicesBVXor
      BVAnd -> yicesBVAnd
      BVOr -> yicesBVOr) tx ty
exprToTerm tps mp i (App (SMTBVUn op) x) = do
  tx <- exprToTerm tps mp i x
  (case op of
      BVNot -> yicesBVNot
      BVNeg -> yicesBVNeg) tx
exprToTerm tps mp i (App SMTSelect (arr,idx)) = do
  tarr <- exprToTerm tps mp i arr
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToTerm tps mp i arg,())) idx
                   (extractArgAnnotation idx) ()
  tidx <- sequence argLst
  withArrayLen tidx $
    \len arr -> yicesApplication tarr (fromIntegral len) arr
exprToTerm tps mp i (App SMTStore (arr,idx,val)) = do
  tarr <- exprToTerm tps mp i arr
  tval <- exprToTerm tps mp i val
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToTerm tps mp i arg,())) idx
                   (extractArgAnnotation idx) ()
  tidx <- sequence argLst
  withArrayLen tidx $
    \len arr -> yicesUpdate tarr (fromIntegral len) arr tval
exprToTerm tps mp i (App fun@(SMTConstArray ann) val) = do
  let getUndef :: SMTFunction p (SMTArray i v) -> i
      getUndef _ = undefined
      sorts = argSorts (getUndef fun) ann
  tval <- exprToTerm tps mp i val
  vars <- mapM (\sort -> do
                  tp <- sortToType tps sort
                  yicesNewVariable tp) sorts
  withArrayLen vars $
    \len arr -> yicesLambda (fromIntegral len) arr tval
exprToTerm tps mp i (App SMTConcat (x,y)) = do
  tx <- exprToTerm tps mp i x
  ty <- exprToTerm tps mp i y
  yicesBVConcat tx ty
exprToTerm tps mp i (App (SMTExtract pstart plen) x) = do
  tx <- exprToTerm tps mp i x
  let start = reflectNat pstart 0
      len = reflectNat plen 0
  yicesBVExtract tx (fromIntegral start) (fromIntegral $ len-1)
exprToTerm tps mp i (App (SMTConstructor (Constructor args dt constr)) _)
  = let (_,tp,num) = findConstructor tps (conName constr)
    in yicesConstant tp (fromIntegral num)
exprToTerm tps mp i (App (SMTConTest (Constructor args dt constr)) x) = do
  tx <- exprToTerm tps mp i x
  let (_,tp,num) = findConstructor tps (conName constr)
  ty <- yicesConstant tp (fromIntegral num)
  yicesEq tx ty

foreign import capi "yices.h &yices_version"
  yicesVersion :: Ptr CString
    
foreign import capi "yices.h yices_init"
  yicesInit :: IO ()

foreign import capi "yices.h yices_exit"
  yicesExit :: IO ()

foreign import capi "yices.h yices_reset"
  yicesReset :: IO ()

foreign import capi "yices.h yices_error_code"
  yicesErrorCode :: IO CInt

foreign import capi "yices.h yices_bool_type"
  yicesBoolType :: IO Type

foreign import capi "yices.h yices_int_type"
  yicesIntType :: IO Type

foreign import capi "yices.h yices_real_type"
  yicesRealType :: IO Type

foreign import capi "yices.h yices_bv_type"
  yicesBVType :: Word32 -> IO Type

foreign import capi "yices.h yices_new_scalar_type"
  yicesNewScalarType :: Word32 -> IO Type

foreign import capi "yices.h yices_new_uninterpreted_type"
  yicesNewUninterpretedType :: IO Type

foreign import capi "yices.h yices_tuple_type"
  yicesTupleType :: Word32 -> Ptr Type -> IO Type

foreign import capi "yices.h yices_function_type"
  yicesFunctionType :: Word32 -> Ptr Type -> Type -> IO Type

foreign import capi "yices.h yices_true"
  yicesTrue :: IO Term

foreign import capi "yices.h yices_false"
  yicesFalse :: IO Term

foreign import capi "yices.h yices_constant"
  yicesConstant :: Type -> Int32 -> IO Term

foreign import capi "yices.h yices_new_uninterpreted_term"
  yicesNewUninterpretedTerm :: Type -> IO Term

foreign import capi "yices.h yices_new_variable"
  yicesNewVariable :: Type -> IO Term

foreign import capi "yices.h yices_application"
  yicesApplication :: Term -> Word32 -> Ptr Term -> IO Term

foreign import capi "yices.h yices_ite"
  yicesITE :: Term -> Term -> Term -> IO Term

foreign import capi "yices.h yices_eq"
  yicesEq :: Term -> Term -> IO Term

foreign import capi "yices.h yices_neq"
  yicesNEq :: Term -> Term -> IO Term

foreign import capi "yices.h yices_not"
  yicesNot :: Term -> IO Term

foreign import capi "yices.h yices_or"
  yicesOr :: Word32 -> Ptr Term -> IO Term

foreign import capi "yices.h yices_and"
  yicesAnd :: Word32 -> Ptr Term -> IO Term

foreign import capi "yices.h yices_xor"
  yicesXor :: Word32 -> Ptr Term -> IO Term

foreign import capi "yices.h yices_iff"
  yicesIff :: Term -> Term -> IO Term

foreign import capi "yices.h yices_implies"
  yicesImplies :: Term -> Term -> IO Term

foreign import capi "yices.h yices_tuple"
  yicesTuple :: Word32 -> Ptr Term -> IO Term

foreign import capi "yices.h yices_select"
  yicesSelect :: Word32 -> Term -> IO Term

foreign import capi "yices.h yices_tuple_update"
  yicesTupleUpdate :: Term -> Word32 -> Term -> IO Term

foreign import capi "yices.h yices_update"
  yicesUpdate :: Term -> Word32 -> Ptr Term -> Term -> IO Term

foreign import capi "yices.h yices_distinct"
  yicesDistinct :: Word32 -> Ptr Term -> IO Term

foreign import capi "yices.h yices_forall"
  yicesForall :: Word32 -> Ptr Term -> Term -> IO Term

foreign import capi "yices.h yices_exists"
  yicesExists :: Word32 -> Ptr Term -> Term -> IO Term

foreign import capi "yices.h yices_lambda"
  yicesLambda :: Word32 -> Ptr Term -> Term -> IO Term

foreign import capi "yices.h yices_int32"
  yicesInt32 :: Int32 -> IO Term

foreign import capi "yices.h yices_int64"
  yicesInt64 :: Int64 -> IO Term

foreign import capi "yices.h yices_rational32"
  yicesRational32 :: Int32 -> Int32 -> IO Term

foreign import capi "yices.h yices_rational64"
  yicesRational64 :: Int64 -> Int64 -> IO Term

foreign import capi "yices.h yices_parse_rational"
  yicesParseRational :: CString -> IO Term

foreign import capi "yices.h yices_add"
  yicesAdd :: Term -> Term -> IO Term

foreign import capi "yices.h yices_sub"
  yicesSub :: Term -> Term -> IO Term

foreign import capi "yices.h yices_neg"
  yicesNeg :: Term -> IO Term

foreign import capi "yices.h yices_mul"
  yicesMul :: Term -> Term -> IO Term

foreign import capi "yices.h yices_power"
  yicesPower :: Term -> Term -> IO Term

foreign import capi "yices.h yices_arith_eq_atom"
  yicesArithEqAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_arith_neq_atom"
  yicesArithNEqAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_arith_geq_atom"
  yicesArithGEqAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_arith_leq_atom"
  yicesArithLEqAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_arith_gt_atom"
  yicesArithGtAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_arith_lt_atom"
  yicesArithLtAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvconst_uint32"
  yicesBVConst32 :: Word32 -> Word32 -> IO Term

foreign import capi "yices.h yices_bvconst_uint64"
  yicesBVConst64 :: Word64 -> Word64 -> IO Term

foreign import capi "yices.h yices_parse_bvhex"
  yicesParseBVHex :: CString -> IO Term

foreign import capi "yices.h yices_bvadd"
  yicesBVAdd :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvsub"
  yicesBVSub :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvneg"
  yicesBVNeg :: Term -> IO Term

foreign import capi "yices.h yices_bvmul"
  yicesBVMul :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvpower"
  yicesBVPower :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvdiv"
  yicesBVDiv :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvrem"
  yicesBVRem :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvsdiv"
  yicesBVSDiv :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvsrem"
  yicesBVSRem :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvsmod"
  yicesBVSMod :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvnot"
  yicesBVNot :: Term -> IO Term

foreign import capi "yices.h yices_bvand"
  yicesBVAnd :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvor"
  yicesBVOr :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvxor"
  yicesBVXor :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvnand"
  yicesBVNAnd :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvnor"
  yicesBVNOr :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvxnor"
  yicesBVXNor :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvshl"
  yicesBVSHL :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvlshr"
  yicesBVLSHR :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvashr"
  yicesBVASHR :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvextract"
  yicesBVExtract :: Term -> Word32 -> Word32 -> IO Term

foreign import capi "yices.h yices_bvconcat"
  yicesBVConcat :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bveq_atom"
  yicesBVEqAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvneq_atom"
  yicesBVNEqAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvge_atom"
  yicesBVGeAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvgt_atom"
  yicesBVGtAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvle_atom"
  yicesBVLeAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvlt_atom"
  yicesBVLtAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvsge_atom"
  yicesBVSGeAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvsgt_atom"
  yicesBVSGtAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvsle_atom"
  yicesBVSLeAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_bvslt_atom"
  yicesBVSLtAtom :: Term -> Term -> IO Term

foreign import capi "yices.h yices_type_of_term"
  yicesTypeOfTerm :: Term -> IO Type

foreign import capi "yices.h yices_term_bitsize"
  yicesTermBitsize :: Term -> IO Word32

foreign import capi "yices.h yices_new_config"
  yicesNewConfig :: IO CtxConfig

foreign import capi "yices.h yices_free_config"
  yicesFreeConfig :: CtxConfig -> IO ()

foreign import capi "yices.h yices_set_config"
  yicesSetConfig :: CtxConfig -> CString -> CString -> IO Int32

foreign import capi "yices.h yices_default_config_for_logic"
  yicesDefaultConfigForLogic :: CtxConfig -> CString -> IO Int32

foreign import capi "yices.h yices_new_context"
  yicesNewContext :: CtxConfig -> IO Context

foreign import capi "yices.h yices_free_context"
  yicesFreeContext :: Context -> IO ()

foreign import capi "yices.h yices_push"
  yicesPush :: Context -> IO Int32

foreign import capi "yices.h yices_pop"
  yicesPop :: Context -> IO Int32

foreign import capi "yices.h yices_assert_formula"
  yicesAssertFormula :: Context -> Term -> IO Int32

foreign import capi "yices.h yices_check_context"
  yicesCheckContext :: Context -> Param -> IO CInt

foreign import capi "yices.h yices_stop_search"
  yicesStopSearch :: Context -> IO ()

foreign import capi "yices.h yices_new_param_record"
  yicesNewParamRecord :: IO Param

foreign import capi "yices.h yices_set_param"
  yicesSetParam :: Param -> CString -> CString -> IO Int32

foreign import capi "yices.h yices_free_param_record"
  yicesFreeParamRecord :: Param -> IO ()

foreign import capi "yices.h yices_get_model"
  yicesGetModel :: Context -> Int32 -> IO Model

foreign import capi "yices.h yices_free_model"
  yicesFreeModel :: Model -> IO ()

foreign import capi "yices.h yices_get_bool_value"
  yicesGetBoolValue :: Model -> Term -> Ptr Int32 -> IO Int32

foreign import capi "yices.h yices_get_int32_value"
  yicesGetInt32Value :: Model -> Term -> Ptr Int32 -> IO Int32

foreign import capi "yices.h yices_get_int64_value"
  yicesGetInt64Value :: Model -> Term -> Ptr Int64 -> IO Int32

foreign import capi "yices.h yices_get_rational32_value"
  yicesGetRational32Value :: Model -> Term -> Ptr Int32 -> Ptr Int32 -> IO Int32

foreign import capi "yices.h yices_get_rational64_value"
  yicesGetRational64Value :: Model -> Term -> Ptr Int64 -> Ptr Int64 -> IO Int32

foreign import capi "yices.h yices_get_bv_value"
  yicesGetBVValue :: Model -> Term -> Ptr Int32 -> IO Int32

foreign import capi "yices.h yices_get_scalar_value"
  yicesGetScalarValue :: Model -> Term -> Ptr Int32 -> IO Int32
