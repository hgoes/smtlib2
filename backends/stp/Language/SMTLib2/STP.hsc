module Language.SMTLib2.STP where

#include <stp/c_interface.h>

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators
import Language.SMTLib2.Internals.Instances

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (foldlM)
import Data.Fix
import Data.Proxy
import Data.Typeable
import Data.IORef

import Foreign.Ptr
import Foreign.C
import Foreign.Marshal
import Foreign.Storable

newtype VC = VC (Ptr VC) deriving (Storable)
newtype STPType = STPType (Ptr STPType) deriving (Storable)
newtype STPExpr = STPExpr (Ptr STPExpr) deriving (Storable)

data STPBackend = STPBackend { stpInstance :: VC
                             , stpVars :: IORef (Map Integer STPExpr) }

withSTP :: SMT' IO a -> IO a
withSTP act = do
  b <- stpBackend
  withSMTBackend b act

stpBackend :: IO STPBackend
stpBackend = do
  vars <- newIORef Map.empty
  inst <- stpCreateValidityChecker
  return (STPBackend { stpInstance = inst
                     , stpVars = vars })

instance SMTBackend STPBackend IO where
  smtHandle _ _ (SMTSetLogic _) = return ()
  smtHandle _ _ (SMTGetInfo SMTSolverName) = return "stp"
  smtHandle _ _ (SMTGetInfo SMTSolverVersion) = return "unknown"
  smtHandle _ _ (SMTSetOption _) = return ()
  smtHandle stp _ (SMTAssert expr Nothing) = do
    mp <- readIORef (stpVars stp)
    expr' <- exprToSTP mp stp expr
    stpAssert (stpInstance stp) expr'
  smtHandle stp _ (SMTCheckSat _) = do
    t <- stpFalseExpr (stpInstance stp)
    res <- stpQuery (stpInstance stp) t
    case res of
      1 -> return False
      0 -> return True
      _ -> error $ "smtlib2-stp: Invalid query result "++show res
  smtHandle _ _ (SMTDeclareDataTypes _) = error "smtlib2-stp: No support for datatypes."
  smtHandle _ _ (SMTDeclareSort _ _) = error "smtlib2-stp: No support for sorts."
  smtHandle stp _ SMTPush = stpPush (stpInstance stp)
  smtHandle stp _ SMTPop = stpPop (stpInstance stp)
  smtHandle stp _ (SMTDefineFun name [] expr) = do
    mp <- readIORef (stpVars stp)
    expr' <- exprToSTP mp stp expr
    modifyIORef (stpVars stp) (Map.insert (funInfoId name) expr')
  smtHandle stp _ (SMTDeclareFun name) = do
    case funInfoArgSorts name of
      [] -> return ()
      _ -> error $ "smtlib2-stp: No support for uninterpreted functions."
    tp <- sortToSTP stp (funInfoSort name)
    expr <- stpVarExpr (stpInstance stp) (escapeName $ case funInfoName name of
                                             Nothing -> Right (funInfoId name)
                                             Just name' -> Left name') tp
    modifyIORef (stpVars stp) (Map.insert (funInfoId name) expr)
  smtHandle stp st (SMTGetValue (expr::SMTExpr t)) = do
    mp <- readIORef (stpVars stp)
    expr' <- exprToSTP mp stp expr
    resExpr <- stpGetCounterExample (stpInstance stp) expr'
    stpToExpr (declaredDataTypes st) (namedVars st) (Just $ getSort (undefined::t) (extractAnnotation expr)) resExpr $
      \res -> case res of
        Const val _ -> case cast val of
          Just val' -> val'
  smtHandle _ _ SMTGetProof = error $ "smtlib2-stp: STP doesn't support proof extraction."
  smtHandle _ _ SMTGetUnsatCore = error $ "smtlib2-stp: STP doesn't support unsat core extraction."
  smtHandle stp st (SMTSimplify (expr::SMTExpr t)) = do
    mp <- readIORef (stpVars stp)
    expr' <- exprToSTP mp stp expr
    simpExpr <- stpSimplify (stpInstance stp) expr'
    stpToExpr (declaredDataTypes st) (namedVars st) (Just $ getSort (undefined::t) (extractAnnotation expr)) simpExpr $
      \res -> case cast res of
        Just res' -> res'
  smtHandle _ _ (SMTGetInterpolant _) = error $ "smtlib2-stp: STP doesn't support interpolation."
  smtHandle _ _ (SMTComment _) = return ()
  smtHandle stp _ SMTExit = stpDestroy (stpInstance stp)
    
sortToSTP :: STPBackend -> Sort -> IO STPType
sortToSTP stp (Fix BoolSort) = stpBoolType (stpInstance stp)
sortToSTP stp (Fix (BVSort { bvSortWidth = w }))
  = stpBVType (stpInstance stp) (fromIntegral w)
sortToSTP stp (Fix (ArraySort [i] v)) = do
  iTp <- sortToSTP stp i
  vTp <- sortToSTP stp v
  stpArrayType (stpInstance stp) iTp vTp
sortToSTP _ sort = error $ "smtlib2-stp: STP doesn't support type "++show sort++"."

exprToSTP :: SMTType a => Map Integer STPExpr -> STPBackend -> SMTExpr a -> IO STPExpr
exprToSTP mp stp (Var name ann) = case Map.lookup name mp of
  Just expr -> return expr
exprToSTP mp stp (Const c ann) = do
  let val = mangle c ann
  case val of
    BoolValue True -> stpTrueExpr (stpInstance stp)
    BoolValue False -> stpFalseExpr (stpInstance stp)
    BVValue { bvValueWidth = w
            , bvValueValue = v }
      -> stpBVConstFromDecStr (stpInstance stp) (fromIntegral w) (show v)
    _ -> error $ "smtlib2-stp: STP backend doesn't support value "++show val
exprToSTP mp stp (Let ann args f) = exprToSTP mp stp (f args)
exprToSTP mp stp (App SMTEq [x,y::SMTExpr t]) = do
  ndx <- exprToSTP mp stp x
  ndy <- exprToSTP mp stp y
  case getSort (undefined::t) (extractAnnotation y) of
    Fix BoolSort -> stpIffExpr (stpInstance stp) ndx ndy
    _ -> stpEqExpr (stpInstance stp) ndx ndy
exprToSTP mp stp (App SMTNot x) = do
  ndx <- exprToSTP mp stp x
  stpNotExpr (stpInstance stp) ndx
exprToSTP mp stp (App (SMTLogic And) xs) = do
  nds <- mapM (exprToSTP mp stp) xs
  stpAndExpr (stpInstance stp) nds
exprToSTP mp stp (App (SMTLogic Or) xs) = do
  nds <- mapM (exprToSTP mp stp) xs
  stpOrExpr (stpInstance stp) nds
exprToSTP mp stp (App (SMTLogic XOr) xs) = do
  n:ns <- mapM (exprToSTP mp stp) xs
  foldlM (stpXOrExpr (stpInstance stp)) n ns
exprToSTP mp stp (App (SMTLogic Implies) [x,y]) = do
  ndx <- exprToSTP mp stp x
  ndy <- exprToSTP mp stp y
  stpImpliesExpr (stpInstance stp) ndx ndy
exprToSTP mp stp (App SMTITE (c,ifT,ifF)) = do
  ndC <- exprToSTP mp stp c
  ndT <- exprToSTP mp stp ifT
  ndF <- exprToSTP mp stp ifF
  stpITEExpr (stpInstance stp) ndC ndT ndF
exprToSTP mp stp (App SMTSelect (arr,i)) = do
  ndArr <- exprToSTP mp stp arr
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToSTP mp stp arg,())) i (extractArgAnnotation i) ()
  [ndI] <- sequence argLst
  stpReadExpr (stpInstance stp) ndArr ndI
exprToSTP mp stp (App SMTStore (arr,i,v)) = do
  ndArr <- exprToSTP mp stp arr
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToSTP mp stp arg,())) i (extractArgAnnotation i) ()
  [ndI] <- sequence argLst
  ndV <- exprToSTP mp stp v
  stpWriteExpr (stpInstance stp) ndArr ndI ndV
exprToSTP mp stp (App SMTConcat (e1,e2)) = do
  nd1 <- exprToSTP mp stp e1
  nd2 <- exprToSTP mp stp e2
  stpBVConcatExpr (stpInstance stp) nd1 nd2
exprToSTP mp stp (App (SMTBVBin op) (e1::SMTExpr (BitVector t),e2)) = do
  let sort = getSort (undefined::BitVector t) (extractAnnotation e1)
      width = case sort of
        Fix (BVSort { bvSortWidth = w }) -> fromIntegral w
  nd1 <- exprToSTP mp stp e1
  nd2 <- exprToSTP mp stp e2
  (case op of
      BVAdd -> stpBVPlusExpr (stpInstance stp) width
      BVSub -> stpBVMinusExpr (stpInstance stp) width
      BVMul -> stpBVMultExpr (stpInstance stp) width
      BVUDiv -> stpBVDivExpr (stpInstance stp) width
      BVURem -> stpBVModExpr (stpInstance stp) width
      BVSDiv -> stpSBVDivExpr (stpInstance stp) width
      BVSRem -> stpSBVRemExpr (stpInstance stp) width
      BVSHL -> stpBVLeftShiftExpr (stpInstance stp) width
      BVLSHR -> stpBVRightShiftExpr (stpInstance stp) width
      BVASHR -> stpBVSignedRightShiftExpr (stpInstance stp) width
      BVAnd -> stpBVAndExpr (stpInstance stp)
      BVOr -> stpBVOrExpr (stpInstance stp)
      BVXor -> stpBVXorExpr (stpInstance stp)) nd1 nd2
exprToSTP mp stp (App (SMTBVComp op) (e1,e2)) = do
  nd1 <- exprToSTP mp stp e1
  nd2 <- exprToSTP mp stp e2
  (case op of
      BVULE -> stpBVLeExpr
      BVULT -> stpBVLtExpr
      BVUGE -> stpBVGeExpr
      BVUGT -> stpBVGtExpr
      BVSLE -> stpSBVLeExpr
      BVSLT -> stpSBVLtExpr
      BVSGE -> stpSBVGeExpr
      BVSGT -> stpSBVGtExpr) (stpInstance stp) nd1 nd2
exprToSTP mp stp (App (SMTBVUn op) e) = do
  nd <- exprToSTP mp stp e
  (case op of
      BVNot -> stpBVNotExpr
      BVNeg -> stpBVUMinusExpr) (stpInstance stp) nd
exprToSTP mp stp (App (SMTExtract prStart prLen) e) = do
  n <- exprToSTP mp stp e
  let start = reflectNat prStart 0
      len = reflectNat prLen 0
  stpBVExtract (stpInstance stp) n (fromIntegral $ start+len-1) (fromIntegral start)
exprToSTP _ _ expr = error $ "smtlib2-stp: STP backend doesn't support expression."

stpToExpr :: DataTypeInfo -> Map (String,Integer) Integer -> Maybe Sort -> STPExpr -> (forall t. SMTType t => SMTExpr t -> a) -> IO a
stpToExpr dts named expected expr f = do
  kind <- stpGetExprKind expr
  case kind of
    #{const SYMBOL} -> do
      name <- stpExprName expr
      sort <- stpExprSort expected expr
      withSort dts sort $
        \(_::t) ann -> case unescapeName name of
          Just (Left name) -> case Map.lookup name named of
            Just var -> return $ f (Var var ann :: SMTExpr t)
          Just (Right i) -> return $ f (Var i ann :: SMTExpr t)
    #{const BVCONST} -> do
      val <- stpGetBVUnsignedLongLong expr
      len <- stpGetBVLength expr
      let untyped = case expected of
            Just (Fix (BVSort { bvSortUntyped = unt }))
              -> unt
            _ -> False
      if untyped
        then return $ f (Const (BitVector $ fromIntegral val) (fromIntegral len)
                         :: SMTExpr (BitVector BVUntyped))
        else reifyNat len $
             \(_::Proxy n)
             -> return $ f (Const (BitVector $ fromIntegral val) ()
                         :: SMTExpr (BitVector (BVTyped n)))
    #{const TRUE} -> return $ f (Const True ())
    #{const FALSE} -> return $ f (Const False ())
    #{const BVNEG} -> do
      arg <- stpGetChild expr 0
      stpToExpr dts named expected arg $
        \arg' -> asBV arg' $
                 \arg'' -> f (App (SMTBVUn BVNeg) arg'')
    -- #{const BVCONCAT} -> do
    --  arg1 <- stpGetChild expr 0
    --  arg2 <- stpGetChild expr 1
    _ -> do
      repr <- stpExprString expr
      error $ "smtlib2-stp: Can't convert expression "++repr++" to haskell."
      
    
asBV :: SMTType t => SMTExpr t -> (forall bv. SMTType (BitVector bv) => SMTExpr (BitVector bv) -> a) -> a
asBV (expr::SMTExpr t) f = case getSort (undefined::t) (extractAnnotation expr) of
  Fix (BVSort { bvSortWidth = w
              , bvSortUntyped = unt })
    -> if unt
       then (case cast expr of
                Just expr' -> f (expr'::SMTExpr (BitVector BVUntyped)))
       else reifyNat w $ \(_::Proxy n) -> case cast expr of
         Just expr' -> f (expr'::SMTExpr (BitVector (BVTyped n)))

stpExprSort :: Maybe Sort -> STPExpr -> IO Sort
stpExprSort expected expr = do
  tp <- stpGetType' expr
  case tp of
    #{const BOOLEAN_TYPE} -> return $ Fix BoolSort
    #{const BITVECTOR_TYPE} -> do
      len <- stpGetBVLength expr
      return (Fix $ BVSort { bvSortWidth = fromIntegral len
                           , bvSortUntyped = case expected of
                             Just (Fix (BVSort { bvSortUntyped = unt })) -> unt
                             _ -> False
                           })
    #{const ARRAY_TYPE} -> do
      let (untI,untV) = case expected of
            Just (Fix (ArraySort [Fix (BVSort { bvSortUntyped = uI })] (Fix (BVSort { bvSortUntyped = uV }))))
              -> (uI,uV)
            _ -> (False,False)
      iw <- stpGetIWidth expr
      vw <- stpGetVWidth expr
      return (Fix $ ArraySort [Fix $ BVSort { bvSortWidth = fromIntegral iw
                                            , bvSortUntyped = untI }]
              (Fix $ BVSort { bvSortWidth = fromIntegral vw
                            , bvSortUntyped = untV }))
    _ -> error $ "smtlib2-stp: Unknown expression type: "++show tp
          
foreign import capi "stp/c_interface.h vc_createValidityChecker"
  stpCreateValidityChecker :: IO VC

foreign import capi "stp/c_interface.h vc_boolType"
  stpBoolType :: VC -> IO STPType

foreign import capi "stp/c_interface.h vc_arrayType"
  stpArrayType :: VC -> STPType -> STPType -> IO STPType

stpVarExpr :: VC -> String -> STPType -> IO STPExpr
stpVarExpr vc name tp
  = withCString name $
    \name' -> stpVarExpr_ vc name' tp

foreign import capi "stp/c_interface.h vc_varExpr"
  stpVarExpr_ :: VC -> CString -> STPType -> IO STPExpr

foreign import capi "stp/c_interface.h vc_getType"
  stpGetType :: VC -> STPExpr -> IO STPType

foreign import capi "stp/c_interface.h vc_eqExpr"
  stpEqExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_trueExpr"
  stpTrueExpr :: VC -> IO STPExpr

foreign import capi "stp/c_interface.h vc_falseExpr"
  stpFalseExpr :: VC -> IO STPExpr

foreign import capi "stp/c_interface.h vc_notExpr"
  stpNotExpr :: VC -> STPExpr -> IO STPExpr

stpAndExpr :: VC -> [STPExpr] -> IO STPExpr
stpAndExpr vc exprs
  = withArrayLen exprs $
    \len arr -> stpAndExpr_ vc arr (fromIntegral len)

foreign import capi "stp/c_interface.h vc_andExprN"
  stpAndExpr_ :: VC -> Ptr STPExpr -> CInt -> IO STPExpr

stpOrExpr :: VC -> [STPExpr] -> IO STPExpr
stpOrExpr vc exprs
  = withArrayLen exprs $
    \len arr -> stpOrExpr_ vc arr (fromIntegral len)

foreign import capi "stp/c_interface.h vc_orExprN"
  stpOrExpr_ :: VC -> Ptr STPExpr -> CInt -> IO STPExpr

foreign import capi "stp/c_interface.h vc_xorExpr"
  stpXOrExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_impliesExpr"
  stpImpliesExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_iffExpr"
  stpIffExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_iteExpr"
  stpITEExpr :: VC -> STPExpr -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_boolToBVExpr"
  stpBoolToBVExpr :: VC -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_readExpr"
  stpReadExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_writeExpr"
  stpWriteExpr :: VC -> STPExpr -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_assertFormula"
  stpAssert :: VC -> STPExpr -> IO ()

foreign import capi "stp/c_interface.h vc_simplify"
  stpSimplify :: VC -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_query"
  stpQuery :: VC -> STPExpr -> IO CInt

foreign import capi "stp/c_interface.h vc_getCounterExample"
  stpGetCounterExample :: VC -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_push"
  stpPush :: VC -> IO ()

foreign import capi "stp/c_interface.h vc_pop"
  stpPop :: VC -> IO ()

foreign import capi "stp/c_interface.h getBVInt"
  stpGetBVInt :: STPExpr -> IO CInt

foreign import capi "stp/c_interface.h getBVUnsigned"
  stpGetBVUnsigned :: STPExpr -> IO CUInt

foreign import capi "stp/c_interface.h getBVUnsignedLongLong"
  stpGetBVUnsignedLongLong :: STPExpr -> IO CULLong

foreign import capi "stp/c_interface.h vc_bvType"
  stpBVType :: VC -> CInt -> IO STPType

stpBVConstFromDecStr :: VC -> CInt -> String -> IO STPExpr
stpBVConstFromDecStr vc w str
  = withCString str $
    \str' -> stpBVConstFromDecStr_ vc w str'

foreign import capi "stp/c_interface.h vc_bvConstExprFromDecStr"
  stpBVConstFromDecStr_ :: VC -> CInt -> CString -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvConcatExpr"
  stpBVConcatExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvPlusExpr"
  stpBVPlusExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

stpBVPlusExprN :: VC -> CInt -> [STPExpr] -> IO STPExpr
stpBVPlusExprN vc w exprs
  = withArrayLen exprs $
    \len arr -> stpBVPlusExprN_ vc w arr (fromIntegral len)

foreign import capi "stp/c_interface.h vc_bvPlusExprN"
  stpBVPlusExprN_ :: VC -> CInt -> Ptr STPExpr -> CInt -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvMinusExpr"
  stpBVMinusExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvMultExpr"
  stpBVMultExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvDivExpr"
  stpBVDivExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvModExpr"
  stpBVModExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_sbvDivExpr"
  stpSBVDivExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_sbvModExpr"
  stpSBVModExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_sbvRemExpr"
  stpSBVRemExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvLtExpr"
  stpBVLtExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvLeExpr"
  stpBVLeExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvGtExpr"
  stpBVGtExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvGeExpr"
  stpBVGeExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_sbvLtExpr"
  stpSBVLtExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_sbvLeExpr"
  stpSBVLeExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_sbvGtExpr"
  stpSBVGtExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_sbvGeExpr"
  stpSBVGeExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvUMinusExpr"
  stpBVUMinusExpr :: VC -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvAndExpr"
  stpBVAndExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvOrExpr"
  stpBVOrExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvXorExpr"
  stpBVXorExpr :: VC -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvNotExpr"
  stpBVNotExpr :: VC -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvLeftShiftExprExpr"
  stpBVLeftShiftExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvRightShiftExprExpr"
  stpBVRightShiftExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvSignedRightShiftExprExpr"
  stpBVSignedRightShiftExpr :: VC -> CInt -> STPExpr -> STPExpr -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvExtract"
  stpBVExtract :: VC -> STPExpr -> CInt -> CInt -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvBoolExtract_Zero"
  stpBVBoolExtractZero :: VC -> STPExpr -> CInt -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvBoolExtract_One"
  stpBVBoolExtractOne :: VC -> STPExpr -> CInt -> IO STPExpr

foreign import capi "stp/c_interface.h vc_bvSignExtend"
  stpBVSignExtend :: VC -> STPExpr -> CInt -> IO STPExpr

stpExprString :: STPExpr -> IO String
stpExprString expr = do
  cstr <- stpExprString_ expr
  str <- peekCString cstr
  free cstr
  return str
  
foreign import capi "stp/c_interface.h exprString"
  stpExprString_ :: STPExpr -> IO CString

foreign import capi "stp/c_interface.h getChild"
  stpGetChild :: STPExpr -> CInt -> IO STPExpr

stpTypeString :: STPType -> IO String
stpTypeString tp = do
  str <- stpTypeString_ tp
  hstr <- peekCString str
  free str
  return hstr

foreign import capi "stp/c_interface.h typeString"
  stpTypeString_ :: STPType -> IO CString

stpIsBool :: STPExpr -> IO Bool
stpIsBool expr = do
  res <- stpIsBool_ expr
  return (res==1)

foreign import capi "stp/c_interface.h vc_isBool"
  stpIsBool_ :: STPExpr -> IO CInt

foreign import capi "stp/c_interface.h vc_Destroy"
  stpDestroy :: VC -> IO ()

foreign import capi "stp/c_interface.h vc_DeleteExpr"
  stpDeleteExpr :: STPExpr -> IO ()

foreign import capi "stp/c_interface.h getDegree"
  stpGetDegree :: STPExpr -> IO CInt

foreign import capi "stp/c_interface.h getExprKind"
  stpGetExprKind :: STPExpr -> IO CInt

foreign import capi "stp/c_interface.h getBVLength"
  stpGetBVLength :: STPExpr -> IO CInt

foreign import capi "stp/c_interface.h getVWidth"
  stpGetVWidth :: STPExpr -> IO CInt

foreign import capi "stp/c_interface.h getIWidth"
  stpGetIWidth :: STPExpr -> IO CInt

stpExprName :: STPExpr -> IO String
stpExprName expr = do
  str <- stpExprName_ expr
  peekCString str

foreign import capi "stp/c_interface.h exprName"
  stpExprName_ :: STPExpr -> IO CString

foreign import capi "stp/c_interface.h getType"
  stpGetType' :: STPExpr -> IO CInt
