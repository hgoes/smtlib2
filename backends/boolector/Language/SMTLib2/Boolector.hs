module Language.SMTLib2.Boolector (BoolectorBackend(),boolectorBackend,withBoolector) where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators

import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Fix
import Data.Bits
import Data.Typeable
import Data.Proxy
import Data.Foldable (foldlM)

import Foreign.Ptr
import Foreign.C
import Foreign.Marshal
import Foreign.Storable

data BoolectorBackend = BoolectorBackend { boolectorInstance :: Btor
                                         , boolectorVars :: IORef (Map Integer BtorNode)
                                         , boolectorAssumeState :: IORef Bool
                                         }

withBoolector :: SMT' IO a -> IO a
withBoolector act = do
  b <- boolectorBackend
  withSMTBackend b act

boolectorBackend :: IO BoolectorBackend
boolectorBackend = do
  btor <- boolectorNew
  boolectorEnableIncUsage btor
  vars <- newIORef Map.empty
  assumeState <- newIORef False
  return $ BoolectorBackend { boolectorInstance = btor
                            , boolectorVars = vars
                            , boolectorAssumeState = assumeState }

instance SMTBackend BoolectorBackend IO where
  smtHandle _ _ (SMTSetLogic _) = return ()
  smtHandle _ _ (SMTGetInfo SMTSolverName) = return "boolector"
  smtHandle _ _ (SMTGetInfo SMTSolverVersion) = return "unknown"
  smtHandle btor _ (SMTSetOption (ProduceModels True)) = boolectorEnableModelGen (boolectorInstance btor)
  smtHandle _ _ (SMTSetOption _) = return ()
  smtHandle btor _ (SMTDeclareFun name) = do
    case funInfoArgSorts name of
      [] -> return ()
      _ -> error "smtlib2-boolector: No support for uninterpreted functions."
    mkVar btor name (funInfoSort name)
    return ()
  smtHandle btor _ (SMTAssert expr Nothing) = do
    isAssume <- readIORef (boolectorAssumeState btor)
    mp <- readIORef (boolectorVars btor)
    nd <- exprToNode mp btor expr
    if isAssume
      then boolectorAssume (boolectorInstance btor) nd
      else boolectorAssert (boolectorInstance btor) nd
  smtHandle btor _ (SMTCheckSat _) = boolectorSat (boolectorInstance btor)
  smtHandle _ _ (SMTDeclareDataTypes _) = error "smtlib2-boolector: No support for data-types."
  smtHandle _ _ (SMTDeclareSort _ _) = error "smtlib2-boolector: No support for sorts."
  smtHandle btor _ SMTPush = do
    isAssume <- readIORef (boolectorAssumeState btor)
    if isAssume
      then error $ "smtlib2-boolector: Only one stack level is supported"
      else return ()
    writeIORef (boolectorAssumeState btor) True
  smtHandle btor _ SMTPop = writeIORef (boolectorAssumeState btor) False
  smtHandle btor _ (SMTDefineFun name [] expr) = do
    mp <- readIORef (boolectorVars btor)
    nd <- exprToNode mp btor expr
    modifyIORef (boolectorVars btor) (Map.insert (funInfoId name) nd)
  smtHandle btor _ (SMTDefineFun name args expr) = do
    params <- mapM (\info -> do
                       let w = case funInfoSort info of
                             Fix BoolSort -> 1
                             Fix (BVSort { bvSortWidth = w' }) -> w'
                             sort -> error $ "smtlib2-boolector: Parameter type "++show sort++" not supported."
                       res <- boolectorParam (boolectorInstance btor) (fromIntegral w)
                              (escapeName $ case funInfoName info of
                                  Nothing -> Right $ funInfoId info
                                  Just name' -> Left name')
                       return (funInfoId info,res)
                   ) args
    mp <- readIORef (boolectorVars btor)
    nd <- exprToNode (Map.union mp (Map.fromList params)) btor expr
    fun <- boolectorFun (boolectorInstance btor) (fmap snd params) nd
    modifyIORef (boolectorVars btor) (Map.insert (funInfoId name) fun)
  smtHandle btor st (SMTGetValue (expr :: SMTExpr t)) = do
    mp <- readIORef (boolectorVars btor)
    nd <- exprToNode mp btor expr
    let sort = getSort (undefined::t) (extractAnnotation expr)
    case sort of
      Fix (BVSort { bvSortWidth = w
                  , bvSortUntyped = unt }) -> do
        assign <- boolectorBVAssignment (boolectorInstance btor) nd
        let res = foldl
                  (\cval n -> (shiftL cval 1) +
                              (case n of
                                  One -> 1
                                  Zero -> 0
                                  DontCare -> 0)) 0 assign
        if unt
          then (case cast (BitVector res :: BitVector BVUntyped) of
                   Just r -> return r)
          else (reifyNat w (\(_::Proxy bw) -> case cast (BitVector res :: BitVector (BVTyped bw)) of
                               Just r -> return r))
      Fix BoolSort -> do
        [assign] <- boolectorBVAssignment (boolectorInstance btor) nd
        let res = case assign of
              One -> True
              Zero -> False
              DontCare -> False
        case cast res of
          Just r -> return r
      _ -> error $ "smtlib2-boolector: Getting values of sort "++show sort++" not supported."
  smtHandle _ _ SMTGetProof = error "smtlib2-boolector: Proof extraction not supported."
  smtHandle _ _ SMTGetUnsatCore = error "smtlib2-boolector: Unsat core extraction not supported."
  smtHandle _ _ (SMTSimplify expr) = return expr
  smtHandle _ _ (SMTGetInterpolant _) = error "smtlib2-boolector: Interpolant extraction not supported."
  smtHandle _ _ (SMTComment _) = return ()
  smtHandle btor _ SMTExit = boolectorDelete (boolectorInstance btor)
  
exprToNode :: SMTType a => Map Integer BtorNode -> BoolectorBackend -> SMTExpr a -> IO BtorNode
exprToNode mp btor (Var name ann) = do
  case Map.lookup name mp of
    Just nd -> return nd
exprToNode _ btor (Const c ann) = do
  let val = mangle c ann
  case val of
    BoolValue True -> boolectorTrue (boolectorInstance btor)
    BoolValue False -> boolectorFalse (boolectorInstance btor)
    BVValue { bvValueWidth = w
            , bvValueValue = v }
      -> if v < 0
         then boolectorInt (boolectorInstance btor) (fromIntegral v) (fromIntegral w)
         else boolectorUnsignedInt (boolectorInstance btor) (fromIntegral v) (fromIntegral w)
    _ -> error $ "smtlib2-boolector: Boolector backend doesn't support value "++show val
exprToNode mp btor (Let ann args f) = exprToNode mp btor (f args)
exprToNode mp btor (App SMTEq [x,y]) = do
  ndx <- exprToNode mp btor x
  ndy <- exprToNode mp btor y
  boolectorEq (boolectorInstance btor) ndx ndy
exprToNode mp btor (App (SMTFun fun _) args) = do
  funNd <- case Map.lookup fun mp of
    Just nd -> return nd
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToNode mp btor arg,())) args (extractArgAnnotation args) ()
  argNds <- sequence argLst
  boolectorApply (boolectorInstance btor) argNds funNd
exprToNode mp btor (App (SMTLogic op) args) = do
  nd:nds <- mapM (exprToNode mp btor) args
  let rop = case op of
        And -> boolectorAnd
        Or -> boolectorOr
        XOr -> boolectorXOr
        Implies -> boolectorImplies
  foldlM (rop (boolectorInstance btor)) nd nds
exprToNode mp btor (App SMTNot e) = do
  nd <- exprToNode mp btor e
  boolectorNot (boolectorInstance btor) nd
exprToNode mp btor (App SMTDistinct [x,y]) = do
  ndx <- exprToNode mp btor x
  ndy <- exprToNode mp btor y
  res <- boolectorEq (boolectorInstance btor) ndx ndy
  boolectorNot (boolectorInstance btor) res
exprToNode mp btor (App SMTITE (c,ifT,ifF)) = do
  ndC <- exprToNode mp btor c
  ndIfT <- exprToNode mp btor ifT
  ndIfF <- exprToNode mp btor ifF
  boolectorCond (boolectorInstance btor) ndC ndIfT ndIfF
exprToNode mp btor (App (SMTBVComp op) (e1,e2)) = do
  n1 <- exprToNode mp btor e1
  n2 <- exprToNode mp btor e2
  (case op of
      BVULE -> boolectorULte 
      BVULT -> boolectorULt
      BVUGE -> boolectorUGte
      BVUGT -> boolectorUGt
      BVSLE -> boolectorSLte
      BVSLT -> boolectorSLt
      BVSGE -> boolectorSGte
      BVSGT -> boolectorSGt
    ) (boolectorInstance btor) n1 n2
exprToNode mp btor (App (SMTBVBin op) (e1::SMTExpr (BitVector a),e2)) = do
  n1 <- exprToNode mp btor e1
  n2 <- exprToNode mp btor e2
  n2' <- if (case op of
                BVSHL -> True
                BVLSHR -> True
                BVASHR -> True
                _ -> False)
         then (do
                  let bw1 = getBVSize (Proxy::Proxy a) (extractAnnotation e1)
                      bw2 = getBVSize (Proxy::Proxy a) (extractAnnotation e2)
                      tw = ceiling $ logBase 2 (fromInteger bw1)
                  case compare bw2 tw of
                    EQ -> return n2
                    GT -> boolectorSlice (boolectorInstance btor) n2 (fromIntegral $ tw-1) 0)
         else return n2
  (case op of
      BVAdd -> boolectorAdd
      BVSub -> boolectorSub
      BVMul -> boolectorMul
      BVURem -> boolectorURem
      BVSRem -> boolectorSRem
      BVUDiv -> boolectorUDiv
      BVSDiv -> boolectorSDiv
      BVSHL -> boolectorSLL
      BVLSHR -> boolectorSRL
      BVASHR -> boolectorSRA
      BVXor -> boolectorXOr
      BVAnd -> boolectorAnd
      BVOr -> boolectorOr) (boolectorInstance btor) n1 n2'
exprToNode mp btor (App (SMTBVUn op) e) = do
  n <- exprToNode mp btor e
  (case op of
      BVNot -> boolectorNot
      BVNeg -> boolectorNeg) (boolectorInstance btor) n
exprToNode mp btor (App SMTSelect (arr,i)) = do
  ndArr <- exprToNode mp btor arr
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToNode mp btor arg,())) i (extractArgAnnotation i) ()
  [ndI] <- sequence argLst
  boolectorRead (boolectorInstance btor) ndArr ndI
exprToNode mp btor (App SMTStore (arr,i,v)) = do
  ndArr <- exprToNode mp btor arr
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToNode mp btor arg,())) i (extractArgAnnotation i) ()
  [ndI] <- sequence argLst
  ndV <- exprToNode mp btor v
  boolectorWrite (boolectorInstance btor) ndArr ndI ndV
exprToNode mp btor (App SMTConcat (e1,e2)) = do
  n1 <- exprToNode mp btor e1
  n2 <- exprToNode mp btor e2
  boolectorConcat (boolectorInstance btor) n1 n2
exprToNode mp btor (App (SMTExtract prStart prLen) e) = do
  n <- exprToNode mp btor e
  let start = reflectNat prStart 0
      len = reflectNat prLen 0
  boolectorSlice (boolectorInstance btor) n (fromIntegral $ start+len-1) (fromIntegral start)
exprToNode _ _ e = error $ "smtlib2-boolector: No support for expression."

mkVar :: BoolectorBackend -> FunInfo -> Sort -> IO BtorNode
mkVar btor info sort = do
  let name = escapeName $ case funInfoName info of
        Nothing -> Right $ funInfoId info
        Just name' -> Left name'
  nd <- case sort of
    Fix BoolSort -> boolectorVar (boolectorInstance btor) 1 name
    Fix (BVSort { bvSortWidth = w }) -> boolectorVar (boolectorInstance btor) (fromIntegral w) name
    Fix (ArraySort [Fix (BVSort { bvSortWidth = idx_w })] (Fix (BVSort { bvSortWidth = el_w })))
      -> boolectorArray (boolectorInstance btor) (fromIntegral el_w) (fromIntegral idx_w) name
    _ -> error $ "smtlib2-boolector: Boolector backend doesn't support sort "++show sort
  modifyIORef (boolectorVars btor) (Map.insert (funInfoId info) nd)
  return nd

newtype BtorNode = BtorNode (Ptr BtorNode) deriving (Storable)
newtype BtorSort = BtorSort (Ptr BtorSort) deriving (Storable)
newtype Btor = Btor (Ptr Btor) deriving (Storable)

foreign import capi "boolector.h boolector_new"
  boolectorNew :: IO Btor

foreign import capi "boolector.h boolector_clone"
  boolectorClone :: Btor -> IO Btor

foreign import capi "boolector.h boolector_enable_model_gen"
  boolectorEnableModelGen :: Btor -> IO ()

foreign import capi "boolector.h boolector_generate_model_for_all_reads"
  boolectorEnableModelForAllReads :: Btor -> IO ()

foreign import capi "boolector.h boolector_enable_inc_usage"
  boolectorEnableIncUsage :: Btor -> IO ()

boolectorSetSatSolver :: Btor -> String -> IO ()
boolectorSetSatSolver btor name
  = withCString name (\name' -> boolectorSetSatSolver_ btor name')

foreign import capi "boolector.h boolector_set_sat_solver"
  boolectorSetSatSolver_ :: Btor -> CString -> IO ()

foreign import capi "boolector.h boolector_set_rewrite_level"
  boolectorSetRewriteLevel :: Btor -> CInt -> IO ()

foreign import capi "boolector.h boolector_get_refs"
  boolectorGetRefs :: Btor -> IO CInt

foreign import capi "boolector.h boolector_delete"
  boolectorDelete :: Btor -> IO ()

foreign import capi "boolector.h boolector_const"
  boolectorConst :: Btor -> CString -> IO BtorNode

foreign import capi "boolector.h boolector_zero"
  boolectorZero :: Btor -> CInt -> IO BtorNode

foreign import capi "boolector.h boolector_false"
  boolectorFalse :: Btor -> IO BtorNode

foreign import capi "boolector.h boolector_ones"
  boolectorOnes :: Btor -> CInt -> IO BtorNode

foreign import capi "boolector.h boolector_true"
  boolectorTrue :: Btor -> IO BtorNode

foreign import capi "boolector.h boolector_one"
  boolectorOne :: Btor -> CInt -> IO BtorNode

foreign import capi "boolector.h boolector_unsigned_int"
  boolectorUnsignedInt :: Btor -> CUInt -> CInt -> IO BtorNode

foreign import capi "boolector.h boolector_int"
  boolectorInt :: Btor -> CInt -> CInt -> IO BtorNode

boolectorVar :: Btor -> CInt -> String -> IO BtorNode
boolectorVar btor w name
  = withCString name $
    \name' -> boolectorVar_ btor w name'

foreign import capi "boolector.h boolector_var"
  boolectorVar_ :: Btor -> CInt -> CString -> IO BtorNode

boolectorArray :: Btor -> CInt -> CInt -> String -> IO BtorNode
boolectorArray btor wi we name
  = withCString name $
    \name' -> boolectorArray_ btor wi we name'

foreign import capi "boolector.h boolector_array"
  boolectorArray_ :: Btor -> CInt -> CInt -> CString -> IO BtorNode

foreign import capi "boolector.h boolector_not"
  boolectorNot :: Btor -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_neg"
  boolectorNeg :: Btor -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_redor"
  boolectorRedOr :: Btor -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_redand"
  boolectorRedAnd :: Btor -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_slice"
  boolectorSlice :: Btor -> BtorNode -> CInt -> CInt -> IO BtorNode

foreign import capi "boolector.h boolector_uext"
  boolectorUExt :: Btor -> BtorNode -> CInt -> IO BtorNode

foreign import capi "boolector.h boolector_sext"
  boolectorSExt :: Btor -> BtorNode -> CInt -> IO BtorNode

foreign import capi "boolector.h boolector_implies"
  boolectorImplies :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_iff"
  boolectorIff :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_xor"
  boolectorXOr :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_xnor"
  boolectorXNOr :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_and"
  boolectorAnd :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_nand"
  boolectorNAnd :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_or"
  boolectorOr :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_nor"
  boolectorNOr :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_eq"
  boolectorEq :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_ne"
  boolectorNE :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_add"
  boolectorAdd :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_uaddo"
  boolectorUAddO :: Btor -> BtorNode -> BtorNode -> IO BtorNode
                  
foreign import capi "boolector.h boolector_saddo"
  boolectorSAddO :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_mul"
  boolectorMul :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_umulo"
  boolectorUMulO :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_smulo"
  boolectorSMulO :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_ult"
  boolectorULt :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_slt"
  boolectorSLt :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_ulte"
  boolectorULte :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_slte"
  boolectorSLte :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_ugt"
  boolectorUGt :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_sgt"
  boolectorSGt :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_ugte"
  boolectorUGte :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_sgte"
  boolectorSGte :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_sll"
  boolectorSLL :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_srl"
  boolectorSRL :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_sra"
  boolectorSRA :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_rol"
  boolectorRoL :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_ror"
  boolectorRoR :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_sub"
  boolectorSub :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_usubo"
  boolectorUSubO :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_ssubo"
  boolectorSSubO :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_udiv"
  boolectorUDiv :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_sdiv"
  boolectorSDiv :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_sdivo"
  boolectorSDivO :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_urem"
  boolectorURem :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_srem"
  boolectorSRem :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_smod"
  boolectorSMod :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_concat"
  boolectorConcat :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_read"
  boolectorRead :: Btor -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_write"
  boolectorWrite :: Btor -> BtorNode -> BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_cond"
  boolectorCond :: Btor -> BtorNode -> BtorNode -> BtorNode -> IO BtorNode

boolectorParam :: Btor -> CInt -> String -> IO BtorNode
boolectorParam btor width name
  = withCString name $
    \name' -> boolectorParam_ btor width name'

foreign import capi "boolector.h boolector_param"
  boolectorParam_ :: Btor -> CInt -> CString -> IO BtorNode

boolectorFun :: Btor -> [BtorNode] -> BtorNode -> IO BtorNode
boolectorFun btor args expr
  = withArrayLen args $
    \len arr -> boolectorFun_ btor (fromIntegral len) arr expr

foreign import capi "boolector.h boolector_fun"
  boolectorFun_ :: Btor -> CInt -> Ptr BtorNode -> BtorNode -> IO BtorNode

boolectorApply :: Btor -> [BtorNode] -> BtorNode -> IO BtorNode
boolectorApply btor args fun
  = withArrayLen args $
    \len arr -> boolectorApply_ btor (fromIntegral len) arr fun

foreign import capi "boolector.h boolector_apply"
  boolectorApply_ :: Btor -> CInt -> Ptr BtorNode -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_inc"
  boolectorInc :: Btor -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_dec"
  boolectorDec :: Btor -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_is_array"
  boolectorIsArray :: Btor -> BtorNode -> IO Bool

foreign import capi "boolector.h boolector_is_fun"
  boolectorIsFun :: Btor -> BtorNode -> IO Bool

foreign import capi "boolector.h boolector_get_fun_arity"
  boolectorGetFunArity :: Btor -> BtorNode -> IO CInt

foreign import capi "boolector.h boolector_get_width"
  boolectorGetWidth :: Btor -> BtorNode -> IO CInt

foreign import capi "boolector.h boolector_get_index_width"
  boolectorGetIndexWidth :: Btor -> BtorNode -> IO CInt

boolectorFunSortCheck :: Btor -> [BtorNode] -> BtorNode -> IO Bool
boolectorFunSortCheck btor args fun
  = withArrayLen args $
    \len arr -> boolectorFunSortCheck_ btor (fromIntegral len) arr fun

foreign import capi "boolector.h boolector_fun_sort_check"
  boolectorFunSortCheck_ :: Btor -> CInt -> Ptr BtorNode -> BtorNode -> IO Bool

boolectorGetSymbolOfVar :: Btor -> BtorNode -> IO String
boolectorGetSymbolOfVar btor node = do
  res <- boolectorGetSymbolOfVar_ btor node
  peekCString res

foreign import capi "boolector.h boolector_get_symbol_of_var"
  boolectorGetSymbolOfVar_ :: Btor -> BtorNode -> IO CString

foreign import capi "boolector.h boolector_copy"
  boolectorCopy :: Btor -> BtorNode -> IO BtorNode

foreign import capi "boolector.h boolector_release"
  boolectorRelease :: Btor -> BtorNode -> IO ()

foreign import capi "boolector.h boolector_assert"
  boolectorAssert :: Btor -> BtorNode -> IO ()

foreign import capi "boolector.h boolector_assume"
  boolectorAssume :: Btor -> BtorNode -> IO ()

boolectorSat :: Btor -> IO Bool
boolectorSat btor = do
  res <- boolectorSat_ btor
  return $ res==10

foreign import capi "boolector.h boolector_sat"
  boolectorSat_ :: Btor -> IO CInt

data BitAssignment = One
                   | Zero
                   | DontCare
                   deriving (Eq,Ord,Show)

boolectorBVAssignment :: Btor -> BtorNode -> IO [BitAssignment]
boolectorBVAssignment btor node = do
  assignment <- boolectorBVAssignment_ btor node
  strAssignment <- peekCString assignment
  boolectorFreeBVAssignment_ btor assignment
  return $ fmap (\c -> case c of
                    '0' -> Zero
                    '1' -> One
                    'x' -> DontCare) strAssignment

foreign import capi "boolector.h boolector_bv_assignment"
  boolectorBVAssignment_ :: Btor -> BtorNode -> IO CString

foreign import capi "boolector.h boolector_free_bv_assignment"
  boolectorFreeBVAssignment_ :: Btor -> CString -> IO ()
