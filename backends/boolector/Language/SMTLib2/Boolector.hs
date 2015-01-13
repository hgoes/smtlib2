module Language.SMTLib2.Boolector (BoolectorBackend(),boolectorBackend,withBoolector) where

import Language.SMTLib2
import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Operators

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Fix
import Data.Bits
import Data.Typeable
import Data.Proxy
import Data.Foldable (foldlM)
import Data.List (genericIndex)

import Foreign.Ptr
import Foreign.C
import Foreign.Marshal
import Foreign.Storable

data BoolectorBackend = BoolectorBackend { boolectorInstance :: Btor
                                         , boolectorNextVar :: Integer
                                         , boolectorNameCount :: Map String Integer
                                         , boolectorVars :: Map Integer (BtorNode,String)
                                         , boolectorAssumeState :: Bool
                                         }

withBoolector :: SMT' IO a -> IO a
withBoolector act = do
  b <- boolectorBackend
  withSMTBackend b act

boolectorBackend :: IO BoolectorBackend
boolectorBackend = do
  btor <- boolectorNew
  return $ BoolectorBackend { boolectorInstance = btor
                            , boolectorNextVar = 0
                            , boolectorNameCount = Map.empty
                            , boolectorVars = Map.empty
                            , boolectorAssumeState = False }

instance SMTBackend BoolectorBackend IO where
  smtGetNames btor = return $ \i -> case Map.lookup i (boolectorVars btor) of
                                     Just (_,name) -> name
  smtNextName btor = return $ \name -> case name of
                                        Nothing -> escapeName (Right $ boolectorNextVar btor)
                                        Just name' -> escapeName $ Left
                                                      (name',
                                                       Map.findWithDefault 0 name'
                                                       (boolectorNameCount btor))
  smtHandle btor (SMTSetLogic _) = return ((),btor)
  smtHandle btor (SMTGetInfo SMTSolverName) = return ("boolector",btor)
  smtHandle btor (SMTGetInfo SMTSolverVersion) = return ("unknown",btor)
  smtHandle btor (SMTSetOption (ProduceModels True)) = do
    boolectorEnableModelGen (boolectorInstance btor)
    return ((),btor)
  smtHandle btor (SMTSetOption _) = return ((),btor)
  smtHandle btor SMTDeclaredDataTypes = return (emptyDataTypeInfo,btor)
  smtHandle btor (SMTDeclareFun name) = do
    case funInfoArgSorts name of
      [] -> return ()
      _ -> error "smtlib2-boolector: No support for uninterpreted functions."
    mkVar btor name (funInfoSort name)
  smtHandle btor (SMTAssert expr Nothing Nothing) = do
    nd <- exprToNode [] Map.empty btor expr
    if boolectorAssumeState btor
      then boolectorAssume (boolectorInstance btor) nd
      else boolectorAssert (boolectorInstance btor) nd
    return ((),btor)
  smtHandle btor (SMTCheckSat _ _) = do
    res <- boolectorSat (boolectorInstance btor)
    return (if res
            then Sat
            else Unsat,btor)
  smtHandle _ (SMTDeclareDataTypes _) = error "smtlib2-boolector: No support for data-types."
  smtHandle _ (SMTDeclareSort _ _) = error "smtlib2-boolector: No support for sorts."
  smtHandle btor SMTPush
    = if boolectorAssumeState btor
      then error $ "smtlib2-boolector: Only one stack level is supported"
      else return ((),btor { boolectorAssumeState = True })
  smtHandle btor SMTPop = return ((),btor { boolectorAssumeState = False })
  smtHandle btor (SMTDefineFun name (_::Proxy arg) ann expr) = do
    nd <- case getTypes (undefined::arg) ann of
      [] -> exprToNode [] Map.empty btor expr
      argTps -> do
        params <- mapM (\(ProxyArg u ann,i) -> do
                           let w = case getSort u ann of
                                 Fix BoolSort -> 1
                                 Fix (BVSort { bvSortWidth = w' }) -> w'
                                 sort -> error $ "smtlib2-boolector: Parameter type "++show sort++" not supported."
                           res <- boolectorParam (boolectorInstance btor) (fromIntegral w)
                                  ("farg_"++show i)
                           return res
                       ) (zip argTps [0..])
        nd <- exprToNode params Map.empty btor expr
        boolectorFun (boolectorInstance btor) params nd
    return (vid,btor { boolectorNextVar = vid+1
                     , boolectorNameCount = ncs
                     , boolectorVars = Map.insert vid (nd,rname)
                                       (boolectorVars btor) })
    where
      vid = boolectorNextVar btor
      (rname,ncs) = case name of
        Nothing -> (escapeName (Right vid),boolectorNameCount btor)
        Just name' -> let (nc,ncs) = case Map.insertLookupWithKey (const (+)) name' 1
                                          (boolectorNameCount btor) of
                                      (Just nc,ncs) -> (nc,ncs)
                                      (Nothing,ncs) -> (0,ncs)
                      in (escapeName (Left (name',nc)),ncs)
  smtHandle btor (SMTGetValue (expr :: SMTExpr t)) = do
    nd <- exprToNode [] Map.empty btor expr
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
                   Just r -> return (r,btor))
          else (reifyNat w (\(_::Proxy bw) -> case cast (BitVector res :: BitVector (BVTyped bw)) of
                               Just r -> return (r,btor)))
      Fix BoolSort -> do
        [assign] <- boolectorBVAssignment (boolectorInstance btor) nd
        let res = case assign of
              One -> True
              Zero -> False
              DontCare -> False
        case cast res of
          Just r -> return (r,btor)
      _ -> error $ "smtlib2-boolector: Getting values of sort "++show sort++" not supported."
  smtHandle _ SMTGetProof = error "smtlib2-boolector: Proof extraction not supported."
  smtHandle _ SMTGetUnsatCore = error "smtlib2-boolector: Unsat core extraction not supported."
  smtHandle btor (SMTSimplify expr) = return (expr,btor)
  smtHandle _ (SMTGetInterpolant _) = error "smtlib2-boolector: Interpolant extraction not supported."
  smtHandle btor (SMTComment _) = return ((),btor)
  smtHandle btor SMTExit = do
    boolectorDelete (boolectorInstance btor)
    return ((),btor)
  
exprToNode :: SMTType a => [BtorNode] -> Map Integer (Map Integer BtorNode) -> BoolectorBackend
           -> SMTExpr a -> IO BtorNode
exprToNode _ _ btor (Var name ann) = do
  case Map.lookup name (boolectorVars btor) of
    Just (nd,_) -> return nd
exprToNode _ qmp btor (QVar p q ann) = case Map.lookup p qmp of
  Just mp' -> case Map.lookup q mp' of
    Just nd -> return nd
exprToNode args _ _ (FunArg i _) = return $ args `genericIndex` i
exprToNode _ _ btor e@(Const c ann) = do
  case mangle of
   PrimitiveMangling f -> do
     let val = f c ann
     case val of
      BoolValue True -> boolectorTrue (boolectorInstance btor)
      BoolValue False -> boolectorFalse (boolectorInstance btor)
      BVValue { bvValueWidth = w
              , bvValueValue = v }
        -> if v < 0
           then boolectorInt (boolectorInstance btor) (fromIntegral v) (fromIntegral w)
           else boolectorUnsignedInt (boolectorInstance btor) (fromIntegral v) (fromIntegral w)
      _ -> error $ "smtlib2-boolector: Boolector backend doesn't support value "++show val
   _ -> error $ "smtlib2-boolector: Boolector backend doesn't support constant "++show e
exprToNode args qmp btor (Let lvl defs body) = do
  nqmp <- foldlM (\cmp (i,expr) -> do
                     nd <- exprToNode args cmp btor expr
                     return $ Map.insertWith Map.union lvl (Map.singleton i nd) cmp
                 ) qmp (zip [0..] defs)
  exprToNode args nqmp btor body
exprToNode mp qmp btor (App SMTEq [x,y]) = do
  ndx <- exprToNode mp qmp btor x
  ndy <- exprToNode mp qmp btor y
  boolectorEq (boolectorInstance btor) ndx ndy
exprToNode mp qmp btor (App (SMTFun fun _) args) = do
  funNd <- case Map.lookup fun (boolectorVars btor) of
    Just (nd,_) -> return nd
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToNode mp qmp btor arg,())) args (extractArgAnnotation args) ()
  argNds <- sequence argLst
  boolectorApply (boolectorInstance btor) argNds funNd
exprToNode mp qmp btor (App (SMTLogic op) args) = do
  nd:nds <- mapM (exprToNode mp qmp btor) args
  let rop = case op of
        And -> boolectorAnd
        Or -> boolectorOr
        XOr -> boolectorXOr
        Implies -> boolectorImplies
  foldlM (rop (boolectorInstance btor)) nd nds
exprToNode mp qmp btor (App SMTNot e) = do
  nd <- exprToNode mp qmp btor e
  boolectorNot (boolectorInstance btor) nd
exprToNode mp qmp btor (App SMTDistinct [x,y]) = do
  ndx <- exprToNode mp qmp btor x
  ndy <- exprToNode mp qmp btor y
  res <- boolectorEq (boolectorInstance btor) ndx ndy
  boolectorNot (boolectorInstance btor) res
exprToNode mp qmp btor (App SMTITE (c,ifT,ifF)) = do
  ndC <- exprToNode mp qmp btor c
  ndIfT <- exprToNode mp qmp btor ifT
  ndIfF <- exprToNode mp qmp btor ifF
  boolectorCond (boolectorInstance btor) ndC ndIfT ndIfF
exprToNode mp qmp btor (App (SMTBVComp op) (e1,e2)) = do
  n1 <- exprToNode mp qmp btor e1
  n2 <- exprToNode mp qmp btor e2
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
exprToNode mp qmp btor (App (SMTBVBin op) (e1::SMTExpr (BitVector a),e2)) = do
  n1 <- exprToNode mp qmp btor e1
  n2 <- exprToNode mp qmp btor e2
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
exprToNode mp qmp btor (App (SMTBVUn op) e) = do
  n <- exprToNode mp qmp btor e
  (case op of
      BVNot -> boolectorNot
      BVNeg -> boolectorNeg) (boolectorInstance btor) n
exprToNode mp qmp btor (App SMTSelect (arr,i)) = do
  ndArr <- exprToNode mp qmp btor arr
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToNode mp qmp btor arg,())) i (extractArgAnnotation i) ()
  [ndI] <- sequence argLst
  boolectorRead (boolectorInstance btor) ndArr ndI
exprToNode mp qmp btor (App SMTStore (arr,i,v)) = do
  ndArr <- exprToNode mp qmp btor arr
  let (argLst,_) = unpackArgs (\arg _ _ -> (exprToNode mp qmp btor arg,())) i (extractArgAnnotation i) ()
  [ndI] <- sequence argLst
  ndV <- exprToNode mp qmp btor v
  boolectorWrite (boolectorInstance btor) ndArr ndI ndV
exprToNode mp qmp btor (App SMTConcat (e1,e2)) = do
  n1 <- exprToNode mp qmp btor e1
  n2 <- exprToNode mp qmp btor e2
  boolectorConcat (boolectorInstance btor) n1 n2
exprToNode mp qmp btor (App (SMTExtract prStart prLen) e) = do
  n <- exprToNode mp qmp btor e
  let start = reflectNat prStart 0
      len = reflectNat prLen 0
  boolectorSlice (boolectorInstance btor) n (fromIntegral $ start+len-1) (fromIntegral start)
exprToNode mp qmp btor (UntypedExpr e) = exprToNode mp qmp btor e
exprToNode mp qmp btor (UntypedExprValue e) = exprToNode mp qmp btor e
exprToNode _ _ _ e = error $ "smtlib2-boolector: No support for expression: "++show e

mkVar :: BoolectorBackend -> FunInfo -> Sort -> IO (Integer,BoolectorBackend)
mkVar btor info sort = do
  let vid = boolectorNextVar btor
      (name,ncs) = case funInfoName info of
        Nothing -> (escapeName (Right vid),
                    boolectorNameCount btor)
        Just name' -> case Map.lookup name' (boolectorNameCount btor) of
          Nothing -> (escapeName (Left (name',0)),
                      Map.insert name' 1 (boolectorNameCount btor))
          Just nc -> (escapeName (Left (name',nc)),
                      Map.insert name' (nc+1) (boolectorNameCount btor))
  nd <- case sort of
    Fix BoolSort -> boolectorVar (boolectorInstance btor) 1 name
    Fix (BVSort { bvSortWidth = w }) -> boolectorVar (boolectorInstance btor) (fromIntegral w) name
    Fix (ArraySort [Fix (BVSort { bvSortWidth = idx_w })] (Fix (BVSort { bvSortWidth = el_w })))
      -> boolectorArray (boolectorInstance btor) (fromIntegral el_w) (fromIntegral idx_w) name
    _ -> error $ "smtlib2-boolector: Boolector backend doesn't support sort "++show sort
  return (vid,btor { boolectorNextVar = vid+1
                   , boolectorNameCount = ncs
                   , boolectorVars = Map.insert vid (nd,name) (boolectorVars btor)
                   })

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
