{-# LANGUAGE TemplateHaskell,OverloadedStrings,FlexibleContexts #-}
{- | This module can be used to automatically lift haskell data-types into the SMT realm.
 -}
module Language.SMTLib2.TH
       (deriveSMT,
        constructor,
        field,
        matches,
        castField)
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Interface
import Language.SMTLib2.Internals.Instances ()
import Language.Haskell.TH
import qualified Data.AttoLisp as L
import qualified Data.Text as T hiding (foldl1)
import Data.Typeable
import Data.Maybe (catMaybes)
import qualified Data.Graph.Inductive as Gr
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable
import Prelude hiding (foldl,foldr,concat,elem,all,foldl1,init)
import Data.List (findIndex,genericLength,zip4)
import Data.Fix
import Data.Unit

data TypeGraph = TypeGraph { typeNodes :: Map Name Gr.Node
                           , typeGraph :: Gr.Gr Dec [Either Int Type] }
                 deriving Show

getTypeGraph :: Name -> Q TypeGraph
getTypeGraph tp = do
  (_,gr) <- getTypeGraph' tp (TypeGraph { typeNodes = Map.empty
                                        , typeGraph = Gr.empty })
  return gr
  where
    getTypeGraph' tp' gr = case Map.lookup tp' (typeNodes gr) of
      Just nd -> return (Just nd,gr)
      Nothing -> do
        inf <- reify tp'
        case inf of
          TyConI dec -> do
            replace_tp <- [t| Integer |]
            i <- isInstance ''SMTType [replaceVars replace_tp (typeFromDec dec)] -- XXX: This works around a bug in TH by replacing type variables with Integer.
                                                                                -- It isn't 100% right, but does the trick unless you do something strange.
                                                                                -- ...don't do something strange... please.
            if i
              then return (Nothing,gr)
              else (do
                       let [nd] = Gr.newNodes 1 (typeGraph gr)
                           ngr = TypeGraph { typeNodes = Map.insert tp' nd (typeNodes gr)
                                           , typeGraph = Gr.insNode (nd,dec) (typeGraph gr) }
                       ngr2 <- addDependencies nd dec ngr
                       return (Just nd,ngr2))
    addDependencies nd (DataD ctx name tyvars (con:cons) derives) gr = do
      ngr <- addDependenciesCon nd tyvars con gr
      addDependencies nd (DataD ctx name tyvars cons derives) ngr
    addDependencies nd (DataD ctx name tyvars [] derives) gr = return gr
    addDependencies nd (NewtypeD ctx name tyvars con derives) gr = addDependenciesCon nd tyvars con gr
    addDependenciesCon nd tyvars (RecC con_name fields) gr = foldlM (\cgr (_,_,tp) -> fieldDependencies nd tyvars tp cgr) gr fields
    addDependenciesCon nd tyvars (NormalC con_name fields) gr = foldlM (\cgr (_,tp) -> fieldDependencies nd tyvars tp cgr) gr fields

    unpackType :: Type -> Maybe (Name,[Type])
    unpackType (AppT t1 t2) = fmap (\(con,pars) -> (con,pars++[t2])) (unpackType t1)
    unpackType (ConT name) = Just (name,[])
    unpackType (TupleT n) = Just (tupleTypeName n,[])
    unpackType tp = Nothing

    replaceVars :: Type -> Type -> Type
    replaceVars with (VarT name) = with
    replaceVars with (AppT t1 t2) = AppT (replaceVars with t1) (replaceVars with t2)
    replaceVars with x = x

    typeFromDec :: Dec -> Type
    typeFromDec (DataD _ name tyvar _ _) = foldl (\t tyv -> AppT t (case tyv of
                                                                       PlainTV n -> VarT n
                                                                       KindedTV n _ -> VarT n)) (ConT name) tyvar
    typeFromDec (NewtypeD _ name tyvar _ _) = foldl (\t tyv -> AppT t (case tyv of
                                                                       PlainTV n -> VarT n
                                                                       KindedTV n _ -> VarT n)) (ConT name) tyvar

    resolvePar :: [TyVarBndr] -> Type -> Either Int Type
    resolvePar tyvars (VarT name) = case findIndex (\tyvar -> case tyvar of
                                                       PlainTV name' -> name==name'
                                                       KindedTV name' _ -> name==name') tyvars of
                                      Nothing -> error $ "Internal error: Unknown type variable "++show name
                                      Just idx -> Left idx
    resolvePar _ tp = Right tp

    fieldDependencies nd tyvars tp gr = case unpackType tp of
      Nothing -> return gr
      Just (con,pars) -> do
        (nd',ngr) <- getTypeGraph' con gr
        ngr2 <- foldlM (\cgr par -> fieldDependencies nd tyvars par cgr) ngr pars
        return $ case nd' of
                      Nothing -> ngr2
                      Just nd'' -> ngr2 { typeGraph = Gr.insEdge (nd,nd'',fmap (resolvePar tyvars) pars) (typeGraph ngr2) }

getDeclGroups :: TypeGraph -> [[Dec]]
getDeclGroups gr = if all (\grp -> checkGroup grp grp Nothing) comps
                   then fmap (fmap (\nd -> let Just dec = Gr.lab (typeGraph gr) nd
                                           in dec)) comps
                   else error "Datatypes invalid for deriving"
  where
    checkGroup [] _ _ = True
    checkGroup (x:xs) grp cur = case checkGroup' (Gr.lsuc (typeGraph gr) x) grp cur of
      Nothing -> False
      Just ncur -> checkGroup xs grp ncur

    checkGroup' [] grp cur = Just cur
    checkGroup' ((nd,lnk):lnks) grp cur = if nd `elem` grp
                                          then (case cur of
                                                   Nothing -> checkGroup' lnks grp (Just lnk)
                                                   Just rcur -> if rcur == lnk
                                                                then checkGroup' lnks grp (Just rcur)
                                                                else Nothing)
                                          else checkGroup' lnks grp cur
    comps = Gr.scc (typeGraph gr)

getDecInfo :: Dec -> (Name,[TyVarBndr])
getDecInfo (DataD _ n vars _ _) = (n,vars)
getDecInfo (TySynD n vars _) = (n,vars)
getDecInfo (NewtypeD _ n vars _ _) = (n,vars)

tyVarName :: TyVarBndr -> Name
tyVarName (PlainTV name) = name
tyVarName (KindedTV name _) = name

usedTypes :: Dec -> [Type]
usedTypes (DataD _ _ _ cons _) = concat $ fmap usedTypesCon cons
usedTypes (NewtypeD _ _ _ con _) = usedTypesCon con
usedTypes (TySynD _ _ tp) = [tp]

usedTypesCon :: Con -> [Type]
usedTypesCon (NormalC _ tps) = fmap snd tps
usedTypesCon (RecC _ fields) = fmap (\(_,_,tp) -> tp) fields
usedTypesCon (InfixC (_,tp1) _ (_,tp2)) = [tp1,tp2]
usedTypesCon (ForallC _ _ con) = usedTypesCon con

allCons :: Dec -> [Con]
allCons (DataD _ _ _ cons _) = cons
allCons (NewtypeD _ _ _ con _) = [con]

allFields :: ExpQ -> Dec -> [(ExpQ,Type)]
allFields udef (DataD _ _ _ cons _) = concat $ fmap (allFieldsCon udef) cons
allFields udef (NewtypeD _ _ _ con _) = allFieldsCon udef con
allFields udef (TySynD _ _ tp) = [(udef,tp)]

allFieldsCon :: ExpQ -> Con -> [(ExpQ,Type)]
allFieldsCon udef (NormalC name fields) = generate' 0 (length fields) fields
  where
    generate' i n [] = []
    generate' i n ((_,tp):tps) = (do
                                     p <- newName "p"
                                     letE [valD (tildeP $ conP name ((replicate i wildP)++[varP p]++(replicate (n-i-1) wildP))) (normalB udef) []] (varE p),tp)
                                 :(generate' (i+1) n tps)
allFieldsCon udef (RecC name fields) = fmap (\(fname,_,tp) -> (appE (varE fname) udef,tp)) fields
allFieldsCon udef (InfixC (_,tp1) name (_,tp2)) = [(do
                                                       p <- newName "p"
                                                       letE [valD (tildeP $ infixP (varP p) name wildP) (normalB udef) []] (varE p),tp1)
                                                  ,(do
                                                       p <- newName "p"
                                                       letE [valD (tildeP $ infixP wildP name (varP p)) (normalB udef) []] (varE p),tp2)
                                                  ]

getTyCon :: Type -> Maybe Name
getTyCon (ConT name) = Just name
getTyCon (AppT l _) = getTyCon l
getTyCon (TupleT n) = Just (tupleDataName n)
getTyCon (SigT tp _) = getTyCon tp
getTyCon _ = Nothing

splitType :: Type -> Maybe (Name,[Type])
splitType (ConT name) = Just (name,[])
splitType (AppT tp1 tp2) = case splitType tp1 of
  Nothing -> Nothing
  Just (name,tps) -> Just (name,tps++[tp2])
splitType (TupleT n) = Just (tupleDataName n,[])
splitType _ = Nothing

declStructure :: ExpQ -> [Name] -> Dec -> (String,[(String,[(String,ExpQ)])])
declStructure undef allNames (DataD _ name tyvars cons _) = (nameBase name,fmap (declStructureCon undef allNames tyvars) cons)
declStructure undef allNames (NewtypeD _ name tyvars con _) = (nameBase name,[declStructureCon undef allNames tyvars con])

declStructureCon :: ExpQ -> [Name] -> [TyVarBndr] -> Con -> (String,[(String,ExpQ)])
declStructureCon undef allNames tyvars (RecC name fields)
  = (nameBase name,
     fmap (\(name,_,tp) -> (nameBase name,
                           declStructureType undef allNames tyvars (\e -> appE (varE name) e) tp)) fields)
declStructureCon undef allNames tyvars (NormalC name []) = (nameBase name,[])
declStructureCon undef allNames tyvars c = error $ "declStructureCon unimplemented for "++show c

declStructureType :: ExpQ -> [Name] -> [TyVarBndr] -> (ExpQ -> ExpQ) -> Type -> ExpQ
declStructureType undef allNames tyvars accessor tp
  = case splitType tp of
    Just (con,args) -> if con `elem` allNames
                       then [| L.Symbol (T.pack $(stringE (nameBase con))) |]
                       else (appsE [[| getSort |],accessor undef,[| () |]])
    Nothing -> case tp of
      VarT name -> case findIndex (\tv -> case tv of
                                      PlainTV name' -> name == name'
                                      KindedTV name' _ -> name == name') tyvars of
                     Just idx -> [| L.Symbol (T.pack $(stringE $ "tv"++show idx)) |]

generateGetSort :: Dec -> Q Dec
generateGetSort decl = do
  let (name,args) = getDecInfo decl
  argAnns <- mapM (\arg -> do
                      name <- newName "ann"
                      return (arg,name)
                  ) args
  funD 'getSort [clause [sigP wildP (foldl appT (conT name) (fmap (varT . tyVarName . fst) argAnns))
                        ,tupP [varP ann | (_,ann) <- argAnns ]]
                   (normalB $ appE [| Fix |]
                                   (appsE [[| NamedSort |]
                                          ,stringE (nameBase name)
                                          ,listE [ appsE [ [| getSort |]
                                                         , sigE [| undefined |] (varT $ tyVarName arg)
                                                         , varE annName ] | (arg,annName) <- argAnns ]])) [] ]

generateAsValueType :: Dec -> Q Dec
generateAsValueType decl = do
  fun <- newName "f"
  funD 'asValueType
    [clause [sigP wildP (foldl appT (conT name) (fmap (varT . tyVarName) args))
            ,varP fun]
      (normalB $ mkExpr fun args []) []]
  where
    (name,args) = getDecInfo decl
    mkExpr fun [] tps = appE (varE fun) (sigE [| undefined |] (foldl appT (conT name) tps))
    mkExpr fun (x:xs) tps = do
      tpName <- newName "tp"
      appsE [varE 'asValueType
            ,sigE [| undefined |] (varT $ tyVarName x)
            ,lamE [sigP wildP (varT $ tpName)] (mkExpr fun xs (tps++[varT tpName]))]

generateTypeCollection :: [Dec] -> ExpQ
generateTypeCollection decls
  = recConE 'TypeCollection
      [ fieldExp 'argCount (litE $ IntegerL argC)
      , fieldExp 'dataTypes (listE dts)
      ]
  where
    argC = case head decls of
      DataD _ _ args _ _ -> genericLength args
      NewtypeD _ _ args _ _ -> genericLength args
    dts = [ recConE 'DataType
              [ fieldExp 'dataTypeName (stringE $ nameBase declName)
              , fieldExp 'dataTypeConstructors (listE (cons declName tyvars decl))
              , fieldExp 'dataTypeGetUndefined
                  (do
                      paramTs <- mapM (const $ newName "tp") tyvars
                      fname <- newName "f"
                      lamE [listP [ varP p | p <- paramTs ],varP fname]
                        (generateUndef declName paramTs fname []))
              ]
          | decl <- decls
          , let (declName,tyvars) = getDecInfo decl
          ]
    generateUndef dName [] fname tps = appsE [varE fname
                                       ,sigE [| undefined |] (foldl appT (conT dName) (fmap (varT . fst) tps))
                                       ,tupE [ varE ann | (_,ann) <- tps ]]
    generateUndef dName (x:xs) fname tps
      = appsE [ [| withProxyArg |]
              , varE x
              , do
                  tp <- newName "tp"
                  ann <- newName "ann"
                  lamE [ sigP wildP (varT tp),varP ann ] (generateUndef dName xs fname (tps++[(tp,ann)])) ]
    cons dName tyvars decl
      = [ case con of
            RecC name f
              -> recConE 'Constr
                  [ fieldExp 'conName (stringE $ nameBase name)
                  , fieldExp 'conFields (listE (fields dName tyvars f))
                  , fieldExp 'construct (generateConstruct dName name tyvars f)
                  , fieldExp 'conTest (generateConTest dName name tyvars f)
                  ]
            NormalC name []
              -> recConE 'Constr
                  [ fieldExp 'conName (stringE $ nameBase name)
                  , fieldExp 'conFields (listE [])
                  , fieldExp 'construct (generateConstruct dName name tyvars [])
                  , fieldExp 'conTest (generateConTest dName name tyvars [])
                  ]
        | con <- allCons decl ]
    generateConstruct dName cName tyvars fs = do
      let (rem,inf) = getInference (Set.fromList $ fmap tyVarBndrName tyvars) fs
      f <- newName "f"
      prxs <- mapM (const (newName "prx")) tyvars
      tvs <- mapM (const (newName "tp")) tyvars
      anns <- mapM (const (newName "ann")) tyvars
      args <- mapM (const (newName "arg")) fs
      rargs <- mapM (const (newName "rarg")) fs
      let body = foldr (\(inf,arg,rarg) e
                        -> if Set.null rem || inf
                           then appsE [[| withAnyValue |]
                                      ,varE arg
                                      ,lamE [varP rarg,wildP] e]
                           else letE [valD (conP 'Just [tupP [varP rarg,wildP]])
                                           (normalB $ appE [| castAnyValue |] (varE arg)) []]
                                     e)
                   (appsE [varE f
                          ,sigE (appsE ((conE cName):
                                        (fmap varE rargs))) (foldl appT (conT dName) (fmap varT tvs))
                          ,tupE (fmap varE anns)]) (zip3 inf args rargs)
      lamE [if Set.null rem
            then wildP
            else conP 'Just [listP [ varP prx | prx <- prxs ]]
           ,listP $ fmap varP args
           ,varP f]
           (if Set.null rem
            then body
            else foldr (\(prx,tv,ann) e
                        -> appsE [varE 'withProxyArg
                                 ,varE prx
                                 ,lamE [sigP wildP (varT tv),varP ann] e]
                       ) body (zip3 prxs tvs anns))
    generateConTest dName cName tyvars fs = do
      prxs <- mapM (const (newName "prx")) tyvars
      tvs <- mapM (const (newName "tv")) tyvars
      obj <- newName "obj"
      lamE [listP $ fmap varP prxs,varP obj]
           (foldr (\(prx,tv) e
                   -> appsE [varE 'withProxyArg
                            ,varE prx
                            ,lamE [sigP wildP (varT tv),wildP] e]
                  ) (caseE (appE (varE 'cast) (varE obj))
                           [match (conP 'Just [sigP (conP cName (fmap (const wildP) fs)) (foldl appT (conT dName) (fmap varT tvs))])
                                  (normalB (conE 'True)) []
                           ,match wildP (normalB (conE 'False)) []]) (zip prxs tvs))

    getInference tyvars [] = (tyvars,[])
    getInference tyvars ((_,_,tp):fs)
      = let tyvars' = allTyVars tp
            (ntyvars,res) = getInference (Set.difference tyvars tyvars') fs
        in (ntyvars,(Set.null (Set.intersection tyvars tyvars')):res)

    fields dName tyvars f
      = [ recConE 'DataField
            [ fieldExp 'fieldName (stringE $ nameBase fname)
            , fieldExp 'fieldSort (getArgSort tyvars tp)
            , fieldExp 'fieldGet (generateGet dName tyvars fname) ]
        | (fname,_,tp) <- f ]
    getArgSort tyvars (VarT name) = case findIndex (\tyvar -> case tyvar of
                                                       PlainTV n -> n==name
                                                       KindedTV n _ -> n==name) tyvars of
                                      Just idx -> appE (conE 'Fix) (appE (conE 'ArgumentSort) (litE $ integerL $ fromIntegral idx))
    getArgSort tyvars tp
      | name == ''Integer = appE (conE 'Fix) (appE (conE 'NormalSort) (conE 'IntSort))
      | otherwise = appE (conE 'Fix) (appE (conE 'NormalSort) (appsE [conE 'NamedSort,stringE $ nameBase name,listE (fmap (getArgSort tyvars) args)]))
      where
        (name,args) = reconstruct tp []
    generateGet dName tyvars fname = do
      paramTs <- mapM (const $ newName "p") tyvars
      obj <- newName "obj"
      f <- newName "f"
      lamE [listP (fmap varP paramTs),varP obj,varP f]
        (generateGet' dName paramTs obj f fname [])
    generateGet' dName (x:xs) obj f fname tps = do
      tp <- newName "tp"
      ann <- newName "ann"
      appsE [ [| withProxyArg |]
            , varE x
            , lamE [sigP wildP (varT tp)
                   ,{-sigP (-}varP ann{-) (appT (conT ''SMTAnnotation) (varT tp))-}]
                   (generateGet' dName xs obj f fname (tps++[(tp,ann)]))]
    generateGet' dName [] obj f fname tps = do
      res <- newName "res"
      let complTp = foldl appT (conT dName) (fmap (varT . fst) tps)
      caseE (appE [| cast |] (varE obj))
        [match (conP 'Just [sigP (varP res) complTp])
               (normalB $ appsE [varE f,appE (varE fname) (varE res)
                                ,case tps of
                                   [(_,ann)] -> varE ann
                                   _ -> tupE [ varE ann | (_,ann) <- tps ] ]) []]

allTyVars :: Type -> Set Name
allTyVars (ForallT bound _ tp)
  = Set.difference (allTyVars tp)
                   (Set.fromList $ fmap tyVarBndrName bound)
allTyVars (AppT t1 t2) = Set.union (allTyVars t1) (allTyVars t2)
allTyVars (SigT tp _) = allTyVars tp
allTyVars (VarT n) = Set.singleton n
allTyVars _ = Set.empty

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _) = n

getUndefFun :: Name -> [TyVarBndr] -> TyVarBndr -> ExpQ -> ExpQ
getUndefFun con tyvars tvar udef
  = do
    appE
      (tupE
         [sigE [| const undefined |]
               (forallT tyvars (cxt []) $
                appT
                 (appT arrowT
                       (foldl appT (conT con) (fmap (varT.tyVarName) tyvars)))
                 (varT (tyVarName tvar)))]
      ) udef

--[| (const undefined :: $(foldl appT (conT con) (fmap (varT.tyVarName) tyvars)) -> $(varT (tyVarName tvar))) $(udef) |]

sortExpr :: Name -> [TyVarBndr] -> ExpQ -> ExpQ
sortExpr con [] _ = [| L.Symbol (T.pack $(stringE (nameBase con))) |]
sortExpr con tyvars udef = [| L.List |] `appE` (listE $ [ [| L.Symbol (T.pack $(stringE (nameBase con))) |] ]
                                                ++ [ [| getSort |] `appE` (getUndefFun con tyvars tv udef)
                                                                   `appE` (tupE []) | tv <- tyvars ])

-- | Given a data-type, this function derives an instance of both 'SMTType' and 'SMTValue' for it.
--   Example: @ $(deriveSMT 'MyType) @
deriveSMT :: Name -> Q [Dec]
deriveSMT name = do
  tg <- getTypeGraph name
  pat <- newName "u"
  ann <- newName "ann"
  field <- newName "field"
  let grps = getDeclGroups tg
  mapM (\(i,grp) -> do
           let coll = mkName ("typeCollection_"++(nameBase name)++"_"++show i)
           tyCollD <- funD coll [clause [] (normalB $ generateTypeCollection grp) []]
           decls <- mapM (\dec -> do
                             let (dec_name,tyvars) = getDecInfo dec
                                 fullType = foldl appT (conT dec_name) (fmap (\n -> varT (tyVarName n)) tyvars)
                             inst1 <- instanceD (cxt [classP ''SMTType [varT n]
                                                     | n <- fmap tyVarName tyvars ])
                                      (appT (conT ''SMTType) fullType)
                                      [tySynInstD ''SMTAnnotation [fullType] (foldl appT (tupleT (genericLength tyvars)) [ appT (conT ''SMTAnnotation) (varT $ tyVarName tyvar)
                                                                                                                         | tyvar <- tyvars ]),
                                       generateGetSort dec,
                                       funD 'asDataType [ clause [wildP] (normalB $ appsE [ [| Just |]
                                                                                          , tupE [stringE $ nameBase $ dec_name
                                                                                          , varE coll]]) []],
                                       do
                                         f <- newName "f"
                                         tps <- mapM (const (newName "tp")) tyvars
                                         tps2 <- mapM (const (newName "tp'")) tyvars
                                         anns <- mapM (const (newName "ann")) tyvars
                                         anns' <- mapM (const (newName "ann'")) tyvars
                                         funD 'asValueType [clause [sigP wildP (foldl appT (conT dec_name) (fmap varT tps))
                                                                   ,tupP (fmap varP anns)
                                                                   ,varP f]
                                                                   (normalB $
                                                                    (if null tyvars
                                                                     then appE [| Just |]
                                                                     else \arg
                                                                          -> foldr (\(tp1,tp2,ann,ann') e
                                                                                    -> appsE [[| asValueType |]
                                                                                             ,sigE [| undefined |]
                                                                                                   (varT tp1)
                                                                                             ,varE ann
                                                                                             ,lamE [sigP wildP (varT tp2),varP ann'] e]
                                                                                   ) arg (zip4 tps tps2 anns anns'))
                                                                    (appsE [varE f
                                                                           ,sigE [| undefined |] (foldl appT (conT dec_name) (fmap varT tps2))
                                                                           ,tupE (fmap varE anns')])
                                                                   ) []],
                                       do
                                         args <- mapM (const (newName "arg")) tyvars
                                         funD 'annotationFromSort [clause [sigP wildP fullType
                                                                          ,conP 'Fix [conP 'NamedSort [wildP,listP $ fmap varP args]]]
                                                                          (normalB $ tupE [ appsE [[| annotationFromSort |]
                                                                                                  ,sigE [| undefined |] (varT $ tyVarName tv)
                                                                                                  ,varE arg]
                                                                                          | (arg,tv) <- zip args tyvars ]) []]
                                      ]
                             inst2 <- instanceD (cxt $ concat [[classP ''SMTValue [varT n]
                                                              ,equalP ((conT ''SMTAnnotation) `appT` (varT n)) (tupleT 0)] | n <- fmap tyVarName tyvars ])
                                       (appT (conT ''SMTValue) fullType)
                                       [generateMangleFun dec
                                       ,generateUnmangleFun dec]
                             inst3 <- instanceD (cxt $ concat [[classP ''SMTType [varT n]
                                                             ,equalP ((conT ''SMTAnnotation) `appT` (varT n)) (tupleT 0)] | n <- fmap tyVarName tyvars ])
                                       (appT (conT ''SMTRecordType) fullType)
                                       [funD 'getFieldAnn [clause [varP field,wildP] (normalB [| castField $(varE field) () |]) []]]
                             return [inst1,inst2,inst3]) grp
           return ((concat decls)++[tyCollD])) (zip [0..] grps) >>= return . concat

castField :: (Typeable (SMTAnnotation f),Typeable g,SMTType f) => Field a f -> g -> SMTAnnotation f
castField (Field name) ann = case cast ann of
  Nothing -> error $ "Internal smtlib2 error: Invalid type access for field "++show name
  Just r -> r

generateMangleFun :: Dec -> DecQ
generateMangleFun dec
  = funD 'mangle [ do
                     let (cname,fields) = case con of
                                            RecC name fields -> (name,fields)
                                            NormalC name [] -> (name,[])
                     vars <- mapM (\field -> do
                                     fName <- newName "f"
                                     return (field,fName)) fields
                     alias <- newName "alias"
                     ann <- newName "ann"
                     annF <- mapM (\var -> do
                                    annName <- newName "annF"
                                    return (var,annName)) tyvars
                     clause [asP alias (conP cname (fmap (varP . snd) vars)),asP ann (tupP [ varP ann' | (_,ann') <- annF ])]
                            (normalB (appsE [ [| ConstrValue |]
                                            , stringE $ nameBase cname
                                            , listE [ appsE [ [| mangle |], varE v
                                                            , getAnn annF tp
                                                            ]
                                                    | ((_,_,tp),v) <- vars ]
                                            , appE [| Just |] (appsE [ [| getSort |]
                                                                     , varE alias
                                                                     , varE ann ])])) []
                 | con <- case dec of
                            DataD _ _ _ cons _ -> cons
                            NewtypeD _ _ _ con _ -> [con]
                 ]
 where
   (name,tyvars) = getDecInfo dec

getAnn :: [(TyVarBndr,Name)] -> Type -> ExpQ
getAnn annF (VarT name) = case find (\(tyvar',_) -> case tyvar' of
                                       PlainTV n -> n==name
                                       KindedTV n _ -> n==name) annF of
  Just (_,ann) -> varE ann
getAnn annF tp = let (_,tps) = reconstruct tp []
                  in tupE (fmap (getAnn annF) tps)

reconstruct :: Type -> [Type] -> (Name,[Type])
reconstruct (ConT name) tps = (name,tps)
reconstruct (AppT x tp) tps = reconstruct x (tp:tps)

generateUnmangleFun :: Dec -> Q Dec
generateUnmangleFun dec
  = do
    let (_,tyvars) = getDecInfo dec
        cons = case dec of
          DataD _ _ _ c _ -> c
          NewtypeD _ _ _ c _ -> [c]
        cl = fmap (genClause tyvars) cons
    funD 'unmangle (cl++[clause [wildP,wildP] (normalB [| Nothing |]) []])

genClause :: [TyVarBndr] -> Con -> Q Clause
genClause tyvars (RecC name fields) = do
  fieldVars <- mapM (\f -> do
                        fname <- newName "f"
                        return (f,fname)) fields
  annVars <- mapM (\tyvar -> do
                      annName <- newName "ann"
                      return (tyvar,annName)) tyvars
  clause [conP 'ConstrValue [litP $ stringL $ nameBase name
                            ,listP [ varP fname | (_,fname) <- fieldVars ]
                            ,wildP]
         ,tupP [ varP annName | (_,annName) <- annVars ]]
    (do
          (bdy,res) <- genBody annVars fieldVars annVars []
          normalB $ doE (bdy++[noBindS res])) []
  where
    genBody annVars (((_,_,ftype),fname):fields) anns fvars = do
      fvar <- newName "fr"
      (rest,res) <- genBody annVars fields anns (fvars++[fvar])
      let stmt = bindS (varP fvar) (appsE [[| unmangle |]
                                          ,varE fname
                                          ,getAnn annVars ftype])
      return (stmt:rest,res)
    genBody _ [] _ fvars = return ([],appE [| Just |] (appsE ((conE name):(fmap varE fvars))))
genClause tyvars (NormalC name []) = do
  clause [conP 'ConstrValue [litP $ stringL $ nameBase name
                            ,listP []
                            ,wildP]
         ,tupP []] (normalB $ appE [| Just |] (conE name)) []

constructorType :: Type -> TypeQ
constructorType tp = if null tbndr
                     then tbody
                     else forallT tbndr (cxt []) tbody
  where
    tbody = [t| Constructor |] `appT`
            (foldl appT (tupleT (length targs))
             [ [t| SMTExpr |] `appT` (return targ) | targ <- targs]) `appT` (return tres)
    (tbndr,targs,tres) = constructorType' tp

constructorType' :: Type -> ([TyVarBndr],[Type],Type)
constructorType' (ForallT bndr _ tp) = let (tbndr,targ,tres) = constructorType' tp
                                       in (bndr++tbndr,targ,tres)
constructorType' (AppT (AppT ArrowT from) to)
  = let (tbndr,targ,tres) = constructorType' to
    in (tbndr,from:targ,tres)
constructorType' tp = ([],[],tp)

-- | Get the SMT representation for a given constructor.
constructor :: Name -> Q Exp
constructor name = do
  inf <- reify name
  case inf of
    DataConI _ tp _ _ -> [| Constructor $(stringE $ nameBase name) :: $(constructorType tp) |]

-- | Get the SMT representation for a given record field accessor.
field :: Name -> Q Exp
field name = do
  inf <- reify name
  case inf of
    VarI _ tp _ _ -> case getExp tp of
      Just rtp -> sigE [| (Field $(stringE $ nameBase name)) |] rtp
      Nothing -> error $ show inf ++ " is not a valid field"
    _ -> error $ show inf ++ " is not a valid field"
  where
    getExp (AppT (AppT ArrowT orig) res) = Just $ [t| Field |] `appT` (return orig) `appT` (return res)
    getExp (ForallT tyvars ctx rec) = fmap (forallT tyvars (return ctx)) (getExp rec)
    getExp _ = Nothing

-- | Checks whether a given SMT expression matches a pattern.
matches :: Q Exp -> Q Pat -> Q Exp
matches exp pat = do
  p <- pat
  case matches' exp p of
    Nothing -> [| constant True |]
    Just res -> res
  where
    matches' exp (LitP l) = Just [| $exp .==. $(litE l) |]
    matches' _ WildP = Nothing
    matches' exp (ConP name []) = Just [| is $exp $(constructor name) |]
    matches' exp (ConP name pats) = Just $ do
      DataConI _ _ d _ <- reify name
      TyConI (DataD _ _ _ cons _) <- reify d
      let Just (RecC _ fields) = find (\con -> case con of
                                          RecC n _ -> n==name
                                          _ -> False) cons
      [| foldl (.&&.) (constant True) $ (is $exp $(constructor name)): $(listE $ catMaybes [ matches' [| $exp .# $(field f) |] pat | ((f,_,_),pat) <- Prelude.zip fields pats ]) |]
    matches' exp (RecP name pats) = Just [| foldl (.&&.) (constant True) $ (is $exp $(constructor name)): $(listE $ catMaybes [ matches' [| $exp .# $(field f) |] pat | (f,pat) <- pats ]) |]
