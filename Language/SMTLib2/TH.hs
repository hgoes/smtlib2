{-# LANGUAGE TemplateHaskell,OverloadedStrings,FlexibleContexts #-}
{- | This module can be used to automatically lift haskell data-types into the SMT realm.
 -}
module Language.SMTLib2.TH 
       (deriveSMT,
        constructor,
        field,
        matches)
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.SMTMonad
import Language.SMTLib2.Internals.Interface
import Language.Haskell.TH
import qualified Data.AttoLisp as L
import qualified Data.Text as T
import Data.Typeable
import Data.Maybe (catMaybes)
import qualified Data.Graph.Inductive as Gr
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Foldable
import Prelude hiding (foldl,concat,elem,all)
import Data.List (findIndex)

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

generateDeclareType :: Dec -> [Dec] -> Q Dec
generateDeclareType decl decls = do
  pat <- newName "u"
  ann <- newName "ann"
  funD 'declareType [clause [varP pat,varP ann] (normalB (body (varE pat) ann)) []]
  where
    (repr_name,tyvars) = getDecInfo (head decls)
    all_names = fmap (fst.getDecInfo) decls
    body pat ann = do
      c <- newName "c"
      decls <- newName "decls"
      mp <- newName "mp"
      con <- newName "con"
      appE (appE [| declareType' |] pat)
           (doE $ [ noBindS $ [| declareType |] `appE` e `appE` [| () |] | (e,tp) <- allFields pat decl 
                                                                        , case getTyCon tp of
                                                                            Nothing -> True
                                                                            Just tycon -> not $ tycon `elem` all_names
                  ] ++ [ noBindS (dataDecl pat) ])
    dataDecl p = [| declareDatatypes |] `appE` 
               (listE [ stringE $ "tv"++show n | (n,tv) <- zip [0..] tyvars ]) `appE`
               (listE [ tupE [ [| T.pack |] `appE` (stringE dname)  -- The datatype name
                             , listE [ tupE [ [| T.pack |] `appE` (stringE cname) -- The constructor name
                                            , listE [ tupE [ stringE fname -- The field name
                                                           , expr ]
                                                    | (fname,expr) <- fields
                                                    ]
                                            ]
                                     | (cname,fields) <- cons
                                     ]
                             ]
                      | (dname,cons) <- fmap (declStructure p all_names) decls
                      ])

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
      res = fmap (\grp -> fmap (\dec -> let (dec_name,tyvars) = getDecInfo dec
                                            fullType = foldl appT (conT dec_name) (fmap (\n -> varT (tyVarName n)) tyvars)
                                        in [instanceD (cxt $ concat [[classP ''SMTType [varT n]
                                                                     ,equalP ((conT ''SMTAnnotation) `appT` (varT n)) (tupleT 0)] | n <- fmap tyVarName tyvars ])
                                            (appT (conT ''SMTType) fullType)
                                            [funD 'getSort [clause [varP pat,wildP] 
                                               (normalB $ sortExpr dec_name tyvars (varE pat)) []],
                                             funD 'getSortBase [clause [varP pat] (normalB $ [| L.Symbol (T.pack $(stringE $ nameBase dec_name)) |]) []],
                                             generateDeclareType dec grp,
                                             tySynInstD ''SMTAnnotation [fullType] (tupleT 0)
                                            ],
                                            instanceD (cxt $ concat [[classP ''SMTValue [varT n]
                                                                     ,equalP ((conT ''SMTAnnotation) `appT` (varT n)) (tupleT 0)] | n <- fmap tyVarName tyvars ])
                                            (appT (conT ''SMTValue) fullType)
                                            [generateMangleFun dec
                                            ,generateUnmangleFun dec],
                                            instanceD (cxt $ concat [[classP ''SMTType [varT n]
                                                                     ,equalP ((conT ''SMTAnnotation) `appT` (varT n)) (tupleT 0)] | n <- fmap tyVarName tyvars ])
                                            (appT (conT ''SMTRecordType) fullType)
                                            [funD 'getFieldAnn [clause [varP field,wildP] (normalB [| castField $(varE field) () |]) []]]
                                           ]) grp) grps
  sequence $ concat $ concat res

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
                     vars <- mapM (const $ newName "f") fields
                     alias <- newName "alias"
                     ann <- newName "ann"
                     clause [asP alias (conP cname (fmap varP vars)),varP ann]
                            (normalB (if Prelude.null vars
                                                    then [| L.Symbol $(stringE $ nameBase cname) |]
                                                    else [| L.List $ [L.Symbol $(stringE $ nameBase cname)] ++
                                                                     $(listE [ appsE [ [| mangle |], varE v, tupE [] ]
                                                                             | v <- vars ]) |]
                                                    )) []
                 | con <- case dec of
                            DataD _ _ _ cons _ -> cons
                            NewtypeD _ _ _ con _ -> [con]
                 ]

generateUnmangleFun :: Dec -> Q Dec
generateUnmangleFun dec 
  = do
    p <- newName "p"
    ann <- newName "ann"
    let cons = case dec of
          DataD _ _ _ c _ -> c
          NewtypeD _ _ _ c _ -> [c]
        cl = fmap genClause cons
        asClause = clause [conP 'L.List [ listP [ [p| L.Symbol "as" |],varP p,wildP] ],varP ann] (normalB $ [| unmangle |] `appE` (varE p) `appE` (varE ann)) []
    funD 'unmangle (cl++[asClause,clause [wildP,wildP] (normalB [| return Nothing |]) []])

genClause :: Con -> Q Clause
genClause (NormalC cname []) = clause [conP 'L.Symbol [litP $ stringL $ nameBase cname],wildP] (normalB $ [| return |] `appE` ([| Just |] `appE` (conE cname))) []
genClause (RecC cname fields) = do
  vars <- mapM (const $ do
                   v1 <- newName "f"
                   v2 <- newName "r"
                   v3 <- newName "q"
                   return (v1,v2,v3)) fields
  let genRet e [] = appsE [[| return |],appsE [[| Just |],e]]
      genRet e ((v,r,q):vs) = doE [ bindS (varP r) (appsE [ [| unmangle |],varE v,tupE [] ]) 
                                  , noBindS $ caseE (varE r)
                                              [ match (conP 'Just [varP q]) (normalB (genRet e vs)) []
                                              , match (conP 'Nothing []) (normalB [| return Nothing |]) []
                                              ]
                                  ]
  clause [(if Prelude.null fields
           then conP 'L.Symbol [litP $ stringL $ nameBase cname]
           else conP 'L.List [listP $ [conP 'L.Symbol [litP $ stringL $ nameBase cname]]++
                                      (fmap (\(v,_,_) -> varP v) vars)])
         ,wildP]
    (normalB $ genRet (appsE $ (conE cname):(fmap (\(_,_,q) -> varE q) vars)) vars) []

constructorType :: Type -> TypeQ
constructorType (AppT _ tp) = constructorType tp
constructorType (ForallT tyvars ctx tp) = forallT tyvars (return ctx) (constructorType tp)
constructorType tp = [t| Constructor |] `appT` (return tp)

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
      Just rtp -> sigE [| (Field (T.pack $(stringE $ nameBase name))) |] rtp
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
      [| and' $ (is $exp $(constructor name)): $(listE $ catMaybes [ matches' [| $exp .# $(field f) |] pat | ((f,_,_),pat) <- Prelude.zip fields pats ]) |]
    matches' exp (RecP name pats) = Just [| and' $ (is $exp $(constructor name)): $(listE $ catMaybes [ matches' [| $exp .# $(field f) |] pat | (f,pat) <- pats ]) |]
    
