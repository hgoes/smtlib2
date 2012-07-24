{-# LANGUAGE TemplateHaskell,OverloadedStrings #-}
{- | This module can be used to automatically lift haskell data-types into the SMT realm.
 -}
module Language.SMTLib2.TH 
       (deriveSMT,
        constructor,
        field,
        matches)
       where

import Language.SMTLib2.Internals
import Language.SMTLib2.Internals.Interface
import Language.Haskell.TH
import qualified Data.AttoLisp as L
import Data.Text as T
import Data.Typeable
import Data.List as List
import Data.Maybe (catMaybes)

data ExtrType = ExtrType { extrArguments :: [Name]
                         , extrContent :: Either [(Name,[(Name,Type)])] (Name,Name,Type) }

-- | Given a data-type, this function derives an instance of both 'SMTType' and 'SMTValue' for it.
--   Example: @ $(deriveSMT 'MyType) @
deriveSMT :: Name -> Q [Dec]
deriveSMT name = do
  tp <- extractDataType name
  pat <- newName "u"
  ann <- newName "ann"
  let fullType = List.foldl appT (conT name) (fmap (\n -> varT n) (extrArguments tp))
      decls = [instanceD (cxt $ List.concat [[classP ''SMTType [varT n]
                                             ,equalP ((conT ''SMTAnnotation) `appT` (varT n)) (tupleT 0)] | n <- extrArguments tp ]) (appT (conT ''SMTType) fullType)
               [funD 'getSort [clause [wildP,varP ann] (normalB $ generateSortExpr name tp ann) []],
                funD 'declareType [clause [varP pat,varP ann] (normalB $ generateDeclExpr name tp pat ann) []],
                tySynInstD ''SMTAnnotation [fullType] (tupleT 0)
               ],
               instanceD (cxt $ List.concat [[classP ''SMTValue [varT n]
                                             ,equalP ((conT ''SMTAnnotation) `appT` (varT n)) (tupleT 0)] | n <- extrArguments tp]) (appT (conT ''SMTValue) fullType)
               [generateMangleFun tp,
                generateUnmangleFun tp]
              ]
  sequence decls

endType :: Type -> Type
endType (AppT _ tp) = endType tp
endType tp = tp

-- | Get the SMT representation for a given constructor.
constructor :: Name -> Q Exp
constructor name = do
  inf <- reify name
  case inf of
    DataConI _ tp _ _ -> [| Constructor $(stringE $ nameBase name) :: Constructor $(return $ endType tp) |]

-- | Get the SMT representation for a given record field accessor.
field :: Name -> Q Exp
field name = do
  inf <- reify name
  case inf of
    VarI _ (AppT (AppT ArrowT orig) res) _ _ -> [| Field $(stringE $ nameBase name) :: Field $(return orig) $(return res) |]
    _ -> error $ show inf ++ " is not a valid field"

extractDataType :: Name -> Q ExtrType
extractDataType name = do
  inf <- reify name
  return $ case inf of
    TyConI (DataD _ _ vars cons _)
      -> ExtrType { extrArguments = fmap getTyVar vars
                  , extrContent = Left $ fmap (\con -> case con of
                                                  RecC n vars -> (n,fmap (\(vn,_,tp) -> (vn,tp)) vars)
                                                  NormalC n [] -> (n,[])
                                                  _ -> error $ "Can't derive SMT classes for constructor "++show con
                                              ) cons }
    TyConI (NewtypeD _ name _ (NormalC con [(_,tp)]) _)
      -> ExtrType { extrArguments = []
                  , extrContent = Right (name,con,tp) }
    _ -> error $ "Can't derive SMT classes for "++show inf
  where
    getTyVar :: TyVarBndr -> Name
    getTyVar (PlainTV n) = n
    getTyVar (KindedTV n _) = n

generateSortExpr :: Name -> ExtrType -> Name -> Q Exp
generateSortExpr name (ExtrType { extrContent = Left _ }) ann = [| L.Symbol $(stringE $ nameBase name) |]
generateSortExpr name (ExtrType { extrContent = Right (name',con,tp) }) ann = [| getSort (undefined :: $(return tp)) $(varE ann) |]

generateDeclExpr :: Name -> ExtrType -> Name -> Name -> Q Exp
generateDeclExpr dname (ExtrType { extrContent = Left cons }) pat ann
  = [| declareType' (typeOf $(varE pat))
       (declareDatatypes [] [(T.pack $(stringE $ nameBase dname),
                              $(listE [ tupE [ [| T.pack $(stringE $ nameBase cname) |],  
                                               listE [ tupE [ stringE $ nameBase sname,
                                                              appsE [ [| getSort |],
                                                                      [| (undefined :: $(return tp)) |],
                                                                      tupE [] ]
                                                            ] 
                                                     | (sname,tp) <- sels ]
                                             ]
                                      | (cname,sels) <- cons ])
                             )])
       $(doE [ noBindS [| declareType (undefined :: $(return tp)) $(tupE []) |] | (_,fields) <- cons, (_,tp) <- fields ]) |]
generateDeclExpr dname (ExtrType { extrContent = Right (name,con_name,tp) }) pat ann
  = [| declareType (undefined :: $(return tp)) $(varE ann) |]

generateMangleFun :: ExtrType -> Q Dec
generateMangleFun (ExtrType { extrContent = Left cons })
  = funD 'mangle [ do
    vars <- mapM (const $ newName "f") fields
    clause [conP cname (fmap varP vars),wildP]
            (normalB (if Prelude.null vars
                      then [| L.Symbol $(stringE $ nameBase cname) |]
                      else [| L.List $ [L.Symbol $(stringE $ nameBase cname)] ++
                                       $(listE [ appsE [ [| mangle |], varE v, tupE [] ]
                                               | v <- vars ])
                            |])) []
    | (cname,fields) <- cons
    ]
generateMangleFun (ExtrType { extrContent = Right (name,con,tp) })
  = funD 'mangle [ do
    var <- newName "f"
    ann <- newName "ann"
    clause [ conP con [varP var], varP ann ] (normalB [| mangle $(varE var) $(varE ann) |]) []
    ]

generateUnmangleFun :: ExtrType -> Q Dec
generateUnmangleFun (ExtrType { extrContent = Left cons }) =
  do clauses <- genClauses cons
     let defaultPat = [WildP, WildP]
     nothing <- [|return Nothing|]
     return $ FunD 'unmangle (clauses ++ [Clause defaultPat (NormalB nothing) []])
generateUnmangleFun (ExtrType { extrContent = Right (name,con,tp) })
  = funD 'unmangle
    [do
       arg <- newName "f"
       ann <- newName "ann"
       res <- newName "r"
       clause [varP arg,varP ann] (normalB $ doE $ [ bindS (varP res) (appsE [ [| unmangle |],varE arg,varE ann ])
                                                   , noBindS [| return (case $(varE res) of { Nothing -> Nothing ; Just r -> Just ($(conE con) r) }) |]
                                                   ]) []
    ]

genClauses :: [(Name, [(Name, Type)])] -> Q [Clause]
genClauses cons = sequence $
     [do
       vars <- mapM (const $ do
                               v1 <- newName "f"
                               v2 <- newName "r"
                               return (v1,v2)) fields
       clause [(if Prelude.null fields
                then conP 'L.Symbol [litP $ stringL $ nameBase cname]
                else conP 'L.List [listP $ [conP 'L.Symbol [litP $ stringL $ nameBase cname]]++
                                           (fmap (varP . fst) vars)])
              ,wildP]
                (normalB $ doE $ [ bindS (conP 'Just [varP r]) (appsE [ [| unmangle |],varE v,tupE [] ]) | (v,r) <- vars ]++
                                 [ noBindS $ appsE [[| return |],appsE [ [| Just |],appsE $ (conE cname):(fmap (varE . snd) vars)] ]]) []
    | (cname,fields) <- cons
    ]

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
      let Just (RecC _ fields) = List.find (\con -> case con of
                                               RecC n _ -> n==name
                                               _ -> False) cons
      [| and' $ (is $exp $(constructor name)): $(listE $ catMaybes [ matches' [| $exp .# $(field f) |] pat | ((f,_,_),pat) <- Prelude.zip fields pats ]) |]
    matches' exp (RecP name pats) = Just [| and' $ (is $exp $(constructor name)): $(listE $ catMaybes [ matches' [| $exp .# $(field f) |] pat | (f,pat) <- pats ]) |]
    
