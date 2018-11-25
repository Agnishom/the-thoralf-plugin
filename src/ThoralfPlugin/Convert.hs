{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module ThoralfPlugin.Convert where

import Debug.Trace

import Data.Maybe ( mapMaybe, catMaybes )
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified SimpleSMT as SMT
import Data.Semigroup
import Control.Monad.Reader
import Prelude

import DynFlags
import Outputable hiding ( (<>) )

-- GHC API imports:
import GhcPlugins hiding ( (<>) )
import TcRnTypes ( Ct, ctPred )
import Class ( Class(..) )
import TcType ( Kind )
import Var ( TyVar )
import Type ( Type, PredTree (..), EqRel (..), getTyVar_maybe
            , splitTyConApp_maybe, splitFunTy_maybe
            , classifyPredType, tyVarKind )
import CoAxiom
import DataCon

-- Internal imports
import ThoralfPlugin.Encode.TheoryEncoding
import Data.Vec



-- * Data Definitions
--------------------------------------------------------------------------------


-- ** Core Types

-- | The input needed to convert 'Ct' into smt expressions.
-- We need the class for dis equality, and an encoding of a collection of
-- theories.
data EncodingData where
  EncodingData ::
    { encodeDisEq :: Class
    , encodeTheory :: TheoryEncoding
    } -> EncodingData


-- | The output of converting constraints. We have a list of converted
-- constraints as well as a list of declarations. These declarations are
-- variable declarations as well as function symbols with accompanying
-- defining assert statements.
data ConvCts where
  ConvCts ::
    { convEquals :: [(SExpr, Ct)]
    , convDeps :: [SExpr]
    , convSorts :: [String]
    } -> ConvCts


-- | Since our encoding data is passed around as a constant state, we put
-- it in a reader monad. Of course, conversion could fail, so we transform
-- from a Maybe monad.
type ConvMonad a = ReaderT EncodingData Maybe a




-- ** Basic Definitions

-- | The type of smt expressions.
type SExpr = SMT.SExpr



-- * Convert Function
--------------------------------------------------------------------------------

convert :: EncodingData -> [Ct] -> Maybe ConvCts
convert encodingData cts = runReaderT (conv cts) encodingData


conv :: [Ct] -> ConvMonad ConvCts
conv cts = do
  EncodingData disEqClass _ <- ask
  let disEquals = extractDisEq disEqClass cts
  let equals = extractEq cts
  convDisEqs <- mapSome $ fmap convPair (map fst disEquals)
  convEqs <- mapSome $ fmap convPair (map fst equals)

  let deps = mconcat $ map snd convDisEqs ++ map snd convEqs
  decls <- convertDeps deps

  let eqExprs = map (mkEqExpr . fst) convEqs
  let disEqExprs = map (mkDisEqExpr . fst) convDisEqs
  let matchingCts = map snd $ disEquals ++ equals
  --guard (length matchingCts == length (disEqExprs ++ eqExprs))
  let convPairs = zip (disEqExprs ++ eqExprs) matchingCts
  return $ ConvCts convPairs decls (convNewSorts deps)

  where

  convPair :: (Type, Type) -> ConvMonad ((SExpr, SExpr), ConvDependencies)
  convPair (t1, t2) = do
    (t1', deps1) <- convertType t1
    (t2', deps2) <- convertType t2
    let sexpr = SMT.Atom
    let convertedPair = (sexpr t1', sexpr t2')
    return (convertedPair, deps1 <> deps2)

  mkEqExpr :: (SExpr, SExpr) -> SExpr
  mkEqExpr (s1,s2) = SMT.eq s1 s2

  mkDisEqExpr :: (SExpr, SExpr) -> SExpr
  mkDisEqExpr (s1,s2) = (SMT.not $ SMT.eq s1 s2)

  mapSome :: [ConvMonad a] -> ConvMonad [a]
  mapSome xs = do
    state <- ask
    let maybeVals = map (`runReaderT` state) xs
    return $ catMaybes maybeVals

showOut x = renderWithStyle unsafeGlobalDynFlags (ppr x) (defaultUserStyle unsafeGlobalDynFlags)


-- ** Extraction
--------------------------------------------------------------------------------

extractEq :: [Ct] -> [((Type, Type), Ct)]
extractEq = mapMaybe maybeExtractTyEq

extractDisEq :: Class -> [Ct] -> [((Type, Type), Ct)]
extractDisEq cls = mapMaybe (maybeExtractTyDisEq cls) where


maybeExtractTyDisEq :: Class -> Ct -> Maybe ((Type, Type), Ct)
maybeExtractTyDisEq disEqCls ct = do
  let predTree = classifyPredType $ ctPred ct
  ClassPred class' (_: t1 : t2 : _) <- return predTree
  guard (class' == disEqCls)
  return ((t1,t2),ct)

maybeExtractTyEq :: Ct -> Maybe ((Type, Type), Ct)
maybeExtractTyEq ct = do
  let predTree = classifyPredType $ ctPred ct
  case predTree of
    EqPred NomEq t1 t2 -> return ((t1,t2),ct)
    _ -> Nothing


  {-
  return ((simpIfCan t1, simpIfCan t2), ct) where

  simpIfCan :: Type -> Type
  simpIfCan t = case coreView t of
    Just t' -> t'
    Nothing -> t -}


-- ** Converting the Dependencies
----------------------------------------

nub :: Ord a => [a] -> [a]
nub = S.toList . S.fromList

convertDeps :: ConvDependencies -> ConvMonad [SExpr]
convertDeps (ConvDeps tyvars' kdvars' decs fams' _ adts') = do
  let tyvars = nub tyvars'
  let kdvars = nub kdvars'
  let fams = L.nub fams'
  let adts = L.nub adts'
  (EncodingData _ theories) <- ask
  let mkPred = tyVarPreds theories
  let tvPreds = foldMap (fmap SMT.Atom) $ mapMaybe mkPred tyvars

  convertedTyVars <- traverse convertTyVars tyvars
  convertedFams <- traverse convertFam fams
  convertedADTs <- traverse convertPromoted adts

  let tyVarExprs  = map       fst convertedTyVars
  let tyVarKdVars = concatMap snd convertedTyVars

  let famDecs       = map       (\(a,_,_)->a) convertedFams
  let famAssertions = concatMap (\(_,b,_)->b) convertedFams
  let famKdVars     = concatMap (\(_,_,c)->c) convertedFams

  let kindVars = nub $ tyVarKdVars  ++ kdvars ++ famKdVars
  let kindExprs = map mkSMTSort kindVars
  decExprs <- convertDecs decs
  -- Order matters:
  let varExprs = kindExprs ++ convertedADTs ++ tyVarExprs ++ famDecs ++ famAssertions
  let otherExprs = decExprs ++ tvPreds
  let exprs = varExprs ++ otherExprs
  return exprs

defineType :: [String] -> SExpr
defineType sorts' = SMT.Atom $
    "(declare-datatypes () ((Type (apply (fst Type) (snd Type)) (constructor (getCon String)) "++unwords xs++")))"
  where
  sorts = nub sorts'
  xs = map f sorts
  f s = unwords ["(inc"++s,"(get"++s,s++"))"]

convertFieldType :: TyCon -> [TyVar] -> Kind -> ConvMonad String
convertFieldType otycon oargs ty = do
  case splitTyConApp_maybe ty of
    Just (tcon,args)
      | (tcon == otycon && and (zipWith eqType args $ map mkTyVarTy oargs)) ->
        return $ show $ getUnique tcon
    _ -> fst <$> convertKind ty

convertPromoted :: TyCon -> ConvMonad SExpr
convertPromoted tc =
  if isAlgTyCon tc
  then do
    let dcs = visibleDataCons $ algTyConRhs tc
        argVars = tyConTyVars tc
        args = map (\tv -> show (getUnique tv)) argVars
        name = show $ getUnique tc
        convertCon dc = do
          convertedFieldTypes <- traverse (convertFieldType tc argVars) (dataConOrigArgTys dc)
          let fieldNames = map (\n -> dname++"Field"++show n ) [1..]
              fields = zipWith (\n t -> "("++n++" "++t++")") fieldNames convertedFieldTypes
          return $ "("++unwords (dname:fields)++")"
          where
            dname = show $ getUnique dc
    convertedCons <- traverse convertCon dcs
    let defn = "(("++unwords (name:convertedCons)++"))"
        smtStr = unwords ["(declare-datatypes ("++unwords args++")", defn,")"]
    return $ SMT.Atom smtStr
  else lift $ Nothing

convertFam :: TyCon -> ConvMonad (SExpr,[SExpr],[KdVar])
convertFam fam = do
  let name = show $ getUnique fam
  let kind = tyConKind fam
  let (argtys,resty) = splitFunTys kind
  argDeps <- mapM convertKind argtys
  (res,resDeps) <- convertKind resty
  let args = unwords $ map fst argDeps
  let smtStr = SMT.Atom $ unwords ["(declare-fun",name,"(" ++ args ++ ")",res,")"]
  assertions <- convertFamEqs fam
  return (smtStr,assertions, foldMap snd argDeps ++ resDeps)

convertFamEqs :: TyCon  -> ConvMonad [SExpr]
convertFamEqs tc
  | Just bs <- isClosedSynFamilyTyConWithAxiom_maybe tc =
      map SMT.Atom <$> compileBranches (show $ getUnique tc) (fromBranches $ co_ax_branches bs)
  | otherwise = return []

compileBranches :: String -> [CoAxBranch] -> ConvMonad [String]
compileBranches funName bs = return []

-- | Converting Local Declarations
convertDecs :: [Decl] -> ConvMonad [SExpr]
convertDecs ds = do
  let assocList = map (\(Decl k v) -> (k,v)) ds
  let ourMap = M.fromList assocList
  let uniqueDecs = foldMap snd $ M.toList ourMap
  return $ map SMT.Atom uniqueDecs where

mkSMTSort :: TyVar -> SExpr
mkSMTSort tv = let
  name = (show $ getUnique tv)
  smtStr = "(declare-sort " ++ name ++ ")"
  in SMT.Atom smtStr


-- | Kind variables are just type variables
type KdVar = TyVar
convertTyVars :: TyVar -> ConvMonad (SExpr, [KdVar])
convertTyVars tv = do
  (smtSort, kindVars) <- convertKind $ tyVarKind tv
  let tvId = show $ getUnique tv
  let smtVar = "(declare-const " ++ tvId ++ " " ++ smtSort ++ ")"
  return (SMT.Atom smtVar, kindVars)




-- * Converting A Single Type
--------------------------------------------------------------------------------


-- ** Type Conversion Data
----------------------------------------

-- | A Type is converted into a string which is a valid SMT term, if the
-- dependencies are converted properly and sent to the solver before the
-- term is mentioned.
type ConvertedType = (String, ConvDependencies)

-- | These are pieces of a type that need to be converted into
-- SMT declarations or definitions in order for the converted
-- type to be well sorted or correct.
data ConvDependencies where
  ConvDeps ::
    { convTyVars :: [TyVar] -- Type variables for a known theory
    , convKdVars :: [TyVar] -- Kind variables for unknown theories
    , convDecs   :: [Decl]  -- SMT declarations specific to some converted type
    , convTyFams :: [TyCon]
    , convNewSorts :: [String]
    , convADTs   :: [TyCon]
    } -> ConvDependencies

noDeps :: ConvDependencies
noDeps = mempty

data Decl where
  Decl ::
    { decKey :: (String, String) -- ^ A unique identifier
    , localDec :: [String]       -- ^ A list of local declarations
    } -> Decl

type Hash = String

instance Semigroup ConvDependencies where
  (ConvDeps a1 b1 c1 d1 e1 f1) <> (ConvDeps a2 b2 c2 d2 e2 f2) =
    ConvDeps (a1<>a2) (b1<>b2) (c1<>c2) (d1<>d2) (e1<>e2) (f1<>f2)

instance Monoid ConvDependencies where
  mempty = ConvDeps [] [] [] [] [] []
  mappend = (<>)



-- ** Converting A Type
----------------------------------------



convertType :: Type -> ConvMonad ConvertedType
convertType ty = do
  case tyVarConv ty of
    Just (smtVar, tyvar) ->
      return  (smtVar, noDeps {convTyVars = [tyvar]})
    Nothing -> tryConvTheory ty

-- Converts types of arbitary SMT Sort to types of SMT Sort Type
convertTypeToSortType :: Type -> ConvMonad ConvertedType
convertTypeToSortType ty = do
  (t, deps) <- convertType ty
  (k, kdvars) <- convertKind $ typeKind ty
  if k == "Type"
  then return (t,deps)
  else do
    let t' = "(inc"++k++" "++t++")"
    return $ (t', deps{convKdVars = kdvars ++ convKdVars deps
                      ,convNewSorts = k:convNewSorts deps})

tyVarConv :: Type -> Maybe (String, TyVar)
tyVarConv ty = do
  tyvar <- getTyVar_maybe ty
  -- Not checking for skolems.
  -- See doc on "dumb tau variables"
  let isSkolem = True
  guard isSkolem
  let tvarStr = show $ getUnique tyvar
  return (tvarStr, tyvar)


tryConvTheory :: Type -> ConvMonad ConvertedType
tryConvTheory ty = do
  EncodingData _ theories <- ask
  let tyConvs = typeConvs theories
  case tryFns tyConvs ty of
    Just (TyConvCont tys kds cont decs) -> do
      recurTys <- vecMapAll convertType tys
      recurKds <- vecMapAll convertKind kds
      (decls, decKds) <- convDecConts decs
      let convTys = fmap fst recurTys
      let convKds = fmap fst recurKds
      let converted = cont convTys convKds
      let tyDeps = foldMap snd recurTys
      let kdVars = foldMap snd recurKds ++ decKds
      let deps = addDepParts tyDeps kdVars decls
      return (converted, deps)
    Nothing -> do
      defaultConvTy ty

addDepParts :: ConvDependencies -> [KdVar] -> [Decl] -> ConvDependencies
addDepParts (ConvDeps t k decl fams s adts) ks decls =
  ConvDeps t (k ++ ks) (decl ++ decls) fams s adts

convDecConts :: [DecCont] -> ConvMonad ([Decl], [KdVar])
convDecConts dcs = do
  decConts <- traverse convDecCont dcs
  let decls = map fst decConts
  let kdVars = concatMap snd decConts
  return (decls, kdVars) where

  convDecCont :: DecCont -> ConvMonad (Decl, [KdVar])
  convDecCont (DecCont kholes declName cont) = do
   recur <- vecMapAll convertKind kholes
   let kConvs = fmap fst recur
   let declKey = (declName, foldMap id kConvs)
   let kdVars = foldMap snd recur
   let decl = Decl declKey (cont kConvs)
   return (decl, kdVars)


defaultConvTy :: Type -> ConvMonad ConvertedType
defaultConvTy = tryFnsM [defFn, adtDef, defTyConApp, defTyApp] where
  adtDef :: Type -> ConvMonad ConvertedType
  adtDef ty = do
    (tc, tys') <- lift $ splitTyConApp_maybe ty
    dc <- lift $ isPromotedDataCon_maybe tc
    guard (isVanillaDataCon dc)
    let visibleArgs = map isVisibleTyConBinder $ tyConBinders tc
        tys = map snd $ filter fst $ zip visibleArgs tys'
    recur <- traverse convertType tys
    let defConvTys = map fst recur
    let tvars = foldMap snd recur
    let convTcon = show (getUnique dc)
    let converted = case defConvTys of
          [] -> convTcon
          _ ->  "("++unwords (convTcon:defConvTys)++")"
    return (converted, tvars{convADTs = dataConTyCon dc : convADTs tvars})

  defFn :: Type -> ConvMonad ConvertedType
  defFn ty = do
    (fn, arg) <- lift $ splitFunTy_maybe ty
    (fnStr, tv1) <- convertType fn
    (argStr, tv2) <- convertType arg
    let smtStr = fnDef fnStr argStr
    return (smtStr, tv1 <> tv2)

  fnDef :: String -> String -> String
  fnDef strIn strOut =
    "(apply (apply (constructor \"->\") " ++
      strIn ++ ") " ++ strOut ++ ")"

  defTyApp :: Type -> ConvMonad ConvertedType
  defTyApp ty = do
    (f,x) <- lift $ splitAppTy_maybe ty
    (f',xs) <- convertTypeToSortType f
    (x',ys) <- convertTypeToSortType x
    return (appDef f' x',xs<>ys)

  defTyConApp :: Type -> ConvMonad ConvertedType
  defTyConApp ty = do
    (tcon, tys) <- lift $ splitTyConApp_maybe ty
    if isTypeFamilyTyCon tcon
    then do
      -- Type families are represented as smt functions
      recur <- traverse convertType tys
      let defConvTys = map fst recur
      let tvars = foldMap snd recur
      let convTcon = show (getUnique tcon)
      let converted = "("++unwords (convTcon:defConvTys)++")"
      return (converted, tvars{convTyFams = tcon : convTyFams tvars})
    else do
      -- Type constructors are represented as (constructor ...)
      recur <- traverse convertTypeToSortType tys
      let defConvTys = map fst recur
      let tvars = foldMap snd recur
      let convTcon = "(constructor \"" ++ (show $ getUnique tcon) ++ "\")"
      let converted = foldl appDef convTcon defConvTys
      return (converted, tvars)

  appDef :: String -> String -> String
  appDef f x = "(apply " ++ f ++ " " ++ x ++ ")"


-- * Converting A Single Kind
------------------------------------------------------------------------------


-- | Converts a Kind into a String and some kind variables
--
convertKind :: Kind -> ConvMonad (String, [KdVar])
convertKind kind =
  case getTyVar_maybe kind of
    Just tvar ->
      return ((show $ getUnique tvar), [tvar])
    Nothing -> convKindTheories kind

convKindTheories :: Kind -> ConvMonad (String, [KdVar])
convKindTheories kind = do
  EncodingData _ theories <- ask
  let kindConvFns = kindConvs theories
  case tryFns kindConvFns kind of
    Just (KdConvCont kholes kContin) -> do
      recur <- vecMapAll convertKind kholes
      let convHoles = fmap fst recur
      let holeVars = foldMap snd recur
      return (kContin convHoles, holeVars)
    Nothing
      | Just (tcon,xs) <- splitTyConApp_maybe kind
      , isAlgTyCon tcon -> do
          let name = show $ getUnique tcon
          args' <- traverse convertKind xs
          let args = map fst args'
          case args of
            [] -> return (name, concatMap snd args')
            _ -> return (("("++unwords (name:args)++")"), concatMap snd args')

      | otherwise -> return ("Type", []) -- Kind defaulting


-- * A Common Helper Function

-- | In order, try the functions.
tryFns :: [a -> Maybe b] -> a -> Maybe b
tryFns [] _ = Nothing
tryFns (f:fs) a = case f a of
  Nothing -> tryFns fs a
  Just b -> Just b
tryFnsM :: [a -> ConvMonad b] -> a -> ConvMonad b
tryFnsM [] _ = lift Nothing
tryFnsM (f:fs) a = do
  env <- ask
  case runReaderT (f a) env of
    Nothing -> tryFnsM fs a
    Just b -> lift $ Just b




