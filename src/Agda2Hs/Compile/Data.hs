module Agda2Hs.Compile.Data where

import qualified Language.Haskell.Exts as Hs

import Control.Monad ( when )
import Data.Either ( partitionEithers )
import Data.List ( intercalate )
import Data.Maybe ( mapMaybe )
import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Monad ( ifM )
import Agda.Utils.Tuple ( mapSnd )

import Agda2Hs.Compile.RuntimeCheckUtils
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

checkNewtype :: Hs.Name () -> [Hs.QualConDecl ()] -> C ()
checkNewtype name cs = do
  checkSingleElement name cs "Newtype must have exactly one constructor in definition"
  case head cs of
    Hs.QualConDecl () _ _ (Hs.ConDecl () cName types) -> checkNewtypeCon cName types

compileData :: AsNewType -> [Hs.Deriving ()] -> Definition -> C ([Hs.Decl ()], [Hs.Decl ()])
compileData newtyp ds def = do
  let prettyName = prettyShow $ qnameName $ defName def
      d = hsName prettyName
  checkValidTypeName d
  let Datatype{dataPars = n, dataIxs = numIxs, dataCons = cs} = theDef def
  TelV tel t <- telViewUpTo n (defType def)
  reportSDoc "agda2hs.data" 10 $ text "Datatype telescope:" <+> prettyTCM tel
  allIndicesErased t
  let params = teleArgs tel
  addContext tel $ do
    binds <- compileTeleBinds tel
    chkdCs <- mapM (compileConstructor params) cs

    chks <- ifM (emitsRtc $ defName def) (do
      let (noneErased, chks) = mapSnd concat $ partitionEithers $ mapMaybe snd chkdCs
      -- Always export data type name
      tellNoErased $ prettyName ++ "(" ++ intercalate ", " noneErased ++ ")"
      return chks)
      $ return []

    let cs = map fst chkdCs
        hd = foldl (Hs.DHApp ()) (Hs.DHead () d) binds

    let target = if newtyp then Hs.NewType () else Hs.DataType ()

    when newtyp (checkNewtype d cs)

    return ([Hs.DataDecl () target Nothing hd cs ds], chks)
  where
    allIndicesErased :: Type -> C ()
    allIndicesErased t = reduce (unEl t) >>= \case
      Pi dom t -> compileDomType (absName t) dom >>= \case
        DomDropped      -> allIndicesErased (unAbs t)
        DomType{}       -> genericDocError =<< text "Not supported: indexed datatypes"
        DomConstraint{} -> genericDocError =<< text "Not supported: constraints in types"
        DomForall{}     -> genericDocError =<< text "Not supported: indexed datatypes"
      _ -> return ()

compileConstructor :: [Arg Term] -> QName -> C (Hs.QualConDecl (),
{- optional exportable cons/checker function -} Maybe (Either String [Hs.Decl ()]))
compileConstructor params c = do
  reportSDoc "agda2hs.data.con" 15 $ text "compileConstructor" <+> prettyTCM c
  reportSDoc "agda2hs.data.con" 20 $ text "  params = " <+> prettyTCM params
  ty <- (`piApplyM` params) . defType =<< getConstInfo c
  reportSDoc "agda2hs.data.con" 20 $ text "  ty = " <+> prettyTCM ty
  TelV tel _ <- telView ty
  let conString = prettyShow $ qnameName c
      conName = hsName conString
  smartQName <- smartConstructor c True

  checkValidConName conName
  args <- compileConstructorArgs tel
  chk <- ifM (emitsRtc c) (do
    sig <- Hs.TypeSig () [hsName $ prettyShow $ qnameName smartQName] <$> compileType (unEl ty)
    -- export constructor name when no erased, provide signature for smart constructor if it exists
    checkRtc tel smartQName (hsVar conString) >>= \case
      NoneErased -> return $ Just $ Left conString
      Uncheckable -> return Nothing
      Checkable ds -> return $ Just $ Right $ sig : ds)
    $ return Nothing

  return (Hs.QualConDecl () Nothing Nothing $ Hs.ConDecl () conName args, chk)

compileConstructorArgs :: Telescope -> C [Hs.Type ()]
compileConstructorArgs EmptyTel = return []
compileConstructorArgs (ExtendTel a tel) = compileDomType (absName tel) a >>= \case
  DomType s hsA     -> do
    ty <- addTyBang s hsA
    (ty :) <$> underAbstraction a tel compileConstructorArgs
  DomConstraint hsA -> genericDocError =<< text "Not supported: constructors with class constraints"
  DomDropped        -> underAbstraction a tel compileConstructorArgs
  DomForall{}       -> __IMPOSSIBLE__
