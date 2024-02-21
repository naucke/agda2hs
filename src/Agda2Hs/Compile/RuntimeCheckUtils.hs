module Agda2Hs.Compile.RuntimeCheckUtils where

import Data.List

import qualified Language.Haskell.Exts.Syntax as Hs

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Internal

import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Pretty

import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

suffix = "AfterRtc"

lookupRtc :: String -> [(ArgName, Type)] -> C Type
lookupRtc n tel = case lookup n tel of
  Just ty -> return ty
  Nothing -> genericDocError =<< text ("Parameter " ++ n ++ " was specified as runtime check, but could not be found")

decify :: Type -> C Type
decify t = do
  dec <- resolveStringName "Haskell.Extra.Dec.Dec"
  level <- liftTCM newLevelMeta
  let vArg = defaultArg
      hArg = setHiding Hidden . vArg
  return $ t { unEl = Def dec $ map Apply [hArg $ Level level, vArg $ unEl t]}

createRtc :: Hs.Name () -> Int -> [((String, [Int]), String)] -> Hs.Decl ()
createRtc n len chks = Hs.FunBind () $ map (createRtc' n len) chks

createRtc' :: Hs.Name () -> Int -> ((String, [Int]), String) -> Hs.Match ()
createRtc' n len ((chk, pos), err) =
  let chk' = eApp (hsVar chk) $ map (hsVar . aify) pos
      msg  = "Runtime check failed: " ++ err
   in Hs.Match
        ()
        n
        (map (Hs.PVar () . hsName) vars)
        ( Hs.GuardedRhss
            ()
            [ Hs.GuardedRhs () [Hs.Qualifier () chk'] $
                eApp (hsVar $ name ++ suffix) (map hsVar vars),
              Hs.GuardedRhs () [Hs.Qualifier () $ Hs.App () (hsVar "not") chk'] $
                Hs.App () (hsVar "error") $
                  Hs.Lit () $
                    Hs.String () msg msg
            ]
        )
        Nothing
  where
    name = case n of
      Hs.Ident _ s -> s
      Hs.Symbol _ s -> s
    aify n = "a" ++ show n
    vars = map aify [0 .. len]

rtcDeferName :: Hs.Name () -> C (Hs.Name ())
rtcDeferName name =
  let (constructor, l, n) = case name of
        Hs.Ident l n -> (Hs.Ident, l, n)
        Hs.Symbol l n -> (Hs.Symbol, l, n)
      rtcDefer = n ++ suffix in
  testResolveStringName rtcDefer >>= \case
    Just _ -> genericDocError =<< text ("Illegal function name " ++ rtcDefer ++ ", reserved for runtime checks")
    Nothing -> return $ constructor l rtcDefer

rtcDeferMatch :: Hs.Match () -> C (Hs.Match ())
rtcDeferMatch m = do
  let n = case m of
        Hs.Match _ n _ _ _ -> n
        Hs.InfixMatch _ _ n _ _ _ -> n
  rtc <- rtcDeferName n
  return $ case m of
    Hs.Match l _ ps rhs b -> Hs.Match l rtc ps rhs b
    Hs.InfixMatch l p _ ps rhs b -> Hs.InfixMatch l p rtc ps rhs b

argPlaces :: Type -> [Int]
argPlaces ty = reverse $ case unEl ty of
  Def _ es ->
    map
      ( \case
          Apply a -> case unArg a of
            Var n _ -> n
      )
      es

argCount :: Hs.Type () -> Int
argCount ty =
  length
    ( unfoldr
        ( \case
            Hs.TyFun _ _ t' -> Just ((), t')
            _ -> Nothing
        )
        ty
    )
    - 1
