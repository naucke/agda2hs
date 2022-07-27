module Agda2Hs.Compile.Function where

import Control.Arrow ( (>>>), (***), (&&&), first, second )
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader

import Data.Generics ( mkT, everywhere, listify, extT, everything, mkQ, Data )
import Data.List
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Maybe
import Data.Map ( Map )
import qualified Data.Text as Text
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps

import Agda.Syntax.Common hiding ( Ranged )
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding ( withCurrentModule )

import Agda.TypeChecking.CheckInternal ( infer )
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.Conversion ( equalTerm )
import Agda.TypeChecking.InstanceArguments ( findInstance )
import Agda.TypeChecking.Level ( isLevelType )
import Agda.TypeChecking.MetaVars ( newInstanceMeta )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records
import Agda.TypeChecking.Sort ( ifIsSort )

import Agda.Utils.Lens
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Functor

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Term
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.TypeDefinition
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils
import Agda2Hs.Pragma

isSpecialPat :: QName -> Maybe (ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ()))
isSpecialPat = prettyShow >>> \ case
  "Haskell.Prim.Tuple.Tuple._∷_" -> Just tuplePat
  _ -> Nothing

tuplePat :: ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ())
tuplePat cons i ps = do
  let p = ConP cons i ps
      err = sep [ text "Tuple pattern"
                , nest 2 $ prettyTCM p
                , text "does not have a known size." ]
  xs <- makeListP' "Haskell.Prim.Tuple.Tuple.[]" "Haskell.Prim.Tuple.Tuple._∷_" err p
  qs <- mapM compilePat xs
  return $ Hs.PTuple () Hs.Boxed qs

compileFun :: Definition -> C [Hs.Decl ()]
compileFun d = do
  locals <- takeWhile (isAnonymousModuleName . qnameModule . fst)
          . dropWhile ((<= defName d) . fst)
          . sortDefs <$> liftTCM curDefs
  compileFun' d locals

compileFun' :: Definition -> LocalDecls -> C [Hs.Decl ()]
compileFun' def@(Defn {..}) locals = do
  let m = qnameModule defName
      n = qnameName defName
      x = hsName $ prettyShow n
      go = foldM $ \(ds, ms) -> compileClause ds x >=> return . fmap (ms `snoc`)
  reportSDoc "agda2hs.compile" 6 $ text "compiling function: " <+> prettyTCM defName
  withCurrentModule m $ setCurrentRange (nameBindingSite n) $ do
    ifM (endsInSort defType) (compileTypeDef x def locals) $ do
      ty <- compileType (unEl defType)
      cs <- snd <$> go (locals, []) funClauses
      return [Hs.TypeSig () [x] ty, Hs.FunBind () cs]
  where
    Function{..} = theDef

    endsInSort t = do
      TelV tel b <- telView t
      addContext tel $ ifIsSort b (\_ -> return True) (return False)


compileClause :: LocalDecls -> Hs.Name () -> Clause -> C (LocalDecls, Hs.Match ())
compileClause locals x c@Clause{clauseTel = tel, namedClausePats = ps', clauseBody = body} = do
  addContext (KeepNames tel) $ liftTCM1 localScope $ do
    scopeBindPatternVariables ps'
    ps <- compilePats ps'
    -- Compile rhs and its @where@ clauses, making sure that:
    --   * inner modules get instantiated
    --   * references to inner modules get un-qualified (and instantiated)
    let localUses = nub $ listify (`elem` map fst locals) body
        belongs q@(QName m _) (QName m0 _) =
          ((prettyShow m0 ++ "._") `isPrefixOf` prettyShow m) && (q `notElem` localUses)
        splitDecls :: LocalDecls -> ([(Definition, LocalDecls)], LocalDecls)
        splitDecls ds@((q,child):rest)
          | any ((`elem` localUses) . fst) ds
          , (grandchildren, outer) <- span ((`belongs` q) . fst) rest
          , (groups, rest') <- splitDecls outer
          = ((child, grandchildren) : groups, rest')
          | otherwise = ([], ds)
        splitDecls [] = ([], [])
        (children, locals') = splitDecls locals

        args   = teleArgs tel
        argLen = length args


        -- 1. apply current telescope to inner definitions
        children' = mapDefs (`applyNoBodies` args) children
          where mapDefs f = map (f *** map (second f))

        -- 2. shrink calls to inner modules (unqualify + partially apply module parameters)
        localNames = concatMap (\(d,ds) -> defName d : map fst ds) children
        shrinkLocalDefs t | Def q es <- t, q `elem` localNames
                          = Def (qualify_ $ qnameName q) (drop argLen es)
                          | otherwise = t
        (body', children'') = mapTerms (everywhere $ mkT shrinkLocalDefs) (body, children')
          where mapTerms f = fmap f *** (map (mapDef f *** map (second (mapDef f))))

    body' <- fromMaybe (hsError $ pp x ++ ": impossible") <$> mapM compileTerm body'
    whereDecls <- concat <$> mapM (uncurry compileFun') children''

    let rhs = Hs.UnGuardedRhs () body'
        whereBinds | null whereDecls = Nothing
                   | otherwise       = Just $ Hs.BDecls () whereDecls
        match = case (x, ps) of
          (Hs.Symbol{}, p : q : ps) -> Hs.InfixMatch () p x (q : ps) rhs whereBinds
          _                         -> Hs.Match () x ps rhs whereBinds
    return (locals', match)

scopeBindPatternVariables :: NAPs -> C ()
scopeBindPatternVariables = mapM_ (scopeBind . namedArg)
  where
    scopeBind :: DeBruijnPattern -> C ()
    scopeBind = \ case
      VarP o i | PatOVar x <- patOrigin o -> liftTCM $ bindVariable LambdaBound (nameConcrete x) x
               | otherwise                -> return ()
      ConP _ _ ps -> scopeBindPatternVariables ps
      DotP{}      -> return ()
      LitP{}      -> return ()
      ProjP{}     -> return ()
      IApplyP{}   -> return ()
      DefP{}      -> return ()

compilePats :: NAPs -> C [Hs.Pat ()]
compilePats ps = mapM (compilePat . namedArg) $ filter keepArg ps

compilePat :: DeBruijnPattern -> C (Hs.Pat ())
compilePat p@(VarP o _)
  | PatOWild <- patOrigin o = return $ Hs.PWildCard ()
  | otherwise               = Hs.PVar () . hsName <$> showTCM p
compilePat (ConP h i ps)
  | Just semantics <- isSpecialPat (conName h) = setCurrentRange h $ semantics h i ps
compilePat (ConP h _ ps) = do
  ps <- compilePats ps
  c <- hsQName (conName h)
  return $ pApp c ps
-- TODO: LitP
compilePat (ProjP _ q) = do
  let x = hsName $ prettyShow q
  return $ Hs.PVar () x
compilePat p = genericDocError =<< text "bad pattern:" <?> prettyTCM p