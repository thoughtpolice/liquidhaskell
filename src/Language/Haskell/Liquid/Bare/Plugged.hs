{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.Plugged (
    makePluggedSigs
  , makePluggedAsmSigs
  , makePluggedDataCons
  ) where

import Prelude hiding (error)
import DataCon
import Module
import Name
import NameSet
import TyCon
import Type (expandTypeSynonyms)
import Var


import Control.Monad
import Control.Monad.Error
import Data.Generics.Aliases (mkT)
import Data.Generics.Schemes (everywhere)
import Data.Monoid

import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Types.Names (dummySymbol)
import Language.Fixpoint.Types (mapPredReft, pAnd, conjuncts, TCEmb)
import qualified Language.Fixpoint.Types as F 

import Language.Haskell.Liquid.GHC.Misc (sourcePos2SrcSpan, typeUniqueString)
import Language.Haskell.Liquid.Types.RefType (addTyConInfo, ofType, rVar, rTyVar, subts, toType, uReft)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.Errors (panic, impossible)
import Language.Haskell.Liquid.Misc (zipWithDefM)

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Misc

import Data.Maybe (fromMaybe)
import qualified Data.List as L 


makePluggedSigs name embs tcEnv exports sigs
  = forM sigs $ \(x,t) -> do
      let τ = expandTypeSynonyms $ varType x
      let r = maybeTrue x name exports
      (x,) <$> plugHoles embs tcEnv x r τ t

makePluggedAsmSigs embs tcEnv sigs
  = forM sigs $ \(x,t) -> do
      let τ = expandTypeSynonyms $ varType x
      let r = const killHoles
      (x,) <$> plugHoles embs tcEnv x r τ t

makePluggedDataCons embs tcEnv dcs
  = forM dcs $ \(dc, Loc l l' dcp) -> do
       let (das, _, dts, dt) = dataConSig dc
       tyArgs <- zipWithM (\t1 (x,t2) ->
                   (x,) . val <$> plugHoles embs tcEnv (dataConName dc) (const killHoles) t1 (Loc l l' t2))
                 dts (reverse $ tyArgs dcp)
       tyRes <- val <$> plugHoles embs tcEnv (dataConName dc) (const killHoles) dt (Loc l l' (tyRes dcp))
       return (dc, Loc l l' dcp { freeTyVars = map rTyVar das
                                , freePred   = map (subts (zip (freeTyVars dcp) (map (rVar :: TyVar -> RSort) das))) (freePred dcp)
                                , tyArgs     = reverse tyArgs
                                , tyRes      = tyRes})

plugHoles tce tyi x f t (Loc l l' st)
  = do tyvsmap <- case runMapTyVars (mapTyVars (toType rt') st'') initvmap of
                    Left e -> throwError e
                    Right s -> return $ vmap s
       let su    = [(y, rTyVar x) | (x, y) <- tyvsmap]
           st''' = subts su st''
           ps'   = fmap (subts su') <$> ps
           su'   = [(y, RVar (rTyVar x) ()) | (x, y) <- tyvsmap] :: [(RTyVar, RSort)]
       Loc l l' . mkArrow αs ps' (ls1 ++ ls2) [] . fmap (fmap (substvsref tyvsmap)) . makeCls cs' <$> go rt' st'''
  where
    (αs, _, ls1, rt)  = bkUniv (ofType t :: SpecType)
    (cs, rt')         = bkClass rt

    (_, ps, ls2, st') = bkUniv st
    (_, st'')         = bkClass st'
    cs'               = [(dummySymbol, RApp c t [] mempty) | (c,t) <- cs]
    initvmap          = initMapSt $ ErrMismatch lqSp (pprint x) (pprint t) (pprint $ toType st) hsSp
    hsSp              = getSrcSpan x
    lqSp              = sourcePos2SrcSpan l l'

    go :: SpecType -> SpecType -> BareM SpecType
    go t                (RHole r)          = return $ (addHoles t') { rt_reft = f t r }
      where
        t'       = everywhere (mkT $ addRefs tce tyi) t
        addHoles = everywhere (mkT $ addHole)
        -- NOTE: make sure we only add holes to RVar and RApp (NOT RFun)
        addHole :: SpecType -> SpecType
        addHole t@(RVar v _)       = RVar v (f t (uReft ("v", hole)))
        addHole t@(RApp c ts ps _) = RApp c ts ps (f t (uReft ("v", hole)))
        addHole t                  = t

    go (RVar _ _)       v@(RVar _ _)       = return v
    go (RFun _ i o _)   (RFun x i' o' r)   = RFun x <$> go i i' <*> go o o' <*> return r
    go (RAllT _ t)      (RAllT a t')       = RAllT a <$> go t t'
    go (RAllT a t)      t'                 = RAllT a <$> go t t'
    go t                (RAllP p t')       = RAllP p <$> go t t'
    go t                (RAllS s t')       = RAllS s <$> go t t'
    go t                (RAllE b a t')     = RAllE b a <$> go t t'
    go t                (REx b x t')       = REx b x <$> go t t'
    go t                (RRTy e r o t')    = RRTy e r o <$> go t t'
    go (RAppTy t1 t2 _) (RAppTy t1' t2' r) = RAppTy <$> go t1 t1' <*> go t2 t2' <*> return r
    -- zipWithDefM: if ts and ts' have different length then the liquid and haskell types are different.
    -- keep different types for now, as a pretty error message will be created at Bare.Check
    go (RApp _ ts _ _)  (RApp c ts' p r)   = RApp c <$> (zipWithDefM go ts ts') <*> return p <*> return r
    -- If we reach the default case, there's probably an error, but we defer
    -- throwing it as checkGhcSpec does a much better job of reporting the
    -- problem to the user.
    go _                st                 = return st

    makeCls cs t              = foldr (uncurry rFun) t cs


substvsref tvs' (F.Reft (v, p)) = F.Reft (v, go p)
  where
    tvs = [(F.symbol y, F.symbol $ typeUniqueString x) | (x, y)<- tvs']

    go (F.ELam f (x, t) e) = F.ELam f (x, go' t) $ go e 
    go (F.EApp e1 e2)    = F.EApp (go e1) (go e2)
    go (F.ENeg e)        = F.ENeg $ go e 
    go (F.EBin b e1 e2)  = F.EBin b (go e1) (go e2)
    go (F.EIte e1 e2 e3) = F.EIte (go e1) (go e2) (go e3)
    go (F.ECst e s)      = F.ECst (go e) (go' s)
    go (F.ETApp e s)     = F.ETApp (go e) (go' s)
    go (F.ETAbs e s)     = F.ETAbs (go e) s 
    go (F.PAnd es)       = F.PAnd (go <$> es)
    go (F.POr  es)       = F.POr  (go <$> es)
    go (F.PNot e)        = F.PNot (go e)
    go (F.PIff e1 e2)    = F.PIff (go e1) (go e2)
    go (F.PImp e1 e2)    = F.PImp (go e1) (go e2)
    go (F.PAtom b e1 e2) = F.PAtom b (go e1) (go e2)
    go (F.PAll bs e)     = F.PAll   ((\(x, s) -> (x, go' s)) <$> bs) (go e)
    go (F.PExist bs e)   = F.PExist ((\(x, s) -> (x, go' s)) <$> bs) (go e)
    go e                 = e 

    go' (F.FObj  s)     = F.FObj $ fromMaybe s (L.lookup s tvs) 
    go' (F.FFunc s1 s2) = F.FFunc (go' s1) (go' s2)
    go' (F.FAbs i s)    = F.FAbs i $ go' s 
    go' (F.FApp s1 s2)  = F.FApp (go' s1) (go' s2)
    go'  t              = t 


addRefs :: TCEmb TyCon
     -> M.HashMap TyCon RTyCon
     -> SpecType
     -> SpecType
addRefs tce tyi (RApp c ts _ r) = RApp c' ts ps r
  where
    RApp c' _ ps _ = addTyConInfo tce tyi (RApp c ts [] r)
addRefs _ _ t  = t


maybeTrue :: NamedThing a => a -> ModName -> NameSet -> SpecType -> RReft -> RReft
maybeTrue x target exports t r
  | not (isFunTy t) && (isInternalName name || inTarget && notExported)
  = r
  | otherwise
  = killHoles r
  where
    inTarget    = moduleName (nameModule name) == getModName target
    name        = getName x
    notExported = not $ getName x `elemNameSet` exports

-- killHoles r@(U (Reft (v, rs)) _ _) = r { ur_reft = Reft (v, filter (not . isHole) rs) }

killHoles ur = ur { ur_reft = tx $ ur_reft ur }
  where
    tx r = {- traceFix ("killholes: r = " ++ showFix r) $ -} mapPredReft dropHoles r
    dropHoles    = pAnd . filter (not . isHole) . conjuncts
