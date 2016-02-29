{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}

module Language.Haskell.Liquid.Constraint.ProofToCore where

import Prelude hiding (error)
import CoreSyn hiding (Expr, Var)
import qualified CoreSyn as H
import Language.Haskell.Liquid.Types.Errors

import Var hiding (Var)
import qualified Var as V
import CoreUtils

import Type hiding (Var)
import TypeRep

import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.WiredIn

import Language.Fixpoint.Misc
import Language.Fixpoint.Types (Constant(I))

import Prover.Types
import Language.Haskell.Liquid.Transforms.CoreToLogic ()
import qualified Data.List as L
import Data.Maybe (fromMaybe)

import Literal 

import Control.Monad.State


type HId       = CoreExpr
type HVar      = Var      HId
type HConst    = Const    HId 
type HAxiom    = Axiom    HId
type HCtor     = Ctor     HId
type HVarCtor  = VarCtor  HId
type HQuery    = Query    HId
type HInstance = Instance HId
type HProof    = Proof    HId
type HExpr     = Expr     HId

type CmbExpr = CoreExpr -> CoreExpr -> CoreExpr
type CR      = State CRSt

data CRSt = CRST { cr_fresh :: Integer
                 , cr_cmp   :: CmbExpr
                 , cr_def   :: CoreExpr
                 } 

getUnique = do 
  i <- cr_fresh <$> get 
  modify (\st -> st {cr_fresh = i + 1})
  return i 

class ToCore a where
  toCore    :: a -> CR CoreExpr
  runToCore :: Integer -> CmbExpr -> CoreExpr -> a -> CoreExpr
  runToCore i cmp def x = evalState (toCore x) (CRST i cmp def) 

instance ToCore HInstance where
  toCore i = do ci  <- toCore $ inst_axiom i
                ces <- mapM toCore $ inst_args i
                makeApp ci ces 

instance ToCore HProof where
  toCore Invalid = cr_def <$> get 
  toCore p       = (mapM toCore $ p_evidence p) >>= combineProofs

instance ToCore HAxiom where
  toCore a = toCore $ axiom_name a

instance ToCore HExpr  where
  toCore (EVar v)     = toCore v
  toCore (EApp c es)  = do ci  <- toCore c 
                           ces <- mapM toCore es 
                           makeApp ci ces 
  toCore (ECon c)     = toCore c

instance ToCore HConst where
  toCore (Const _ e) = return e

instance ToCore HCtor where
  toCore c =  toCore $ ctor_expr c

instance ToCore HVar where
  toCore v = return $ var_info v


-------------------------------------------------------------------------------
----------------  Combining Proofs --------------------------------------------
-------------------------------------------------------------------------------

-- | combineProofs :: combinator -> default expressions -> list of proofs
-- |               -> combined result

combineProofs :: [CoreExpr] -> CR CoreExpr


combineProofs []  = cr_def <$> get 
combineProofs [e] = return $ Let dictionaryBind e 
combineProofs es  = do
  (vs, bs) <- unzip <$> mapM bindExpr es 
  e <- makeCombine vs 
  return $ foldl (flip mkLet) e (bs ++ [dictionaryBind])


makeCombine [e]    = return $ H.Var e 
makeCombine (e:es) = do cmp <- cr_cmp <$> get 
                        go cmp (H.Var e) es 
  where 
    go _   e []     = return e 
    go cmp e [x]    = return $ cmp e (H.Var x)
    go cmp e (x:xs) = do (v, b) <- bindExpr (cmp e $ H.Var x)
                         e' <- go cmp (H.Var v) xs 
                         return $ mkLet b e'    
makeCombine _       = impossible Nothing "ProofToCore.makeCombine this cannot happen"

bindExpr (H.Var v) = 
  return (v, NonRec v (H.Var v))
bindExpr e = do
  v <- varANF $ exprType e 
  return (v, NonRec v e)


mkLet (NonRec _ (H.Var _)) e = e 
mkLet             b        e = foldl (flip Let) e (go b) 
  where
    go (NonRec x ex)  = let (bs, e) = grapLets [] ex in (NonRec x e:bs) 
    go b              = [b]

    grapLets acc (Let b e) = grapLets (b:acc) e 
    grapLets acc e         = (acc, e) 

varANF τ = do 
  n <- getUnique 
  return $ stringVar ("proof_anf_" ++ show n) τ 


{- 
combineProofs es = foldl (flip Let) (combine [1..] c (H.Var v) (H.Var <$> vs)) (bs ++ [dictionaryBind])
    where
      (v:vs, bs) = unzip [let v = (varANF i (exprType e)) in (v, NonRec v e)
                              | (e, i) <- zip es [1..] ]

combine _ _ e []             = e
combine _ c e' [e]           = c e' e
combine (i:uniq) c e' (e:es) = Let (NonRec v (c e' e)) (combine uniq c (H.Var v) es)
  where
     v = varCombine i (exprType $ c e' e)
combine _ _ _ _              = impossible Nothing err -- TODO: Does this case have a
   where                                              -- sane implementation?
     err = "Language.Haskell.Liquid.Constraint.ProofToCore.combine called with"
           ++ " empty first argument and non-empty fourth argument. This should"
           ++ " never happen!"
-}

-------------------------------------------------------------------------------
----------------  make Application --------------------------------------------
-------------------------------------------------------------------------------



-- | To make application we need to instantiate expressions irrelevant to logic
-- | type application and dictionaries.
-- | Then, ANF the final expression

makeApp :: CoreExpr -> [CoreExpr] -> CR CoreExpr
makeApp f es = do 
  do  (vs, bs) <- unzip <$> mapM bindExpr (ds ++ (instantiateVars vts es))
      return $ foldl (flip mkLet) (foldl App f' ((H.Var <$> vs))) (reverse bs)
  where
   vts      = resolveVs as $ zip (dropWhile isClassPred ts) (exprType <$> es)
   (as, ts) = bkArrow (exprType f)
   [f']     = instantiateVars vts [f]
   ds       = makeDictionaries dictionaryVar f'
   -- (bs, es', _) = foldl anf ([], [], [1..]) (ds ++ (instantiateVars vts <$> es))


instance Show Type where
  show (TyVarTy v) = show $ tvId v
  show (FunTy t1 t2) = show t1 ++ " -> " ++ show t2 
  show (ForAllTy a t) = "forall " ++ show a ++ " . " ++ show t
  show t           = showPpr t


instance Show (Bind CoreBndr) where
  show = showPpr

 
{- 
-- | ANF
anf :: ([CoreBind], [CoreExpr], [Int]) -> CoreExpr -> ([CoreBind], [CoreExpr], [Int])
anf (bs, es, uniq) e@(H.Var _)  = (bs, e:es, uniq)
anf (bs, es, uniq) e@(H.Type _) = (bs, e:es, uniq)
anf (bs, es, i:uniq) (App f e) = ((NonRec v (App f e')):(bs++bs'), H.Var v:es, uniq')
  where v = varANFPr i (exprType $ App f e)
        (bs', [e'], uniq') = anf ([], [], uniq) e
anf (bs, es, i:uniq) e = ((NonRec v e):bs, H.Var v:es, uniq)
  where v = varANFPr i (exprType e)
anf (bs, es, uniq) e = (bs, e:es, uniq)

-- anf (bs, es, uniq) e = traceShow "\nANF2 = \n"  (bs, e:es, uniq)
-} 
-- | Filling up dictionaries
makeDictionaries dname e = go (exprType e)
  where
    go (ForAllTy _ t) = go t
    go (FunTy tx t  ) | isClassPred tx = (makeDictionary dname tx):go t
    go _              = []

makeDictionary dname t = App (H.Var dname) (Type t)

-- | Filling up types
instantiateVars vts es = go' vts es
  where
    go' _   []     = []
    go' vts (e:es) = go vts e (exprType e) : go' (updateVts vts (exprType e))   es 

    go vts e (ForAllTy a t) = go vts (App e (Type $ fromMaybe (TyVarTy a) $ L.lookup a vts)) t
    go _   e _              = e
 
    updateVts vts (ForAllTy a t) = dropOne ((==a) . fst) (updateVts vts t)
    updateVts vts _              = vts

    dropOne _ []                 = []
    dropOne p (x:xs) | p x       = xs 
                     | otherwise = dropOne p xs 


resolveVs :: [Id] -> [(Type, Type)] -> [(Id, Type)]
resolveVs as ts = go [] as ts
  where
    go acc _   []                                     = acc 
    go acc fvs ((ForAllTy v t1, t2):ts)               = go acc (v:fvs) ((t1, t2):ts)
    go acc fvs ((t1, ForAllTy v t2):ts)               = go acc (v:fvs) ((t1, t2):ts)
    go acc fvs ((FunTy t1 t2, FunTy t1' t2'):ts)      = go acc fvs ((t1, t1'):(t2, t2'):ts)
    go acc fvs ((AppTy t1 t2, AppTy t1' t2'):ts)      = go acc fvs ((t1, t1'):(t2, t2'):ts)
    go acc fvs ((TyVarTy a, TyVarTy a'):ts) | a == a' = go acc fvs ts
    go acc fvs ((TyVarTy a, t):ts) | isFree a acc fvs = let tt = resolveVar a t acc 
                                                            acc' = [(v, substTyV (a,tt) vt) | (v, vt) <- acc]
                                                        in go ((a, tt):acc') fvs (substTyV2 (a, tt) <$> ts) 
    go acc fvs ((t, TyVarTy a):ts) | isFree a acc fvs = let tt = resolveVar a t acc 
                                                            acc' = [(v, substTyV (a,tt) vt) | (v, vt) <- acc]
                                                        in go ((a, tt):acc') fvs (substTyV2 (a, tt) <$> ts) 
    go acc fvs ((TyConApp _ cts,TyConApp _ cts'):ts)  = go acc fvs (zip cts cts' ++ ts)
    go acc fvs ((LitTy _, LitTy _):ts)                = go acc fvs ts
    go _    _   (tt:_)                                = panic Nothing $ ("cannot resolve " ++ show tt ++ (" for ") ++ show ts)

resolveVar _ t [] = t
resolveVar a t ((a', t'):ats)
  | a == a'                      = resolveVar a' t' ats
  | TyVarTy a'' <- t', a' == a  = resolveVar a'' t' ats
  | otherwise                    = resolveVar a t ats


isFree a acc fvs 
  = a `elem` fvs -- && _unbound 
  where 
    _unbound = case L.lookup a acc of 
                Just (TyVarTy b) -> isFree b acc fvs
                Just _ -> False
                Nothing -> True


substTyV2 :: (Id, Type) -> (Type, Type) -> (Type, Type)
substTyV2 su (t1, t2) = (substTyV su t1, substTyV su t2)

substTyV (a, at) = go 
  where
    go (ForAllTy a' t) | a == a'   = ForAllTy a' t
                       | otherwise = ForAllTy a' (go t)
    go (FunTy t1 t2)   = FunTy (go t1) (go t2)
    go (AppTy t1 t2)   = AppTy (go t1) (go t2)
    go (TyConApp c ts) = TyConApp c (go <$> ts)
    go (LitTy l)       = LitTy l
    go (TyVarTy v)     | v == a    = at
                       | otherwise = TyVarTy v


-------------------------------------------------------------------------------
-------------------------  HELPERS --------------------------------------------
-------------------------------------------------------------------------------
{-
varCombine i = stringVar ("proof_anf_cmb"  ++ show i)
varANF     i = stringVar ("proof_anf_bind" ++ show i)
varANFPr   i = stringVar ("proof_anf_bind_pr" ++ show i)
-}

bkArrow = go [] []
  where
    go vs ts (ForAllTy v t) = go (v:vs) ts t
    go vs ts (FunTy tx t)   = go vs (tx:ts) t
    go vs ts _              = (reverse vs, reverse ts)


