{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.Haskell.Liquid.Constraint.Fresh (Freshable(..)) where

import           Prelude                hiding (error)


import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Misc  (single)
import           Language.Haskell.Liquid.Types

class (Applicative m, Monad m) => Freshable m a where
  fresh   :: m a
  true    :: a -> m a
  true    = return
  refresh :: a -> m a
  refresh = return

instance Freshable m Integer => Freshable m Symbol where
  fresh = tempSymbol "x" <$> fresh

instance Freshable m Integer => Freshable m Expr where
  fresh  = kv <$> fresh
    where
      kv = (`PKVar` mempty) . intKvar

instance Freshable m Integer => Freshable m [Expr] where
  fresh = single <$> fresh

instance Freshable m Integer => Freshable m Reft where
  fresh                = panic Nothing "fresh Reft"
  true    (Reft (v,_)) = return $ Reft (v, mempty)
  refresh (Reft (_,_)) = (Reft .) . (,) <$> freshVV <*> fresh
    where
      freshVV          = vv . Just <$> fresh

instance Freshable m Integer => Freshable m RReft where
  fresh             = panic Nothing "fresh RReft"
  true (MkUReft r _ s)    = MkUReft <$> true r    <*> return mempty <*> true s
  refresh (MkUReft r _ s) = MkUReft <$> refresh r <*> return mempty <*> refresh s

instance Freshable m Integer => Freshable m Strata where
  fresh      = (:[]) . SVar <$> fresh
  true []    = fresh
  true s     = return s
  refresh [] = fresh
  refresh s  = return s

instance (Freshable m Integer, Freshable m r, Reftable r ) => Freshable m (RRType r) where
  fresh   = panic Nothing "fresh RefType"
  refresh = refreshRefType
  true    = trueRefType

-----------------------------------------------------------------------------------------------
trueRefType :: (Freshable m Integer, Freshable m r, Reftable r) => RRType r -> m (RRType r)
-----------------------------------------------------------------------------------------------
trueRefType (RAllT α t)
  = RAllT α <$> true t

trueRefType (RAllP π t)
  = RAllP π <$> true t

trueRefType (RFun _ t t' _)
  = rFun <$> fresh <*> true t <*> true t'

trueRefType (RApp c ts _  _) | isClass c
  = rRCls c <$> mapM true ts

trueRefType (RApp c ts rs r)
  = RApp c <$> mapM true ts <*> mapM trueRef rs <*> true r

trueRefType (RAppTy t t' _)
  = RAppTy <$> true t <*> true t' <*> return mempty

trueRefType (RVar a r)
  = RVar a <$> true r

trueRefType (RAllE y ty tx)
  = do y'  <- fresh
       ty' <- true ty
       tx' <- true tx
       return $ RAllE y' ty' (tx' `subst1` (y, EVar y'))

trueRefType (RRTy e o r t)
  = RRTy e o r <$> trueRefType t

trueRefType t
  = return t

trueRef :: (Reftable r, Freshable f r, Freshable f Integer)
        => Ref τ (RType RTyCon RTyVar r) -> f (Ref τ (RRType r))
trueRef (RProp _ (RHole _)) = panic Nothing "trueRef: unexpected RProp _ (RHole _))"
trueRef (RProp s t) = RProp s <$> trueRefType t



-----------------------------------------------------------------------------------------------
refreshRefType :: (Freshable m Integer, Freshable m r, Reftable r) => RRType r -> m (RRType r)
-----------------------------------------------------------------------------------------------
refreshRefType (RAllT α t)
  = RAllT α <$> refresh t

refreshRefType (RAllP π t)
  = RAllP π <$> refresh t

refreshRefType (RFun b t t' _)
  | b == dummySymbol = rFun <$> fresh <*> refresh t <*> refresh t'
  | otherwise        = rFun     b     <$> refresh t <*> refresh t'

refreshRefType (RApp rc ts _ _) | isClass rc
  = return $ rRCls rc ts

refreshRefType (RApp rc ts rs r)
  = RApp rc <$> mapM refresh ts <*> mapM refreshRef rs <*> refresh r

refreshRefType (RVar a r)
  = RVar a <$> refresh r

refreshRefType (RAppTy t t' r)
  = RAppTy <$> refresh t <*> refresh t' <*> refresh r

refreshRefType (RAllE y ty tx)
  = do y'  <- fresh
       ty' <- refresh ty
       tx' <- refresh tx
       return $ RAllE y' ty' (tx' `subst1` (y, EVar y'))

refreshRefType (RRTy e o r t)
  = RRTy e o r <$> refreshRefType t

refreshRefType t
  = return t

refreshRef :: (Reftable r, Freshable f r, Freshable f Integer)
           => Ref τ (RType RTyCon RTyVar r) -> f (Ref τ (RRType r))
refreshRef (RProp _ (RHole _)) = panic Nothing "refreshRef: unexpected (RProp _ (RHole _))"
refreshRef (RProp s t) = RProp <$> mapM freshSym s <*> refreshRefType t

freshSym :: Freshable f a => (t, t1) -> f (a, t1)
freshSym (_, t)        = (, t) <$> fresh
