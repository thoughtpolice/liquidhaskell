
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--autoproofs"      @-}
{- LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module Monoid where
import Axiomatize
import Equational

import Prelude hiding (mappend, mempty)

data L a = N | C a (L a)

instance Eq a => Eq (L a) where
  N == N                 = True
  (C x xs) == (C x' xs') = x == x' && xs == xs'


{- 
Monoid Laws :
mempty-left ∀ x . mappend mempty x ≡ x
mempty-right ∀ x . mappend x  mempty ≡ x
mappend-assoc ∀ x y z . mappend (mappend x y) z ≡ mappend x (mappend y z)
-}

{-@ axiomatize mempty @-}
$(axiomatize
  [d| mempty :: L a
      mempty = N
    |])

{-@ axiomatize mappend @-}
$(axiomatize
  [d| mappend :: L a -> L a -> L a 
      mappend  N       ys = ys
      mappend (C x xs) ys = C x (mappend xs ys) 
    |])

prop_mempty_left         :: Eq a => L a -> Proof 
{-@ prop_mempty_left     :: x:L a -> {v: Proof | mappend mempty x == x } @-}
prop_mempty_left x       = cases 1 (mappend mempty x == x)

prop_mempty_right        :: Eq a => L a -> Proof 
{-@ prop_mempty_right    :: xs:L a -> {v: Proof | mappend xs mempty == xs } @-}
prop_mempty_right xs     = cases 2 (mappend xs mempty == xs)

prop_mempty_assoc        :: Eq a => L a -> L a -> L a -> Proof 
{-@ prop_mempty_assoc    :: x:L a -> y:L a -> z:L a 
                         -> {v: Proof | mappend (mappend x y) z == mappend x (mappend y z)} @-}
prop_mempty_assoc x y z  = cases 2 (mappend (mappend x y) z == mappend x (mappend y z))


{-@ data L [llen] @-}
{-@ invariant {v: L a | llen v >= 0} @-}

{-@ measure llen @-}
llen :: L a -> Int
llen N = 0
llen (C x xs) = 1 + llen xs

