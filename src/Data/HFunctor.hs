-- |
-- Module:      Data.HFunctor
-- Copyright:   (C) 2022 Skye Soss
-- License:     BSD-style
-- Maintainer:  skyler.soss@gmail.com
-- Stability:   experimental
-- Portability: portable
--
-- This module defines functors over the category of
-- 'Functor's, where morphisms are natural transformations ('(~>)').
--
-- Due to the limited usage of such a construct in everyday programming,
-- combinators for working with such a function are not provided.

module Data.HFunctor (
      type (~>)
    -- * Higher-kinded functors
    , HFunctor (..)
    ) where

import Control.Monad.Free        (Free, hoistFree)
import Control.Monad.Free.Church (F, hoistF)
import Data.Coerce
import Data.Functor.Compose      (Compose (Compose))
import Data.Functor.Product      (Product (Pair))
import Data.Functor.Sum          (Sum (InL, InR))

-- | A natural transformation between two 'Functor's
-- This type alias does not constrain the arguments to 'Functor's,
-- though most functions in this library will do so.
type (~>) f g = forall a. f a -> g a

-- | A higher-kinded functor
class (forall f. Functor f => Functor (h f)) => HFunctor h where
    -- | Lift a natural transformation to be over a 'HFunctor'
    -- This should satisfy:
    --
    -- @
    -- 'hmap' 'id' = 'id'
    -- 'hmap' α . 'hmap' β = 'hmap' (α . β)
    -- @
    hmap :: (Functor f, Functor g) => (f ~> g) -> h f ~> h g

    -- | Default implementation for algebraic 'HFunctor's
    default hmap :: (forall a. Coercible (h f a) (h g a)) => (f ~> g) -> h f ~> h g
    hmap _ = coerce

instance Functor f => HFunctor (Sum f) where
    hmap _ (InL x) = InL x
    hmap t (InR y) = InR (t y)

instance Functor f => HFunctor (Product f) where
    hmap t (Pair x y) = Pair x (t y)

instance Functor f => HFunctor (Compose f) where
    hmap t (Compose x) = Compose (fmap t x)

instance HFunctor Free where
    hmap t = hoistFree t

instance HFunctor F where
    hmap t = hoistF t

