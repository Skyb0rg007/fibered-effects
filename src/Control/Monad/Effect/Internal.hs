{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Control.Monad.Effect.Internal (
    -- * Typeclasses
      Algebraic (..)
    , All
    , mapAll
    , (:<) (..)
    -- * Datatypes
    , Sum (..)
    -- * Re-exports
    , HFunctor (..)
    , type (~>)
    ) where

import Data.HFunctor         (HFunctor (..), type (~>))
import Data.Coerce           (Coercible, coerce)
import Data.Kind             (Constraint, Type)

-- | An Algebraic 'HFunctor' doesn't utilize its 'Functor' parameter
class HFunctor h => Algebraic h where
    -- | A witness for the above fact
    -- 'hvoid' . 'hvoid' == 'id'
    hvoid :: h f ~> h g

    default hvoid :: (forall a. Coercible (h f a) (h g a)) => h f ~> h g
    hvoid = coerce

{-

-- | Free 'Monad' over a 'HFunctor'
data HFree h a
    = HPure a
    | HFree (h (HFree h) (HFree h a))

instance HFunctor h => Functor (HFree h) where
    fmap f (HPure a) = HPure (f a)
    fmap f (HFree h) = HFree (fmap (fmap f) h)

instance HFunctor h => Applicative (HFree h) where
    pure = HPure
    (<*>) = ap

instance HFunctor h => Monad (HFree h) where
    HPure a >>= k = k a
    HFree h >>= k = HFree (fmap (>>= k) h)

-- | Base 'HFunctor' for 'HFree'
data HFreeH h g a
    = HPureH a
    | HFreeH (h g (g a))

instance (HFunctor h, Functor g) => Functor (HFreeH h g) where
    fmap f (HPureH a) = HPureH (f a)
    fmap f (HFreeH h) = HFreeH (fmap (fmap f) h)

instance HFunctor h => HFunctor (HFreeH h) where
    hmap _ (HPureH a) = HPureH a
    hmap t (HFreeH h) = HFreeH (hmap t . fmap t $ h)

hcata :: forall h g. (HFunctor h, Functor g) => (HFreeH h g ~> g) -> HFree h ~> g
hcata alg = go
    where
        go :: HFree h ~> g
        go (HPure a) = alg (HPureH a)
        go (HFree h) = alg (hmap go (HFreeH h))

-- | Base 'Functor' for 'HFree'
data HFreeF h a b
    = HPureF a
    | HFreeF (h (Const Void) b)

instance HFunctor h => Functor (HFreeF h a) where
    fmap _ (HPureF a) = HPureF a
    fmap f (HFreeF h) = HFreeF (fmap f h)

type instance Base (HFree h a) = HFreeF h a

instance Algebraic h => Recursive (HFree h a) where
    project (HPure a) = HPureF a
    project (HFree h) = HFreeF (hvoid h)

instance Algebraic h => Corecursive (HFree h a) where
    embed (HPureF a) = HPure a
    embed (HFreeF h) = HFree (hvoid h)
-}

-- Sum type
type Sum :: [(Type -> Type) -> Type -> Type] -> (Type -> Type) -> Type -> Type
data Sum r f a where
    This :: h f a -> Sum (h ': r) f a
    That :: Sum r f a -> Sum (h ': r) f a

type AllF :: (k -> Constraint) -> [k] -> Constraint
type family AllF c xs where
    AllF _ '[] = ()
    AllF c (x ': xs) = (c x, AllF c xs)

class Top a
instance Top a

class (AllF c xs, All Top xs) => All c xs where
    cpara :: r '[] -> (forall y ys. (c y, All c ys) => r ys -> r (y ': ys)) -> r xs

instance All c '[] where
    cpara n _ = n

instance (c x, All c xs) => All c (x ': xs) where
    cpara n c = c (cpara @c n c)

data MapAll c r where
    MapAll :: All c r => MapAll c r

-- | Witness the fact that superclass constraints can be lifted through 'All'
-- @
-- -- `All HFunctor r` is unnecesary, but GHC needs help to prove it
-- hvoid :: (All HFunctor r, All Algebraic r) => Sum r f ~> Sum r g
-- -- Version without unnecessary constraint
-- hvoid' :: forall r f g. All Algebraic r => Sum r f ~> Sum r g
-- hvoid' = mapAll @Algebraic @HFunctor @r hvoid
-- @
mapAll :: forall c1 c2 r a. (forall b. c1 b => c2 b, All c1 r) => (All c2 r => a) -> a
mapAll a =
    case cpara @c1 @r @(MapAll c2) MapAll (\MapAll -> MapAll) of
        MapAll -> a

newtype SumFn f g a b r = SumFn { unSumFn :: Sum r f a -> Sum r g b }

instance (All HFunctor r, Functor f) => Functor (Sum r f) where
    fmap :: forall a b. (a -> b) -> Sum r f a -> Sum r f b
    fmap f = unSumFn $ cpara @HFunctor n c
        where
            n :: SumFn f f a b '[]
            n = SumFn \case
            c :: forall y ys. HFunctor y => SumFn f f a b ys -> SumFn f f a b (y : ys)
            c (SumFn k) = SumFn \case
                This y -> This (fmap f y)
                That ys -> That (k ys)

instance All HFunctor r => HFunctor (Sum r) where
    hmap :: forall f g a. (Functor f, Functor g) => (f ~> g) -> Sum r f a -> Sum r g a
    hmap t = unSumFn $ cpara @HFunctor n c
        where
            n :: SumFn f g a a '[]
            n = SumFn \case
            c :: forall y ys. HFunctor y => SumFn f g a a ys -> SumFn f g a a (y : ys)
            c (SumFn k) = SumFn \case
                This y -> This (hmap t y)
                That ys -> That (k ys)

instance (All HFunctor r, All Algebraic r) => Algebraic (Sum r) where
    hvoid :: forall f g a. Sum r f a -> Sum r g a
    hvoid = unSumFn $ cpara @Algebraic n c
        where
            n :: SumFn f g a a '[]
            n = SumFn \case
            c :: forall y ys. Algebraic y => SumFn f g a a ys -> SumFn f g a a (y : ys)
            c (SumFn k) = SumFn \case
                This y -> This (hvoid y)
                That ys -> That (k ys)
    
-- | Type-list membership
type (:<) :: ((Type -> Type) -> Type -> Type) -> [(Type -> Type) -> Type -> Type] -> Constraint
class (HFunctor h, All HFunctor r) => h :< r where
    hinject :: h f a -> Sum r f a
    hproject :: Sum r f a -> Maybe (h f a)

instance (HFunctor h, All HFunctor r) => h :< (h : r) where
    hinject = This
    hproject (This x) = Just x
    hproject (That _) = Nothing

instance {-# OVERLAPPABLE #-} (HFunctor g, h :< r) => h :< (g : r) where
    hinject = That . hinject
    hproject (This _) = Nothing
    hproject (That x) = hproject x


