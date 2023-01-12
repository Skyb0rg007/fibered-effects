{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.Effect (
    -- 
      Eff (..)
    , runPure
    , send

    -- * Algebraic effect handling
    , interpose
    -- , interposeS
    , handle
    -- , handleS

    -- * Higher-order effect handling
    , handleH
    , interposeH
    -- , interposeHS

    -- * Re-exports
    , HFunctor (..)
    , Algebraic (..)
    , All
    , mapAll
    , (:<)

    , Product (..)
    , Const (..)
    , Compose (..)
    , Identity (..)
    , Void
    ) where

import Control.Monad.Effect.Internal
import Control.Monad
import Data.Functor.Const
import Data.Functor.Compose
import Data.Functor.Product
import Data.Functor.Identity
import Data.HFunctor
import Data.Void

data Eff r a
    = Pure a
    | Free (Sum r (Eff r) (Eff r a))

instance All HFunctor r => Functor (Eff r) where
    fmap f (Pure a) = Pure (f a)
    fmap f (Free x) = Free (fmap (fmap f) x)

instance All HFunctor r => Applicative (Eff r) where
    pure = Pure
    (<*>) = ap

instance All HFunctor r => Monad (Eff r) where
    Pure a >>= f = f a
    Free x >>= f = Free (fmap (>>= f) x)

runPure :: Eff '[] a -> a
runPure (Pure a) = a
runPure (Free x) = case x of

send :: h :< r => h (Eff r) a -> Eff r a
send = Free . hinject . fmap Pure

handle :: forall h r a b.
       (Algebraic h, All Algebraic r)
    => (a -> Eff r b)
    -> (h (Const Void) (Eff r b) -> Eff r b)
    -> Eff (h : r) a
    -> Eff r b
handle onPure onEff = mapAll @Algebraic @HFunctor @r go
    where
        go :: All HFunctor r => Eff (h : r) a -> Eff r b
        go (Pure a)        = onPure a
        go (Free (This h)) = onEff $ hvoid $ fmap go h
        go (Free (That x)) = Free $ hvoid $ fmap go x

handle2 :: forall h1 h2 r a b.
       (Algebraic h1, Algebraic h2, All Algebraic r)
    => (a -> Eff r b)
    -> (h1 (Const Void) (Eff r b) -> Eff r b)
    -> (h2 (Const Void) (Eff r b) -> Eff r b)
    -> Eff (h1 : h2 : r) a
    -> Eff r b
handle2 onPure onEff1 onEff2 = mapAll @Algebraic @HFunctor @r go
    where
        go :: All HFunctor r => Eff (h1 : h2 : r) a -> Eff r b
        go (Pure a) = onPure a
        go (Free (This h1)) = onEff1 $ hvoid $ fmap go h1
        go (Free (That (This h2))) = onEff2 $ hvoid $ fmap go h2
        go (Free (That (That x))) = Free $ hvoid $ fmap go x

handleH :: forall h r a.
       (HFunctor h, All HFunctor r)
    => (forall b. b -> Eff r b)
    -> (forall b. h (Eff r) (Eff r b) -> Eff r b)
    -> Eff (h : r) a
    -> Eff r a
handleH onPure onEff = go
    where
        go :: Eff (h : r) ~> Eff r
        go (Pure a)        = onPure a
        go (Free (This h)) = onEff $ hmap go $ fmap go h
        go (Free (That x)) = Free $ hmap go $ fmap go x

handleH2 :: forall h1 h2 r a.
       (HFunctor h1, HFunctor h2, All HFunctor r)
    => (forall b. b -> Eff r b)
    -> (forall b. h1 (Eff r) (Eff r b) -> Eff r b)
    -> (forall b. h2 (Eff r) (Eff r b) -> Eff r b)
    -> Eff (h1 : h2 : r) a
    -> Eff r a
handleH2 onPure onEff1 onEff2 = go
    where
        go :: Eff (h1 : h2 : r) ~> Eff r
        go (Pure a)                = onPure a
        go (Free (This h1))        = onEff1 $ hmap go $ fmap go h1
        go (Free (That (This h2))) = onEff2 $ hmap go $ fmap go h2
        go (Free (That (That x)))  = Free $ hmap go $ fmap go x

interpose :: forall h r a b.
       (h :< r, Algebraic h, All Algebraic r)
    => (a -> Eff r b)
    -> (h (Const Void) (Eff r b) -> Eff r b)
    -> Eff r a
    -> Eff r b
interpose onPure onEff = go
    where
        go :: Eff r a -> Eff r b
        go (Pure a)        = onPure a
        go (Free x) =
            case hproject @h x of
                Nothing -> Free $ hvoid $ fmap go x
                Just h  -> onEff $ hvoid $ fmap go h

interposeH :: forall h r a.
       (h :< r)
    => (forall b. b -> Eff r b)
    -> (forall b. h (Eff r) (Eff r b) -> Eff r b)
    -> Eff r a
    -> Eff r a
interposeH onPure onEff = go
    where
        go :: Eff r ~> Eff r
        go (Pure a) = onPure a
        go (Free x) =
            case hproject @h x of
                Nothing -> Free $ hmap go $ fmap go x
                Just h  -> onEff $ hmap go $ fmap go h


-- newtype Eff r a = Eff { unEff :: HFree (Sum r) a }

-- deriving newtype instance All HFunctor r => Functor (Eff r)
-- deriving newtype instance All HFunctor r => Applicative (Eff r)
-- deriving newtype instance All HFunctor r => Monad (Eff r)

-- runPure :: Eff '[] a -> a
-- runPure (Eff (HPure a)) = a
-- runPure (Eff (HFree s)) = case s of

-- send :: h :< r => h (Eff r) a -> Eff r a
-- send = Eff . HFree . hinject . hmap unEff . fmap HPure

-- interpose :: forall h r a b.
--        (h :< r, All Algebraic r)
--     => (a -> Eff r b)                -- ^ Handle pure result
--     -> (h (Const Void) (Eff r b) -> Eff r b) -- ^ Handle effect
--     -> Eff r a
--     -> Eff r b
-- interpose onPure onEff = Eff . cata alg . unEff
--     where
--         alg :: HFreeF (Sum r) a (HFree (Sum r) b) -> HFree (Sum r) b
--         alg (HPureF a) = unEff $ onPure a
--         alg (HFreeF x) =
--             case hproject @h x of
--                 Nothing -> HFree $ hvoid x
--                 Just h -> unEff $ onEff (fmap Eff h)

-- interposeS :: forall s h r a b.
--        (h :< r, All Algebraic r)
--     => (s -> a -> Eff r b)
--     -> (s -> h (Const Void) (s -> Eff r b) -> Eff r b)
--     -> Eff r a
--     -> s
--     -> Eff r b
-- interposeS onPure onEff = fmap Eff . cata alg . unEff
--     where
--         alg :: HFreeF (Sum r) a (s -> HFree (Sum r) b) -> s -> HFree (Sum r) b
--         alg (HPureF a) s = unEff $ onPure s a
--         alg (HFreeF x) s =
--             case hproject @h x of
--                 Nothing -> HFree $ hvoid $ fmap ($ s) x
--                 Just h -> unEff $ onEff s (fmap (fmap Eff) h)

-- handle :: forall h r a b.
--        (Algebraic h, All Algebraic r)
--     => (a -> Eff r b)
--     -> (h (Const Void) (Eff r b) -> Eff r b)
--     -> Eff (h : r) a
--     -> Eff r b
-- handle onPure onEff = mapAll @Algebraic @HFunctor @r $ cata alg . unEff
--     where
--         alg :: All HFunctor r => HFreeF (Sum (h : r)) a (Eff r b) -> Eff r b
--         alg (HPureF a) = onPure a
--         alg (HFreeF (This h)) = onEff h
--         alg (HFreeF (That x)) = Eff $ HFree $ hvoid $ fmap unEff x

-- handleS :: forall s h r a b.
--        (Algebraic h, All Algebraic r)
--     => (s -> a -> Eff r b)
--     -> (s -> h (Const Void) (s -> Eff r b) -> Eff r b)
--     -> Eff (h : r) a
--     -> s
--     -> Eff r b
-- handleS onPure onEff = mapAll @Algebraic @HFunctor @r $ cata alg . unEff
--     where
--         alg :: All HFunctor r => HFreeF (Sum (h : r)) a (s -> Eff r b) -> s -> Eff r b
--         alg (HPureF a) s = onPure s a
--         alg (HFreeF (This h)) s = onEff s h
--         alg (HFreeF (That x)) s = Eff $ HFree $ hvoid $ fmap (($ s) . fmap unEff) x

-- interposeH :: forall h r a.
--        h :< r
--     => (forall b. b -> Eff r b)
--     -> (forall b. h (Eff r) (Eff r b) -> Eff r b)
--     -> Eff r a
--     -> Eff r a
-- interposeH onPure onEff = go
--     where
--         go (Eff (HPure a)) = onPure a
--         go (Eff (HFree x)) =
--             case hproject @h x of
--                 Nothing -> go $ Eff $ HFree x
--                 Just h  -> go $ onEff $ hmap Eff $ fmap Eff h

-- foldH :: forall h r g a.
--        (HFunctor h, All HFunctor r, Functor g)
--     => (forall b. b -> g b)
--     -> (forall b. h g (g b) -> g b)
--     -> (forall b. Sum r g (g b) -> g b)
--     -> Eff (h : r) a -> g a
-- foldH onPure onEff weave = go
--     where
--         go :: Eff (h : r) ~> g
--         go (Eff (HPure a)) = onPure a
--         go (Eff (HFree (This h))) = onEff $ hmap (go . Eff) $ fmap (go . Eff) h
--         go (Eff (HFree (That x))) = weave $ hmap (go . Eff) $ fmap (go . Eff) x

-- newtype ArrowEff s r b = ArrowEff { unArrowEff :: s -> Eff r b }

-- deriving instance All HFunctor r => Functor (ArrowEff s r)

-- interposeHS :: forall s h r a.
--        h :< r
--     => (forall b. s -> b -> Eff r b)
--     -> (forall b. s -> h (Eff r) (s -> Eff r b) -> Eff r b)
--     -> Eff r a
--     -> s
--     -> Eff r a
-- interposeHS onPure onEff = unArrowEff . hcata alg . unEff
--     where
--         alg :: HFreeH (Sum r) (ArrowEff s r) ~> ArrowEff s r
--         alg (HPureH a) = ArrowEff $ \s -> onPure s a
--         alg (HFreeH x) = ArrowEff $ \s ->
--             case hproject @h x of
--                 Nothing -> Eff $ HFree $ hmap (unEff . ($ s) . unArrowEff) $ fmap (unEff . ($ s) . unArrowEff) x
--                 Just h -> onEff s $ hmap (($ s) . unArrowEff) $ fmap unArrowEff h

-- handleH :: forall h r a.
--        (HFunctor h, All HFunctor r)
--     => (forall b. b -> Eff r b)
--     -> (forall b. h (Eff r) (Eff r b) -> Eff r b)
--     -> Eff (h : r) a
--     -> Eff r a
-- handleH onPure onEff = hcata alg . unEff
--     where
--         alg :: HFreeH (Sum (h : r)) (Eff r) ~> Eff r
--         alg (HPureH a) = onPure a
--         alg (HFreeH (This h)) = onEff h
--         alg (HFreeH (That x)) = Eff $ HFree $ hmap unEff $ fmap unEff x
