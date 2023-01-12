{-# LANGUAGE AllowAmbiguousTypes #-}

module Main (module Main) where

import Control.Applicative (liftA2)
import Control.Monad
import Control.Monad.Effect
import Control.Monad.Effect.Internal

data Throw e m a = Throw e
    deriving (Functor, HFunctor, Algebraic)

throw :: Throw e :< r => e -> Eff r a
throw e = send (Throw e)

handleThrow :: forall e r a. All Algebraic r => Eff (Throw e : r) a -> Eff r (Either e a)
handleThrow = mapAll @Algebraic @HFunctor @r $ handle (pure . Right) \case
    Throw e -> pure (Left e)

interposeThrow :: forall e r a. (Throw e :< r, All Algebraic r) => Eff r a -> Eff r (Either e a)
interposeThrow = interpose (pure . Right) \case
    Throw e -> pure (Left e)

data Catch e m a = Catch (m a) (e -> m a)
    deriving (Functor)

instance HFunctor (Catch e) where
    hmap t (Catch m h) = Catch (t m) (t . h)

catch :: Catch e :< r => Eff r a -> (e -> Eff r a) -> Eff r a
catch m k = send (Catch m k)

elabCatch :: (Throw e :< r, All Algebraic r) => Catch e (Eff r) (Eff r a) -> Eff r a
elabCatch (Catch m k) =
    interposeThrow m >>= \case
        Left e  -> join $ k e
        Right a -> a

-- elabCatch :: forall e r a. Throw e :< r => Eff (Catch e : r) a -> Eff r a
-- elabCatch

-- -- elabCatch :: forall e r a. Throw e :< r => Eff (Catch e : r) a -> Eff r a
-- -- elabCatch = handleH pure \case
-- --     Catch (m :: Eff r (Eff r b)) (h :: e -> Eff r (Eff r b)) ->
-- --         let m' :: Eff r (Eff r b)
-- --             m' = interposeH @(Throw e) pure (\(Throw e) -> _) m
-- --         in undefined :: Eff r b
--         -- join $ interposeH @(Throw e) pure (\(Throw e) -> h e) m
--         -- interposeH @(Throw e) @r @_ pure alg m >>= k
--         -- where
--         --     alg :: forall b. Throw e (Eff r) (Eff r b) -> Eff r b
--         --     alg (Throw e) = h e


data NonDet m a
    = Empty
    | Choose a a
    deriving (Functor, HFunctor, Algebraic)

empty :: NonDet :< r => Eff r a
empty = send Empty

choose :: NonDet :< r => a -> a -> Eff r a
choose a b = send (Choose a b)

(<|>) :: NonDet :< r => Eff r a -> Eff r a -> Eff r a
a <|> b = join $ choose a b

handleNonDet :: forall r a. All Algebraic r => Eff (NonDet : r) a -> Eff r [a]
handleNonDet = mapAll @Algebraic @HFunctor @r $ handle (\a -> pure [a]) \case
    Empty      -> pure []
    Choose a b -> liftA2 (++) a b

interposeNonDet :: forall r a. (NonDet :< r, All Algebraic r) => Eff r a -> Eff r [a]
interposeNonDet = interpose (\a -> pure [a]) \case
    Empty      -> pure []
    Choose a b -> liftA2 (++) a b

data Once m a
    = Once (m a)
    deriving (Functor)

instance HFunctor Once where
    hmap t (Once m) = Once (t m)

once :: Once :< r => Eff r a -> Eff r a
once m = send (Once m)

elabOnce :: forall r a. (NonDet :< r, All Algebraic r) => Once (Eff r) (Eff r a) -> Eff r a
elabOnce (Once m) = 
    let hdl :: forall b. Eff r b -> Eff r (Maybe b)
        hdl = interpose (\a -> pure (Just a)) \case
                Empty      -> pure Nothing
                Choose a b -> liftA2 mplus a b
     in join $ hdl m >>= maybe empty pure

-- ignoreOnce :: All HFunctor r => Eff (Once : r) a -> Eff r a
-- ignoreOnce = handleH pure \case
--     Once m -> join m

prog :: (Once :< r, NonDet :< r) => Eff r Int
prog = do
    a <- choose 10 20
    _ <- choose () ()
    b <- once $ choose 3 4
    pure $ a + b

prog2 :: (Throw String :< r, Catch String :< r, NonDet :< r) => Eff r String
prog2 = catch (throw @String "Foo" <|> pure "Normal return")
              (\e -> pure $ "Caught Error: " ++ e)

main :: IO ()
main = do
    putStrLn "Hello from fibered-effects"

    putStrLn "prog"
    print $ runPure $ handleNonDet $ handleH pure elabOnce prog

    putStrLn "prog2"
    print $ runPure $ handleNonDet $ handleThrow @String $ handleH pure (elabCatch @String) prog2
    print $ runPure $ handleThrow @String $ handleNonDet $ handleH pure (elabCatch @String) prog2
