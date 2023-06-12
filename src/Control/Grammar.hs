{-# LANGUAGE GADTs, RankNTypes #-}

module Control.Grammar where

import Control.Monad
import Control.Monad.Fix

data Grammar r a where
  BindRule :: (r -> Grammar r b) -> r -> Grammar r b
  BindFix :: (a -> Grammar r b) -> (a -> Grammar r a) -> Grammar r b
  Return :: a -> Grammar r a

instance Functor (Grammar r) where
  fmap f (BindRule ab a) = BindRule (fmap f . ab) a
  fmap f (BindFix ab a) = BindFix (fmap f . ab) a
  fmap f (Return a) = Return (f a)

instance Applicative (Grammar r) where
  pure = Return
  (<*>) = ap

instance Monad (Grammar r) where
  return = Return
  BindRule ab a >>= f = BindRule (ab >=> f) a
  BindFix ab a >>= f = BindFix (ab >=> f) a
  Return a >>= f = f a

instance MonadFix (Grammar r) where
  mfix = BindFix Return

rule :: r -> Grammar r r
rule = BindRule Return

runGrammar :: MonadFix m => (forall a. a -> m a) -> Grammar r b -> m b
runGrammar r (BindRule ab a) = do
  a' <- r a
  runGrammar r $ ab a'
runGrammar r (BindFix ab a) = do
  a' <- mfix $ runGrammar r <$> a
  runGrammar r $ ab a'
runGrammar _ (Return a) = return a
