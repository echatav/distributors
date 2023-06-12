{-# LANGUAGE
FlexibleInstances
, QuantifiedConstraints
#-}

module Data.Profunctor.Monoidal_ where

import Data.Bifunctor
import Control.Applicative hiding (WrappedArrow(..))
import Control.Selective
import Data.Profunctor
import Witherable

(>*<)
  :: (Profunctor p, forall a. Applicative (p a))
  => p a0 b0 -> p a1 b1 -> p (a0,a1) (b0,b1)
infixr 4 >*<
p0 >*< p1 = ($) <$> dimap fst (,) p0 <*> lmap snd p1

decompress
  :: Costrong p
  => p (a0,a1) (b0,b1) -> (p a0 b0, p a1 b1)
decompress = undefined

(>+<)
  :: (Choice p, forall a. Selective (p a))
  => p a0 b0 -> p a1 b1 -> p (Either a0 a1) (Either b0 b1)
p0 >+< p1 = undefined

discriminate
  :: (Cochoice p, forall a. Filterable (p a))
  => p (Either a0 a1) (Either b0 b1)
  -> (p a0 b0, p a1 b1)
discriminate = undefined

-- monoidality :: Selective f => f (Either a b) -> Either (f a) (f b)
-- monoidality = either id id . either fmap

class Elective f where
  elect :: f (Either a b) -> Either (f a) (f b)

sElect :: (Applicative f, Elective f) => f (a -> b) -> f (Either a b) -> f b
sElect f = either id id . bimap (f <*>) id . elect
