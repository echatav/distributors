{-# LANGUAGE
GADTs
, LambdaCase
, QuantifiedConstraints
#-}

module Control.Distributor where

import Data.Profunctor
import Data.Void

class Profunctor p => Bimodule p where

  expel :: b -> p a b
  expel b = dimap (\_ -> ()) (\_ -> b) expelled
  expelled :: p () ()
  expelled = expel ()
  
  factor
    :: (a -> (a0, a1))
    -> (b0 -> b1 -> b)
    -> p a0 b0
    -> p a1 b1
    -> p a b
  factor f g p0 p1 = dimap f (uncurry g) (p0 >*< p1)
  (>*<) :: p a0 b0 -> p a1 b1 -> p (a0,a1) (b0,b1)
  (>*<) = factor id (,)

class Bimodule p => Distributor p where

  root :: (a -> Void) -> p a b
  root f = dimap f absurd rooted
  rooted :: p Void Void
  rooted = root id

  branch
    :: (a -> Either a0 a1)
    -> (Either b0 b1 -> b)
    -> p a0 b0
    -> p a1 b1
    -> p a b
  branch f g p0 p1 = dimap f g (p0 >|< p1)
  (>|<) :: p a0 b0 -> p a1 b1 -> p (Either a0 a1) (Either b0 b1)
  (>|<) = branch id id

data Dist q a b where
  Expel :: b -> Dist q a b
  Factor
    :: (a -> (a0, a1))
    -> (b0 -> b1 -> b)
    -> Dist q a0 b0
    -> Dist q a1 b1
    -> Dist q a b
  Root :: (a -> Void) -> Dist q a b
  Branch
    :: (a -> Either a0 a1)
    -> (Either b0 b1 -> b)
    -> Dist q a0 b0
    -> Dist q a1 b1
    -> Dist q a b
instance Profunctor (Dist q) where
  dimap f g = \case
    Expel b -> Expel (g b)
    Factor f' g' d1 d2 ->
      Factor (f' . f) (((.).(.)) g g') d1 d2
    Root f' -> Root (f' . f)
    Branch f' g' d1 d2 ->
      Branch (f' . f) (g . g') d1 d2
instance Bimodule (Dist q) where
  expel = Expel
  factor = Factor
instance Distributor (Dist q) where
  root = Root
  branch = Branch

class (forall q. Distributor (dist q))
  => FreeDistributor dist where
instance FreeDistributor Dist
