{-# LANGUAGE
GADTs
, LambdaCase
, QuantifiedConstraints
#-}

module Control.Distributor where

import Control.Arrow
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

data Bimod q a b where
  Expel :: b -> Bimod q a b
  Factor
    :: (a -> (a0, a1))
    -> (b0 -> b1 -> b)
    -> q a0 b0
    -> Bimod q a1 b1
    -> Bimod q a b
instance Profunctor (Bimod q) where
  dimap f g = \case
    Expel b -> Expel (g b)
    Factor f' g' x y ->
      Factor (f' . f) (((.).(.)) g g') x y
instance Bimodule (Bimod q) where
  expel = Expel
  -- 1*x = x
  factor f g (Expel b) x = dimap (snd . f) (g b) x
  -- (x*y)*z = x*(y*z)
  factor f g (Factor f' g' x y) z =
    let
      associate ((a,b),c) = (a,(b,c))
      ff = first f' . f
      gg b0 (b1,b2) = g (g' b0 b1) b2
    in
      Factor (associate . ff) gg x (y >*< z)

data Dist q a b where
  Root :: (a -> Void) -> Dist q a b
  Branch
    :: (a -> Either a0 a1)
    -> (Either b0 b1 -> b)
    -> Bimod q a0 b0
    -> Dist q a1 b1
    -> Dist q a b

liftBimod :: Bimod q a b -> Dist q a b
liftBimod x = Branch Left (either id absurd) x (Root id)

instance Profunctor (Dist q) where
  dimap f g = \case
    Root v -> Root (v . f)
    Branch f' g' x y -> Branch (f' . f) (g . g') x y

instance Bimodule (Dist q) where
  expel b = liftBimod (Expel b)
  -- 0 * _ = 0
  factor f _ (Root v) _ = Root (v . fst . f)
  -- (x+y)*z = (x*z)+(y*z)
  factor f g (Branch f' g' x y) z =
    let
      distribute (Left a,c) = Left (a,c)
      distribute (Right b,c) = Right (b,c)

      redistribute (Left (a,c)) = (Left a,c)
      redistribute (Right (b,c)) = (Right b,c)

      ff = first f' . f

      gg (a,b) = g (g' a) b
    in
      branch
        (distribute . ff)
        (gg . redistribute)
        (liftBimod x >*< z)
        (y >*< z)

instance Distributor (Dist q) where
  root = Root
  -- 0+x = x
  branch f g (Root v) x =
    dimap (either (absurd . v) id . f) (g . Right) x
  -- (x+y)+z = x+(y+z)
  branch f g (Branch f' g' x y) z =
    let
      associate (Left (Left a)) = Left a
      associate (Left (Right b)) = Right (Left b)
      associate (Right  c) = Right (Right c)

      ff = left f' . f

      gg (Left b0) = g (Left (g' (Left b0)))
      gg (Right (Left b1)) = g (Left (g' (Right b1)))
      gg (Right (Right b2)) = g (Right b2)
    in
      Branch (associate . ff) gg x (y >|< z)
