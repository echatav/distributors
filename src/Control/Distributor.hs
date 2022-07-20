{-# LANGUAGE
GADTs
, LambdaCase
, QuantifiedConstraints
#-}

module Control.Distributor where

import Control.Arrow
import Data.Profunctor
import Data.Void

{- The name `Bimodule` in the category theory literature
is a synonym for `Profunctor`. Here it is restricted
to the case of a Hask-enriched endo-profunctor which respects
the product structure of Hask given by pairing `(,)`.
`Bimodule` and `Profunctor` relate in the same way as
`Applicative` and `Functor`.

I might guess that there's a Van Laarhoven representation
of `Traversal`s using `Bimodule`.

```
type Traversal s t a b =
  forall p. Bimodule p => p a b -> p s t
```
-}
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
    Factor f' g' q0 d1 ->
      Factor (f' . f) (((.).(.)) g g') q0 d1
instance Bimodule (Bimod q) where
  expel = Expel
  factor f g (Expel b) bim = dimap (snd . f) (g b) bim
  factor f g (Factor f' g' q bim0) bim1 =
    let
      associate ((a,b),c) = (a,(b,c))
      ff = first f' . f
      gg b0 (b1,b2) = g (g' b0 b1) b2
    in
      Factor (associate . ff) gg q (bim0 >*< bim1)

data Dist q a b where
  Root :: (a -> Void) -> Dist q a b
  Branch
    :: (a -> Either a0 a1)
    -> (Either b0 b1 -> b)
    -> Bimod q a0 b0
    -> Dist q a1 b1
    -> Dist q a b

instance Profunctor (Dist q) where
  dimap f g = \case
    Root a -> Root (a . f)
    Branch f' g' bim dist -> Branch (f' . f) (g . g') bim dist

instance Bimodule (Dist q) where
  expel b = Branch Left (either id absurd) (Expel b) (Root id)
  factor f _ (Root v) _ = Root (v . fst . f)
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
        (Branch Left (either id absurd) x (Root id) >*< z)
        (y >*< z)

instance Distributor (Dist q) where
  root = Root
  branch f g (Root v) dist =
    dimap (either (absurd . v) id . f) (g . Right) dist
  branch f g (Branch f' g' x y) z =
    let
      associate (Left (Left a)) = Left a
      associate (Left (Right b)) = Right (Left b)
      associate (Right  c) = Right (Right c)

      ff = left f' . f

      gg (Left b2) = g (Left (g' (Left b2)))
      gg (Right (Left b3)) = g (Left (g' (Right b3)))
      gg (Right (Right b1)) = g (Right b1)
    in
      Branch (associate . ff) gg x (y >|< z)
