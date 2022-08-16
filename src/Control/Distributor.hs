{-|
Module: Control.Distributor
Description: Bimodule and Distributor algebraic combinators
Copyright: (c) Eitan Chatav, 2022
Maintainer: eitan@morphism.tech
Stability: experimental

`Bimodule` and `Distributor` are subclasses of `Profunctor`
that act in analogy to how `Applicative` and `Alternative`
act as subclasses of `Functor`.
-}

{-# LANGUAGE
GADTs
, LambdaCase
, QuantifiedConstraints
, RankNTypes
#-}

module Control.Distributor where

import Data.Bifunctor
import Data.Profunctor
import Data.Profunctor.Composition
import Data.Void

{- | A `Bimodule` is a `Profunctor` which respects
the monoidal structure of the category of Haskell
types and functions `(->)` given by
the unit type `()` and the Cartesian product `(,)`.

That is, a `Bimodule` is Cartesian monoidal endoprofunctor on `(->)`.

This is contrary to the definition of bimodule
in the category theory literature, which is the
same as a profunctor but in a setting of enriched
category theory.
-}
class Profunctor p => Bimodule p where

  {-# MINIMAL
      expel, factor
    | expel, (>*<)
    | expelled, factor
    | expelled, (>*<)
    #-}

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
  infixr 4 >*<
  (>*<) = factor id (,)

(>*) :: Bimodule p => p () () -> p a b -> p a b
infixr 4 >*
(>*) = factor (\a -> ((),a)) (\_ b -> b)

(*<) :: Bimodule p => p a b -> p () () -> p a b
infixr 4 *<
(*<) = factor (\a -> (a,())) (\b _ -> b)

instance Bimodule (->) where
  expelled = id
  (>*<) = bimap

instance Applicative f => Bimodule (Star f) where
  expel b = Star (\_ -> pure b)
  factor f g (Star s0) (Star s1) =
    let
      g01 (a0, a1) = g <$> s0 a0 <*> s1 a1
    in
      Star (g01 . f)

instance (Bimodule p, Bimodule q)
  => Bimodule (Procompose p q) where
    expelled = Procompose expelled expelled
    Procompose bc0 ab0 >*< Procompose bc1 ab1 =
      Procompose (bc0 >*< bc1) (ab0 >*< ab1)

{- | A category with finite products and coproducts is called
distributive, if the canonical distributivity morphism
is an isomorphism. A `Distributor` is a `Profunctor`
which respects the distributive structure on `(->)`
given by nullary product `()`, binary product `(,)`,
nullary coproduct `Void` and binary coproduct `Either`.

In the category theory literature, distributor is a
synonym for profunctor; Jean Bénabou,
who coined both terms and originally used profunctor
later preferred distributor.

Credit for the use of the term distributor in the
case of a profunctor which respects distributive structure
goes to Travis Squires in his thesis
"Profunctors and Distributive Categories".
-}
class Bimodule p => Distributor p where

  {-# MINIMAL
      root, branch
    | root, (>|<)
    | rooted, branch
    | rooted, (>|<)
    #-}

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
  infixr 3 >|<
  (>|<) = branch id id

instance Distributor (->) where
  rooted = id
  (>|<) = bimap

instance (Distributor p, Distributor q)
  => Distributor (Procompose p q) where
    rooted = Procompose rooted rooted
    Procompose bc0 ab0 >|< Procompose bc1 ab1 =
      Procompose (bc0 >|< bc1) (ab0 >|< ab1)

instance Applicative f => Distributor (Star f) where
  root v = Star (vacuous . pure . v)
  branch f g (Star s0) (Star s1) =
    let
      g01 (Left a0) = g . Left <$> s0 a0
      g01 (Right a1) = g . Right <$> s1 a1
    in
      Star (g01 . f)

{- |
`Bimod` is an encoding of the free `Bimodule`
generated over a quiver.
-}
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
      ff = associate . first f' . f
      gg a (b,c) = g (g' a b) c
    in
      Factor ff gg x (y >*< z)

foldBimod
  :: Bimodule p
  => (forall a b. q a b -> p a b)
  -> Bimod q a b -> p a b
foldBimod k = \case
  Expel b -> expel b
  Factor f g x y -> factor f g (k x) (foldBimod k y)

{- |
`Dist` is an encoding of the free `Distributor`
generated over a quiver.
-}
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
      associate (Right c) = Right (Right c)

      ff = associate . first f' . f

      gg (Left a) = g (Left (g' (Left a)))
      gg (Right (Left b)) = g (Left (g' (Right b)))
      gg (Right (Right c)) = g (Right c)
    in
      Branch ff gg x (y >|< z)

mayhaps :: Distributor p => p a b -> p (Maybe a) (Maybe b)
mayhaps =
  let
    hither = maybe (Left ()) Right
    thither = either (\_ -> Nothing) Just
  in
    branch hither thither expelled

several :: Distributor p => p a b -> p [a] [b]
several p =
  let
    cons (Left ()) = []
    cons (Right (x,xs)) = x:xs

    decons [] = Left ()
    decons (x:xs) = Right (x,xs)
  in
    branch decons cons expelled (several1 p)

several1 :: Distributor p => p a b -> p (a,[a]) (b,[b])
several1 p = p >*< several p

sepBy :: Distributor p => p () () -> p a b -> p [a] [b]
sepBy separator p =
  let
    cons (Left ()) = []
    cons (Right (x,xs)) = x:xs

    decons [] = Left ()
    decons (x:xs) = Right (x,xs)
  in
    branch decons cons expelled (sepBy1 separator p)

sepBy1 :: Distributor p => p () () -> p a b -> p (a,[a]) (b,[b])
sepBy1 separator p = p >*< several (separator >* p)

foldDist
  :: Distributor p
  => (forall a b. q a b -> p a b)
  -> Dist q a b -> p a b
foldDist k = \case
  Root v -> root v
  Branch f g x y -> branch f g (foldBimod k x) (foldDist k y)
