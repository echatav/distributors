{-# LANGUAGE
GADTs
, LambdaCase
, QuantifiedConstraints
, RankNTypes
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
  infixr 4 >*<
  (>*<) = factor id (,)

(>*) :: Bimodule p => p () () -> p a b -> p a b
infixr 4 >*
p0 >* p1 = factor (\a -> ((),a)) (\_ b -> b) p0 p1

(*<) :: Bimodule p => p a b -> p () () -> p a b
infixr 4 *<
p0 *< p1 = factor (\a -> (a,())) (\b _ -> b) p0 p1

(>**<)
  :: Bimodule p
  => p a0 b0
  -> p a1 b1
  -> p (a0,(a1,())) (b0,(b1,()))
infixr 4 >**<
x >**< y = x >*< y >*< expelled

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
  infixr 3 >|<
  (>|<) = branch id id

(>|) :: Distributor p => p Void Void -> p a b -> p a b
infixr 3 >|
p0 >| p1 = branch Right (either absurd id) p0 p1

(|<) :: Distributor p => p a b -> p Void Void -> p a b
infixr 3 |<
p0 |< p1 = branch Left (either id absurd) p0 p1

(>||<)
  :: Distributor p
  => p a0 b0
  -> p a1 b1
  -> p (Either a0 (Either a1 Void)) (Either b0 (Either b1 Void))
infixr 3 >||<
x >||< y = x >|< y >|< rooted

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

      ff = associate . left f' . f

      gg (Left a) = g (Left (g' (Left a)))
      gg (Right (Left b)) = g (Left (g' (Right b)))
      gg (Right (Right c)) = g (Right c)
    in
      Branch ff gg x (y >|< z)

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
