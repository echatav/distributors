{-# LANGUAGE
FlexibleInstances
, QuantifiedConstraints
#-}

module Data.Profunctor.Monoidal where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Tannen
import Data.Functor.Contravariant.Divisible
import Data.List.NonEmpty (unzip)
import Data.Profunctor
import Data.Profunctor.Cayley
import Data.Profunctor.Composition
import Data.Tagged
import Data.Void
import Prelude hiding (unzip)

class Profunctor p => Applicator p where

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

instance Applicator (->) where
  expel = pure
  (>*<) = (***)

instance Applicator Tagged where
  expel = pure
  factor _ g (Tagged x) (Tagged y) = Tagged (g x y)

instance Functor f => Applicator (Costar f) where
  expel = pure
  Costar u >*< Costar v = Costar ((u >*< v) . unzip)

instance Monoid m => Applicator (Forget m) where
  expel _ = Forget (\_ -> mempty)
  factor f _ (Forget u) (Forget v) = Forget $ \a ->
    let
      (a0, a1) = f a
    in
      u a0 <> v a1

instance Applicative f => Applicator (Star f) where
  expel = pure
  factor f g (Star u) (Star v) = Star $ \a ->
    let
      (a0,a1) = f a
      fb0 = u a0
      fb1 = v a1
    in
      g <$> fb0 <*> fb1

instance Divisible f => Applicator (Clown f) where
  expel _ = Clown conquer
  factor f _ (Clown u) (Clown v) = Clown (divide f u v)

instance Applicative f => Applicator (Joker f) where
  expel = Joker . pure
  factor _ g (Joker u) (Joker v) = Joker (liftA2 g u v)

instance Arrow a  => Applicator (WrappedArrow a) where
  expel b = WrapArrow (arr (\_ -> b))
  WrapArrow u >*< WrapArrow v = WrapArrow (u *** v)

instance (Applicator p0, Applicator p1) => Applicator (Product p0 p1) where
  expel b = Pair (expel b) (expel b)
  factor f g (Pair u v) (Pair u' v') =
    Pair (factor f g u u') (factor f g v v')

instance (Applicative f, Applicator p) => Applicator (Cayley f p) where
  expel b = Cayley (pure (expel b))
  factor f g (Cayley u) (Cayley v) = Cayley (liftA2 (factor f g) u v)

instance (Applicative f, Applicator p) => Applicator (Tannen f p) where
  expel b = Tannen (pure (expel b))
  factor f g (Tannen u) (Tannen v) = Tannen (liftA2 (factor f g) u v)

instance (Functor f, Applicative g, Applicator p)
  => Applicator (Biff p f g) where
    expel = Biff . expel . pure
    factor f g (Biff u) (Biff v) =
      Biff (factor (unzip . fmap f) (liftA2 g) u v)

instance (Applicator p, Applicator q) => Applicator (Procompose p q) where
  expel b = Procompose (expel b) (expel b)
  factor f g (Procompose u v) (Procompose u' v') =
    Procompose (factor id g u u') (factor f (,) v v')

class Profunctor p => Alternator p where

  {-# MINIMAL
      root, branch
    | root, (>+<)
    | rooted, branch
    | rooted, (>+<)
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
  branch f g p0 p1 = dimap f g (p0 >+< p1)

  (>+<) :: p a0 b0 -> p a1 b1 -> p (Either a0 a1) (Either b0 b1)
  infixr 3 >+<
  (>+<) = branch id id

instance Alternator (->) where
  root v = absurd . v
  branch f g u v = g . (u +++ v) . f

instance Alternator (Forget r) where
  root = Forget . root
  branch f _ (Forget u) (Forget v) = Forget ((u ||| v) . f)

instance Functor f => Alternator (Star f) where
  root = Star . root
  branch f g (Star u) (Star v) =
    Star (fmap g . either (Left <$>) (Right <$>) . (u +++ v) . f)

instance Decidable f => Alternator (Clown f) where
  root = Clown . lose
  branch f _ (Clown u) (Clown v) = Clown (choose f u v)

instance Alternative f => Alternator (Joker f) where
  root _ = Joker empty
  branch _ g (Joker u) (Joker v) = Joker (g <$> (Left <$> u <|> Right <$> v))

instance ArrowChoice a  => Alternator (WrappedArrow a) where
  root v = WrapArrow (arr (absurd . v))
  WrapArrow u >+< WrapArrow v = WrapArrow (u +++ v)

instance (Alternator p0, Alternator p1) => Alternator (Product p0 p1) where
  root v = Pair (root v) (root v)
  branch f g (Pair u v) (Pair u' v') =
    Pair (branch f g u u') (branch f g v v')

instance (Applicative f, Alternator p) => Alternator (Cayley f p) where
  root v = Cayley (pure (root v))
  branch f g (Cayley u) (Cayley v) = Cayley (liftA2 (branch f g) u v)

instance (Applicative f, Alternator p) => Alternator (Tannen f p) where
  root v = Tannen (pure (root v))
  branch f g (Tannen u) (Tannen v) = Tannen (liftA2 (branch f g) u v)

instance (Alternator p, Alternator q) => Alternator (Procompose p q) where
  root v = Procompose (root v) (root v)
  branch f g (Procompose u v) (Procompose u' v') =
    Procompose (branch id g u u') (branch f id v v')

class Costrong p => Decompressor p where
  decompress :: p (a0,a1) (b0,b1) -> (p a0 b0, p a1 b1)

class (Strong p, Decompressor p) => Refractor p where
  refract :: (s -> (s, a)) -> (s -> b -> t) -> p a b -> p s t
  refract f g =
    let
      f' (_,s) = f s
      g' (s,b) = ((),g s b)
    in
      snd . decompress . dimap f' g' . second'

class Cochoice p => Discriminator p where
  discriminate :: p (Either a0 a1) (Either b0 b1) -> (p a0 b0, p a1 b1)

class (Choice p, Discriminator p) => Filtrator p where
  dimapMaybe :: (s -> Maybe a) -> (b -> Maybe t) -> p a b -> p s t
  dimapMaybe f g
    = snd
    . discriminate
    . dimap (either Left (rightly f)) (>>= rightly g)
    . right'
    where
      rightly h = maybe (Left ()) Right . h

dicatMaybe :: Filtrator p => p a (Maybe b) -> p (Maybe a) b
dicatMaybe = dimapMaybe id id

plus'
  :: (s -> Maybe a, b -> Maybe t)
  -> (s -> Maybe a, b -> Maybe t)
  -> (s -> Maybe a, b -> Maybe t)
plus' (f0,g0) (f1,g1) =
  ( \s -> f0 s <|> f1 s
  , \b -> g0 b <|> g1 b
  )

-- class (Applicator p, Refractor p) => Compactor p where
--   full :: p a a
--   full = refract (\a -> (a,())) (\a () -> a) expelled

--   (><) :: p a b -> p a b -> p a b
--   p0 >< p1 = snd (decompress (p0 >*< p1))

-- class (Alternator p, Filtrator p) => Endeavor p where
--   devoid :: p a a
--   devoid = dimapMaybe (\_ -> Nothing) (\_ -> Nothing) rooted

-- class (Alternator p, Filtrator p) => Endeavor p where
--   devoid :: p a a
--   devoid = dimapMaybe (\_ -> Nothing) (\_ -> Nothing) rooted

--   (>|<) :: p a b -> p a b -> p a b
--   p0 >|< p1 = snd (discriminate (p0 >+< p1))

-- class (Applicator p, Filtrator p) => Endeavor p where
--   nope :: p a a
--   nope = dimapMaybe (\_ -> Nothing) (\_ Nothing) expelled

  -- (>|<) :: p a b -> p a b -> p a b

-- (>++<) :: Endeavor p => p a0 b0 -> p a1 b1 -> p (Either a0 a1) (Either b0 b1)
-- p0 >++< p1 =
--   dimapMaybe (either Just (\_ -> Nothing)) (Just . Left) p0 >|<
--   dimapMaybe (either (\_ -> Nothing) Just) (Just . Right) p1

-- https://pi.math.cornell.edu/~maguiar/a.pdf
-- other info
