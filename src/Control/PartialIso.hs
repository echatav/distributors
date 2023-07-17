{-# LANGUAGE
RankNTypes
#-}

module Control.PartialIso where

import Control.Applicative
import Control.Monad
import Data.Profunctor
import Witherable

type PartialIso s t a b =
  forall p f. (Choice p, Cochoice p, Applicative f, Filterable f)
    => p a (f b) -> p s (f t)

partialIso :: (s -> Maybe a) -> (b -> Maybe t) -> PartialIso s t a b
partialIso f g = dimap f' g' . right' where
  f' = maybe (Left ()) Right . f
  g' = catMaybes . either (const (pure Nothing)) (fmap g)

type APartialIso s t a b =
  Token a b a (Maybe b) -> Token a b s (Maybe t)

withPartialIso
  :: APartialIso s t a b
  -> ((s -> Maybe a) -> (b -> Maybe t) -> r)
  -> r
withPartialIso k tok = case k (Token Just (Just . Just)) of
  Token f g -> tok f (join . g)

clonePartialIso :: APartialIso s t a b -> PartialIso s t a b
clonePartialIso k = withPartialIso k $ \f g -> partialIso f g

mirrorPartialIso :: APartialIso s t a b -> PartialIso b a t s
mirrorPartialIso k = withPartialIso k $ \f g -> partialIso g f

class (Choice p, Cochoice p) => Discriminator p where

  discriminate :: p (Either a0 a1) (Either b0 b1) -> (p a0 b0, p a1 b1)
  discriminate p =
    ( partialIso (Just . Left) (either Just (pure Nothing)) <$< p
    , partialIso (Just . Right) (either (pure Nothing) Just) <$< p
    )

  (<$<) :: APartialIso s t a b -> p a b -> p s t
  infixr 4 <$<
  (<$<) k = withPartialIso k $ \f g ->
    let
      f' = maybe (Left ()) Right . f
      g' = maybe (Left ()) Right . g
    in
      snd . discriminate . dimap (either Left f') (>>= g') . right'

  (>$>) :: APartialIso b a t s -> p a b -> p s t
  infixr 4 >$>
  optic >$> p = mirrorPartialIso optic <$< p

data Token a b s t = Token (s -> Maybe a) (b -> Maybe t)
instance Semigroup (Token a b s t) where
  Token f g <> Token f' g' =
    Token ((<|>) <$> f <*> f') ((<|>) <$> g <*> g')
instance Monoid (Token a b s t) where
  mempty = Token (pure Nothing) (pure Nothing) where
instance Functor (Token a b s) where fmap = rmap
instance Filterable (Token a b s) where
  mapMaybe h (Token f g) = Token f (h <=< g)
instance Profunctor (Token a b) where
  dimap f' g' (Token f g) = Token (f . f') (fmap g' . g)
instance Choice (Token a b) where
  left' (Token f g) = Token
    (either f (pure Nothing)) (fmap Left . g)
  right' (Token f g) = Token
    (either (pure Nothing) f) (fmap Right . g)
instance Cochoice (Token a b) where
  unleft (Token f g) = Token f' g' where
    f' a = f (Left a)
    g' b = case g b of
      Just (Left b') -> Just b'
      _ -> Nothing
  unright (Token f g) = Token f' g' where
    f' a = f (Right a)
    g' b = case g b of
      Just (Right b') -> Just b'
      _ -> Nothing
instance Discriminator (Token a b) where
  discriminate (Token f g) = (Token f' g', Token f'' g'') where
    f' = f . Left
    g' = either Just (pure Nothing) <=< g
    f'' = f . Right
    g'' = either (pure Nothing) Just <=< g

toToken :: APartialIso s t a b -> Token a b s t
toToken k = withPartialIso k Token

fromToken :: Token a b s t -> PartialIso s t a b
fromToken (Token f g) = partialIso f g
