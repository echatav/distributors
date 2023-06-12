{-# LANGUAGE
ConstraintKinds
, FlexibleContexts
, FlexibleInstances
, FunctionalDependencies
, GADTs
, MultiParamTypeClasses
, QuantifiedConstraints
, RankNTypes
, TupleSections
, UndecidableInstances
#-}

module Control.Token where

import Control.Applicative
import Control.Distributor
import Control.Lens
import Control.Monad
import Control.Monad.State
import Data.Char
import Data.Maybe (listToMaybe)
import Data.Profunctor
import Data.String
import Data.Void
import Witherable

-- Equality < Iso < Prism < Token
type Token s t a b =
  forall p f. (Choice p, Cochoice p, Applicative f, Filterable f)
    => p a (f b) -> p s (f t)

partialIso :: (s -> Maybe a) -> (b -> Maybe t) -> Token s t a b
partialIso f g = dimap f' g' . right' where
  f' = maybe (Left ()) Right . f
  g' = catMaybes . either (const (pure Nothing)) (fmap g)

-- Token < AToken
type AToken s t a b =
  TokenP a b a (Maybe b) -> TokenP a b s (Maybe t)

class (Choice p, Cochoice p) => Discriminator p where
  discriminate :: p (Either a0 a1) (Either b0 b1) -> (p a0 b0, p a1 b1)
  discriminate p =
    ( partialIso (Just . Left) (either Just (\_ -> Nothing)) <$< p
    , partialIso (Just . Right) (either (\_ -> Nothing) Just) <$< p
    )
  (<$<) :: AToken s t a b -> p a b -> p s t
  (<$<) k = withToken k $ \f g ->
    let
      f' = maybe (Left ()) Right . f
      g' = maybe (Left ()) Right . g
    in
      snd . discriminate . dimap (either Left f') (>>= g') . right'
infixr 4 <$<

withToken :: AToken s t a b -> ((s -> Maybe a) -> (b -> Maybe t) -> r) -> r
withToken k tok = case k (TokenP Just (Just . Just)) of
  TokenP f g -> tok f (join . g)

cloneToken :: AToken s t a b -> Token s t a b
cloneToken k = withToken k $ \f g -> partialIso f g

mirrorToken :: AToken s t a b -> Token b a t s
mirrorToken k = withToken k $ \f g -> partialIso g f

class
  ( Discriminator p
  , Distributor p
  , forall a b. Monoid (p a b)
  ) => Syntax c d p | p -> c, p -> d where
    look1 :: p c d

token :: Syntax c d p => AToken s t c d -> p s t
token k = k <$< look1

data TokenP a b s t = TokenP (s -> Maybe a) (b -> Maybe t)

instance Profunctor (TokenP a b) where
  dimap f' g' (TokenP f g) = TokenP (f . f') (fmap g' . g)
instance Semigroup (TokenP a b s t) where
  TokenP f g <> TokenP f' g' =
    TokenP (\s -> f s <|> f' s) (\b -> g b <|> g' b)
instance Monoid (TokenP a b s t) where
  mempty = TokenP nope nope where
    nope _ = Nothing
instance Choice (TokenP a b) where
  left' (TokenP f g) = TokenP (either f (\_ -> Nothing)) (fmap Left . g)
  right' (TokenP f g) = TokenP (either (\_ -> Nothing) f) (fmap Right . g)
instance Cochoice (TokenP a b) where
  unleft (TokenP f g) = TokenP f' g' where
    f' a = f (Left a)
    g' b = case g b of
      Just (Left b') -> Just b'
      _ -> Nothing
  unright (TokenP f g) = TokenP f' g' where
    f' a = f (Right a)
    g' b = case g b of
      Just (Right b') -> Just b'
      _ -> Nothing
instance Monoid a => Bimodule (TokenP a b) where
  expelled = TokenP (\_ -> Just mempty) (\_ -> Just ())
  TokenP f0 g0 >*< TokenP f1 g1 = TokenP
    (\(a0,a1) -> (<>) <$> f0 a0 <*> f1 a1)
    (\b -> (,) <$> g0 b <*> g1 b) -- this does the wrong thing!
instance Monoid a => Distributor (TokenP a b) where
  rooted = mempty
  TokenP f0 g0 >|< TokenP f1 g1 = TokenP
    (either f0 f1)
    (\b -> Left <$> g0 b <|> Right <$> g1 b)
instance Discriminator (TokenP a b) where
  discriminate (TokenP f g) = (TokenP f' g', TokenP f'' g'') where
    f' = f . Left
    g' = either Just (\_ -> Nothing) <=< g
    f'' = f . Right
    g'' = either (\_ -> Nothing) Just <=< g
  -- k <$< TokenP f g = withToken k $ \f' g' -> TokenP (f' >=> f) (g' <=< g)
instance (Monoid s, Cons s s c c, Cons t t d d)
  => Syntax c d (TokenP s t) where
    look1 = TokenP (\a -> Just (cons a mempty)) (fmap fst . uncons)

toTokenP :: AToken s t a b -> TokenP a b s t
toTokenP k = withToken k TokenP

fromTokenP :: TokenP a b s t -> Token s t a b
fromTokenP (TokenP f g) = partialIso f g

satisfy :: (t -> Bool) -> Token t t t t
satisfy cond = partialIso satiate satiate where
  satiate t = if cond t then Just t else Nothing

the :: Eq t => t -> Token t t t t
the t = satisfy (== t)

the_ :: Eq t => t -> Token () () t t
the_ t = ignore t . the t

notThe :: Eq t => t -> Token t t t t
notThe t = satisfy (/= t)

oneOf :: Eq t => [t] -> Token t t t t
oneOf ts = satisfy (`elem` ts)

notOneOf :: Eq t => [t] -> Token t t t t
notOneOf ts = satisfy (`notElem` ts)

(>+<)
  :: AToken s t a b
  -> AToken s t a b
  -> Token s t a b
k >+< k' = withToken k $ \f g -> withToken k' $ \f' g' ->
  partialIso (liftA2 (<|>) f f') (liftA2 (<|>) g g')

(><)
  :: AToken s t a b
  -> AToken s' t' a' b'
  -> Token (s,s') (t,t') (a,a') (b,b')
k >< k' = withToken k $ \f g -> withToken k' $ \f' g' ->
  partialIso (tuple f f') (tuple g g')
    where
      tuple h h' (u,u') = (,) <$> h u <*> h' u'

associate :: Token (a,(b,c)) (a',(b',c')) ((a,b),c) ((a',b'),c')
associate = partialIso f g where
  f (a,(b,c)) = Just ((a,b),c)
  g ((a,b),c) = Just (a,(b,c))

unit :: Token a b (a,()) (b,())
unit = partialIso f g where
  f a = Just (a,())
  g (a,()) = Just a

ignore :: s -> Iso () () s t
ignore s = dimap (\() -> s) (fmap (\_t -> ()))

iterateToken :: AToken a b a b -> Iso a b a b
iterateToken k = withToken k $ \f g ->
  dimap (iter f) (fmap (iter g)) where
    iter step state = maybe state (iter step) (step state)

step
  :: AToken (a,a') (b,b') a b
  -> Token (a,[a']) (b,[b']) (a,[a']) (b,[b'])
step k
  = (id >< mirrorToken cons')
  . associate
  . (k >< id)

nil' :: Token () () [a] [b]
nil' = partialIso f g where
  f () = Just []
  g [] = Just ()
  g _ = Nothing

cons' :: Token (a,[a]) (b,[b]) [a] [b]
cons' = partialIso f g where
  f (x,xs) = Just (x:xs)
  g (x:xs) = Just (x,xs)
  g _ = Nothing

foldToken :: AToken (a,a') (b,b') a b -> Token (a,[a']) (b,[b']) a b
foldToken k
  = iterateToken (step k)
  . (id >< mirrorToken nil')
  . mirrorToken unit
  
chainl1
  :: (Distributor p, Discriminator p)
  => p s t -> p a b
  -> Token (t,(b,t)) (s,(a,s)) t s -> p s t
chainl1 arg op f = mirrorToken (foldToken f) <$< (arg >*< several (op >*< arg))

control, space
  , lower, upper, alpha, alphaNum, printChar
  , digit, octDigit, hexDigit
  , letter, mark, number, punctuation, symbol, separator
  , ascii, latin1, asciiUpper, asciiLower
  :: Token Char Char Char Char
control = satisfy isControl
space = satisfy isSpace
lower = satisfy isLower
upper = satisfy isUpper
alpha = satisfy isAlpha
alphaNum = satisfy isAlphaNum
printChar = satisfy isPrint
digit = satisfy isDigit
octDigit = satisfy isOctDigit
hexDigit = satisfy isHexDigit
letter = satisfy isLetter
mark = satisfy isMark
number = satisfy isNumber
punctuation = satisfy isPunctuation
symbol = satisfy isSymbol
separator = satisfy isSeparator
ascii = satisfy isAscii
latin1 = satisfy isLatin1
asciiUpper = satisfy isAsciiUpper
asciiLower = satisfy isAsciiLower

syntaxString :: (Cons s s c c, Syntax c c p, Eq c) => s -> p () ()
syntaxString s = case uncons s of
  Nothing -> expelled
  Just (c,cs) -> token (the_ c) >* syntaxString cs

data PP f a b s t = PP
  { printPP :: s -> Maybe a
  , parsePP :: b -> f (t,b)
  }

instance Functor f => Profunctor (PP f a b) where
  dimap f' g' (PP f g) = PP (f . f') (fmap (first' g') . g)
instance Functor f => Choice (PP f a b) where
  left' (PP f g) =
    PP (either f (\_ -> Nothing)) (fmap (first' Left) . g)
  right' (PP f g) =
    PP (either (\_ -> Nothing) f) (fmap (first' Right) . g)
instance Filterable f => Cochoice (PP f a b) where
  unleft (PP f g) = PP (f . Left) (mapMaybe l . g) where
    l (Left a, b) = Just (a,b)
    l _ = Nothing
  unright (PP f g) = PP (f . Right) (mapMaybe r . g) where
    r (Right a, b) = Just (a,b)
    r _ = Nothing
instance (MonadPlus f, Monoid a) => Bimodule (PP f a b) where
  expelled = PP (\_ -> Just mempty) (\b -> return ((), b))
  PP f0 g0 >*< PP f1 g1 = PP f' g' where
    f' (a0,a1) = (<>) <$> f0 a0 <*> f1 a1
    g' b = do
      (b0,b') <- g0 b
      (b1,b'') <- g1 b'
      return ((b0,b1),b'')
instance (MonadPlus f, Monoid a) => Distributor (PP f a b) where
  rooted = mempty
  PP f0 g0 >|< PP f1 g1 = PP
    (either f0 f1)
    (\b -> first' Left <$> g0 b <|> first' Right <$> g1 b)
instance MonadPlus f => Semigroup (PP f a b s t) where
  PP f g <> PP f' g' =
    PP (\s -> f s <|> f' s) (\b -> g b <|> g' b)
instance MonadPlus f => Monoid (PP f a b s t) where
  mempty = PP (\_ -> Nothing) (\_ -> empty)
instance Filterable f => Discriminator (PP f a b) where
  k <$< PP f g = withToken k $ \f' g' ->
    let g'' = \(b1, b) -> fmap (\t -> (t,b)) (g' b1)
    in PP (f' >=> f) (mapMaybe g'' . g)
instance (Monoid s, Cons s s c c, Cons t t d d, Filterable f, MonadPlus f)
  => Syntax c d (PP f s t) where
    look1 = PP (\a -> Just (cons a mempty)) (maybe empty pure . uncons)
instance
  ( Filterable f
  , MonadPlus f
  , Monoid s
  , Cons s s Char Char
  , Cons t t Char Char
  , a ~ ()
  , b ~ ()
  ) => IsString (PP f s t a b) where
  fromString = syntaxString

manySyntax :: Syntax c d p => p a b -> p [a] [b]
manySyntax p = many_p where
  many_p = some_p <> expel []
  some_p = _Cons <$< p >*< many_p
