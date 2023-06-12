{-# LANGUAGE
FlexibleContexts
, FlexibleInstances
, FunctionalDependencies
, GADTs
, MultiParamTypeClasses
, OverloadedStrings
, RankNTypes
, TemplateHaskell
, UndecidableInstances
#-}

module Text.PP where

import Control.Applicative
import Control.Distributor
import Control.Lens
import Control.Monad
import Control.Token
import Data.Bifunctor
import Data.Bool
import Data.Char
import Data.Profunctor
import Data.String
import Data.Void

data PP' s t c d = PP' (c -> Maybe s) (t -> [(d, t)])

instance Profunctor (PP' s t) where
  dimap f' g' (PP' f g)  = PP' (f . f') (map (first g') . g)

instance Choice (PP' s t) where
  left' (PP' f g) =
    PP' (either f (\_ -> Nothing)) (\t -> [(Left b, t') | (b,t') <- g t])
  right' (PP' f g) =
    PP' (either(\_ -> Nothing) f ) (\t -> [(Right b, t') | (b,t') <- g t])

instance Cochoice (PP' s t) where
  unleft (PP' f g) =
    PP' (f . Left) (\t -> [(b,t) | (Left b, t) <- g t])
  unright (PP' f g) =
    PP' (f . Right) (\t -> [(b,t) | (Right b, t) <- g t])

instance Discriminator (PP' s t) where
  k <$< PP' f g = withToken k $ \f' g' ->
    let
      f'' = f' >=> f
      g'' s = [(y,s') | (x,s') <- g s, Just y <- [g' x]]
    in PP' f'' g''

instance Monoid s => Bimodule (PP' s t) where
  expelled = PP' (\() -> Just mempty) (\t -> [((), t)])
  PP' f g >*< PP' f' g' = PP' f'' g'' where
    f'' (a,a') = (<>) <$> f a <*> f' a'
    g'' t = [((b,b'),t'') | (b,t') <- g t, (b',t'') <- g' t']

instance Monoid s => Distributor (PP' s t) where
  rooted = PP' absurd (\_ -> [])
  PP' f g >|< PP' f' g' = PP' f'' g'' where
    f'' = either f f'
    g'' t =
      [(Left b, t') | (b, t') <- g t] <>
      [(Right b', t'') | (b', t'') <- g' t]

instance Semigroup (PP' a b s t) where
  PP' f0 g0 <> PP' f1 g1 =
    PP' (\s -> f0 s <|> f1 s) (\b -> g0 b <> g1 b)
instance Monoid (PP' a b s t) where
  mempty = PP' (\_ -> Nothing) (\_ -> [])

instance (Monoid s, Cons s s c c, Cons t t d d)
  => Syntax c d (PP' s t) where
    look1= PP' (\a -> Just (cons a mempty)) (maybe [] pure . uncons)

instance (IsString s, Monoid s, Cons s s Char Char, Cons t t Char Char, a ~ (), b ~ ())
  => IsString (PP' s t a b) where
    fromString s = case uncons (fromString s) of
      Nothing -> expelled
      Just (c,cs) -> token (the_ c) *< fromString cs

skipSpace, optSpace, sepSpace
  :: (IsString s, Monoid s, Cons s s Char Char, Cons t t Char Char) => PP' s t () ()
skipSpace = ignore [] <$< several " "
optSpace = ignore [()] <$< several " "
sepSpace = " " *< skipSpace

data Operator
  = AddOp
  | MulOp
  deriving (Show,Eq)
makePrisms ''Operator

data Expression
  = Variable String
  | Literal Integer
  | BinOp Expression Operator Expression
  | IfZero Expression Expression Expression
  deriving (Show,Eq)
makePrisms ''Expression

expression :: PP' String String Expression Expression
expression = exp2 where
  keywords = ["ifzero","else"]
  identifier
    = (notOneOf keywords . _Cons) <$<
      (token letter >*< several (token letter <> token digit))
  integer = partialIso show' read' <$< several (token digit)
  read' s = case [x | (x,"") <- reads s] of
    [] -> Nothing
    x:_ -> Just (x::Integer)
  show' = Just . show
  parens p = "(" >* p *< ")"
  ops = (_MulOp <$< "*") <> (_AddOp <$< "+")
  spacedOps = optSpace >* ops *< optSpace
  priority MulOp = 1
  priority AddOp = 2
  triple :: Iso (a,b,c) (d,e,f) (a,(b,c)) (d,(e,f))
  triple = dimap (\(a,b,c) -> (a,(b,c))) (fmap (\(a,(b,c)) -> (a,b,c)))
  exp0 = (_Literal <$< integer)
    <> (_Variable <$< identifier)
    <> ((_IfZero . triple) <$< ifzero)
    <> parens (skipSpace >* expression *< skipSpace)
  exp1 = chainl1 exp0 spacedOps (binOpPrio 1)
  exp2 = chainl1 exp1 spacedOps (binOpPrio 2)
  ifzero = "ifzero" >*
    optSpace >* parens expression >*<
    optSpace >* parens expression >*<
    optSpace >* "else" >*
    optSpace >* parens expression
  binOpPrio n = mirrorToken $
    _BinOp . triple . satisfy (\(_,(op,_)) -> priority op == n)

-- (>||<) :: (Distributor p, ApToken p) => p a a -> p a a -> p a a
-- p >||< p' = (token _ _ :: forall a. AToken a a (Either a a) (Either a a)) (p >|< p')
