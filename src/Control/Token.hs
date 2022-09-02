{-# LANGUAGE
FlexibleInstances
, FunctionalDependencies
, LambdaCase
, MultiParamTypeClasses
#-}

module Control.Token where

import Data.Bool
import Data.Profunctor
import Control.Monad ((<=<))

data Token a b s t = Token (s -> Maybe a) (b -> Maybe t)

instance Profunctor (Token a b) where
  dimap f g (Token unlex lex) = Token (unlex . f) (fmap g . lex)

instance Choice (Token a b) where
  right' (Token unlex lex) =
    Token (either (const Nothing) unlex) (fmap Right . lex)

instance Cochoice (Token a b) where
  unright (Token unlex lex) =
    Token (unlex . Right) (either (const Nothing) Just <=< lex)

toChoice :: (Choice p, Cochoice p) => Token a b s t -> p a b -> p s t
toChoice (Token unlex lex) =
  let
    eitherToMaybe = either (const Nothing) Just
    maybeToEither = maybe (Left ()) Right
    conjugate k = maybeToEither . (k <=< eitherToMaybe)
  in
    unright . dimap (conjugate unlex) (conjugate lex) . right'

fromChoice :: (Token a b a b -> Token a b s t) -> Token a b s t
fromChoice p = p (Token Just Just)

class LiftToken a b p | p -> a b where
  liftToken :: Token a b s t -> p s t

instance LiftToken s t (Token s t) where liftToken = id

satisfy :: LiftToken a a p => (a -> Bool) -> p a a
satisfy cond =
  let
    satiate = bool <$> const Nothing <*> Just <*> cond
  in
    liftToken (Token satiate satiate)
