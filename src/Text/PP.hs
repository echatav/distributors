module Text.PP where

import Control.Applicative
import Control.Distributor
import Data.Bifunctor
import Data.Bool
import Data.Profunctor

data PP s a b = PP
  { printer :: a -> s -> Maybe s
  , parser :: s -> [(b, s)]
  }
instance Profunctor (PP s) where
  dimap f g pp = PP (printer pp . f) (map (first g) . parser pp)
instance Monoid s => Bimodule (PP s) where
  expel b = PP (\_ -> Just) (\s -> [(b,s)])
  factor f g pp0 pp1 = PP printer' parser'
    where
      printer' a s = do
        let (fa0, fa1) = f a
        s' <- printer pp0 fa0 s
        printer pp1 fa1 s'
      parser' s = do
        (b0, s0) <- parser pp0 s
        (b1, s1) <- first (g b0) <$> parser pp1 s0
        return (b1, s1)
instance Monoid s => Distributor (PP s) where
  root f = PP (\_ _ -> Nothing) (\_ -> [])
  branch f g pp0 pp1 = PP printer' parser'
    where
      printer' a = either (printer pp0) (printer pp1) (f a)
      parser' s = do
        (b0,s0) <- parser pp0 s
        (b1,s1) <- parser pp1 s
        [(g (Left b0), s0), (g (Right b1), s1)]

end :: PP [t] () ()
end = PP (\_ -> Just) (bool [] [((),[])] . null)

token :: (a -> Maybe t) -> (t -> Maybe b) -> PP [t] a b
token f g = PP printer' parser'
  where
    printer' a ts = case f a of
      Nothing -> Nothing
      Just t -> Just (t:ts)
    parser' [] = []
    parser' (t:ts) = case g t of
      Nothing -> []
      Just b -> [(b,ts)]
