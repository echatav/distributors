module Text.PP where

import Control.Applicative
import Control.Distributor
import Data.Bifunctor
import Data.Bool
import Data.Profunctor

data PP s t a b = PP
  { printer :: a -> s -> Maybe s
  , parser :: t -> [(b, t)]
  }
instance Profunctor (PP s t) where
  dimap f g pp = PP (printer pp . f) (map (first g) . parser pp)
instance Bimodule (PP s t) where
  expel b = PP (\_ -> Just) (\t -> [(b,t)])
  factor f g pp0 pp1 = PP printer' parser'
    where
      printer' a s = do
        let (fa0, fa1) = f a
        s' <- printer pp0 fa0 s
        printer pp1 fa1 s'
      parser' t = do
        (b0, t0) <- parser pp0 t
        (b1, t1) <- first (g b0) <$> parser pp1 t0
        return (b1, t1)
instance Distributor (PP s t) where
  root f = PP (\_ _ -> Nothing) (\_ -> [])
  branch f g pp0 pp1 = PP printer' parser'
    where
      printer' a = either (printer pp0) (printer pp1) (f a)
      parser' t = do
        (b0,t0) <- parser pp0 t
        (b1,t1) <- parser pp1 t
        [(g (Left b0), t0), (g (Right b1), t1)]

end :: PP [s] [t] () ()
end = PP (\_ -> Just) (bool [] [((),[])] . null)

token :: (a -> Maybe s) -> (t -> Maybe b) -> PP [s] [t] a b
token f g = PP printer' parser'
  where
    printer' a ts = case f a of
      Nothing -> Nothing
      Just t -> Just (t:ts)
    parser' [] = []
    parser' (t:ts) = case g t of
      Nothing -> []
      Just b -> [(b,ts)]
