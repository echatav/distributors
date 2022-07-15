module Control.Bimodule where

class Bimodule p where

  expel :: b -> p a b
  expelled :: p () ()
  
  factor
    :: (a0 -> a1 -> a)
    -> (b -> (b0, b1))
    -> p a b
    -> p (a0, a1) (b0, b1)
  (>*<) :: p a0 b0 -> p a1 b1 -> p (a0,a1) (b0,b1)

class (forall q. Bimodule (c q)) => FreeBimodule c where

module Control.Distributor

class Bimodule p => Distributor p where

  root :: (a -> Void) -> p a b
  rooted :: p Void Void

  branch
    :: (Either a0 a1 -> a)
    -> (b -> Either b0 b1)
    -> p a b
    -> p (Either a0 a1) (Either b0 b1)
  (>|<) :: p a0 b0 -> p a1 b1 -> p (Either a0 a1) (Either b0 b1)

class (forall q. Distributor (c q)) => FreeDistributor c where

module Text.PP

data PP text a b = PP
  { printer :: a -> Maybe text
  , parser :: text -> [(b, text)]
  }
