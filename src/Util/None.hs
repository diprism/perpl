{-# LANGUAGE Rank2Types #-}
module Util.None where

import Control.Applicative (Alternative(..))

data None a = None deriving (Eq, Ord, Show)

instance Functor None where fmap _ None = None
instance Applicative None where pure _ = None; None <*> None = None
instance Alternative None where empty = None; None <|> None = None
instance Foldable None where foldMap _ None = mempty
instance Traversable None where traverse _ None = pure None

class HFunctor t where
  hmap :: (Functor f, Functor g) => (forall a. f a -> g a) -> t f -> t g
