module Data.Functor2 where

class Functor2 f where fmap2 :: (a -> b) -> f a c -> f b c;
