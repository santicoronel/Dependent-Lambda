module Transitive where

newtype Transitive a = Transitive [(a , a)]

empty :: Eq a => Transitive a
empty = Transitive []

addRel :: Eq a => Transitive a -> a -> a -> Transitive a
addRel (Transitive re) x y = Transitive ((x, y) : re)

rel :: Eq a => Transitive a -> a -> a -> Bool
rel (Transitive re) x y = go x y
  where
  go x y = case lookup x re of
    Nothing -> False
    Just z -> (y == z) || go z y