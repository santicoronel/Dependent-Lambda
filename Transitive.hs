module Transitive where

data Transitive = Transitive {
  nv :: Int,
  re :: [(Int, Int)]
}

empty :: Transitive
empty = Transitive 0 []

newVar :: Transitive -> (Int, Transitive)
newVar (Transitive nv re) = (nv, Transitive (nv + 1) re)

addRel :: Transitive -> Int -> Int -> Transitive
addRel (Transitive nv re) x y 
  | max x y < nv && min x y >= 0 = Transitive nv ((x, y) : re)
  | otherwise = error "Transitive: fuera de indice"

rel :: Transitive -> Int -> Int -> Bool
rel (Transitive nv re) x y = go x y
  where
  go x y
    | max x y < nv && min x y >= 0 = case lookup x re of
      Nothing -> False
      Just z -> (y == z) || go z y
    | otherwise = error "Transitive: fuera de indice"