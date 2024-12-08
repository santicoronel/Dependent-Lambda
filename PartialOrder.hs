module PartialOrder where

-- TODO no es orden parcial

data PO = PO {
  nv :: Int,
  re :: [(Int, Int)]
}

empty :: PO
empty = PO 0 []

newVar :: PO -> (Int, PO)
newVar (PO nv re) = (nv, PO (nv + 1) re)

addRel :: PO -> Int -> Int -> PO
addRel (PO nv re) x y 
  | max x y < nv && min x y >= 0 = PO nv ((x, y) : re)
  | otherwise = error "PO: fuera de indice"

rel :: PO -> Int -> Int -> Bool
rel (PO nv re) x y = go x y
  where
  go x y
    | max x y < nv && min x y >= 0 = case lookup x re of
      Nothing -> False
      Just z -> (y == z) || go z y
    | otherwise = error "PO: fuera de indice"