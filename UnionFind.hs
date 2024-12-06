module UnionFind where

import qualified Data.DisjointSet as DS

-- TODO hacer removeNode solo para sanity check
-- i.e. sacarlo de mp, y cuando hacemos find nos aseguramos
-- de q exista
-- es mas costoso pero puede servir para debuggear

data UnionFind x = UnionFind {
  nn :: Int,
  ds :: DS.DisjointSet Int,
  mp :: [(x, Int)]
} 

empty :: Eq x => UnionFind x
empty = UnionFind 0 DS.empty []

insert :: Eq x => UnionFind x -> x -> UnionFind x
insert (UnionFind nn ds mp) x = UnionFind {
  nn = nn + 1,
  ds = DS.insert nn ds,
  mp = (x, nn) : mp
}

union :: Eq x => UnionFind x -> x -> x -> Maybe (UnionFind x)
union (UnionFind nn ds mp) x y = do
  xn <- lookup x mp
  yn <- lookup y mp
  return (UnionFind {
    nn = nn,
    ds = DS.union xn yn ds,
    mp = mp
})

equivalent :: Eq x => UnionFind x -> x -> x -> Maybe (UnionFind x, Bool)
-- aca hacemos compresion
equivalent uf x y = do
  xn <- lookup x (mp uf)
  yn <- lookup y (mp uf)
  let (mrx, ds') = DS.representative' xn (ds uf)
      (mry, ds'') = DS.representative' yn ds'
  rx <- mrx
  ry <- mry
  return (uf { ds = ds'' }, rx == ry)
-- aca no
equivalent uf x y = do
  xn <- lookup x (mp uf)
  yn <- lookup y (mp uf)
  return (uf, DS.equivalent xn yn (ds uf))
  