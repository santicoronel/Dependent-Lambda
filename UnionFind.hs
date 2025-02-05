module UnionFind where

import qualified Data.DisjointSet as DS

newtype UnionFind x = UnionFind { ds :: DS.DisjointSet x }

empty :: Ord x => UnionFind x
empty = UnionFind DS.empty

insert :: Ord x => UnionFind x -> x -> UnionFind x
insert (UnionFind ds) x = UnionFind (DS.insert x ds) 

union :: Ord x => UnionFind x -> x -> x -> UnionFind x
union (UnionFind ds) x y = UnionFind (DS.union x y ds)

equivalent :: Ord x => UnionFind x -> x -> x -> Maybe (UnionFind x, Bool)
equivalent uf x y = do
  let (mrx, ds') = DS.representative' x (ds uf)
      (mry, ds'') = DS.representative' y ds'
  rx <- mrx
  ry <- mry
  return (uf { ds = ds'' }, rx == ry)