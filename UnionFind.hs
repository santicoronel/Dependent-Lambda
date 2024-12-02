module UnionFind where

type UnionFind x = ()

addNode :: UnionFind x -> x -> Maybe (UnionFind x)
addNode uf x = Nothing

removeNode :: UnionFind x -> x -> Maybe (UnionFind x)
removeNode uf x = Nothing

union :: UnionFind x -> x -> x -> Maybe (UnionFind x)
union uf x y = Nothing

find :: UnionFind x -> x -> Maybe x
find uf x = Nothing