module Context where

import Lang
import UnionFind ( UnionFind )

data LocalBinder = LBinder {
  localName :: Name,
  localType :: Type,
  localDef :: Maybe Term,
  recArg :: Maybe Name
  }

data GlobalBinder = GBinder {
  globalName :: Name,
  globalType :: Type,
  globalDef :: Term
}

-- solo tipos reducidos
data Context = TC {
  local :: [LocalBinder],
  global :: [GlobalBinder],
  datadefs :: [DataDef],
  unif :: UnionFind Name }