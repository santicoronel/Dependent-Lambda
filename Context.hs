module Context where

import Lang
import UnionFind ( UnionFind )

-- TODO no voy a hacer analisis de terminacion durante typechecking
-- con un bool me alcanza
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