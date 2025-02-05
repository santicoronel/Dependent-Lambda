module Context where

import Lang
import UnionFind ( UnionFind, insert )
import qualified UnionFind as UF


data LocalBinder = LBinder {
  localVar :: Int,
  localType :: Type
} deriving Show

data LocalDef = LDef {
  defVar :: Int,
  localDef :: Term,
  localRec :: Bool
} deriving Show

data GlobalBinder = GBinder {
  globalName :: Name,
  globalType :: Type,
  globalDef :: Term
} deriving Show

data Context = TC {
  varCount :: Int,
  names :: [Name],
  local :: [LocalBinder],
  localDefs :: [LocalDef],
  global :: [GlobalBinder],
  datadefs :: [DataDef],
  unif :: UnionFind Int
}

emptyContext :: Context
emptyContext = TC {
  varCount = 0,
  names = [],
  local = [],
  localDefs = [],
  global = [],
  datadefs = [],
  unif = UF.empty
}

freshVar :: Name -> Context -> (Int, Context)
freshVar n ctx =
  let vc = varCount ctx
      ns = names ctx
      uf = unif ctx
  in  (vc, ctx {
    varCount = vc + 1,
    names = n : ns,
    unif = insert uf vc
    })

nameAt :: Context -> Int -> Name
nameAt ctx i = names ctx !! (varCount ctx - 1 - i)