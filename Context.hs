module Context where

import Lang
import UnionFind ( UnionFind, insert )

data LocalBinder = LBinder {
  localVar :: Int,
  localType :: Type
}

data LocalDef = LDef {
  defVar :: Int,
  localDef :: Term
}

data GlobalBinder = GBinder {
  globalName :: Name,
  globalType :: Type,
  globalDef :: Term
}

data Context = TC {
  varCount :: Int,
  names :: [Name],
  local :: [LocalBinder],
  localDefs :: [LocalDef],
  global :: [GlobalBinder],
  datadefs :: [DataDef],
  unif :: UnionFind Int
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