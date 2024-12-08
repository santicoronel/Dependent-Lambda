module Context where

import Lang
import UnionFind ( UnionFind, insert )

-- TODO quizas llevar tipos y definiciones en distintos
-- binders
-- puedo pensar en sustituir y listo peeero bindear un pattern
-- es un problema

data LocalBinder = LBinder {
  localVar :: Int,
  localType :: Type,
  localDef :: Maybe Term
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
    } )

nameAt :: Context -> Int -> Name
nameAt ctx i = names ctx !! (varCount ctx - 1 - i)