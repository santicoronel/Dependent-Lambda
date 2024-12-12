module Context where

import Lang
import UnionFind ( UnionFind, insert )
import qualified UnionFind as UF

-- TODO ver uso del contexto
-- creo q se esta haciendo muy grande muy rapido
-- chequear si estoy usando doAndRestore siempre q se puede
-- o si el problema esta en otro lado (dios nos libre
-- puede q solo sea en la reduccion recursiva, i.e. stack

data LocalBinder = LBinder {
  localVar :: Int,
  localType :: Type
} deriving Show

data LocalDef = LDef {
  defVar :: Int,
  localDef :: Term
} deriving Show

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