module Equality ( equal, tequal ) where

import Lang
import Reduce
import MonadTypeCheck
import Error

import Control.Monad.Except
import Control.Monad ( zipWithM_ )

-- NICETOHAVE usar reduceHead
equal :: MonadTypeCheck m => Term -> Term -> m ()
equal t u = do
  rt <- reduceNF t
  ru <- reduceNF u
  go rt ru
  where
    go t1@(V (Local x)) t2@(V (Local y)) = do
      x' <- findVar x
      y' <- findVar y
      when (x' /= y') throwError (ENeq t1 t2)
    go (Lam a1 (Scope t)) (Lam a2 (Scope u)) = doAndRestore id (do
      unifyVars (argName a1) (argName a2) -- aca no tengo nodo de uf
      go t u
      )
    go (Con c) (Con d)
      | c == d = return ()
    go (Data d1) (Data d2)
      | d1 == d2 = return ()
    go t1@(Elim t tbs) t2@(Elim u ubs) = equal t u >> bequal tbs ubs
    go (Fix f fa _ t) (Fix g ga _ u) = doAndRestore id (do
      unifyVars f g
      unifyVars (argName fa) (argName ga)
      go t u
      )
    go (Pi a1 (Scope ty)) (Pi a2 (Scope uy)) = doAndRestore id (do
      unifyVars (argName a1) (argName a2)
      ty `tequal` uy)
    go (Sort s) (Sort t) = s `sequal` t
    go (Ann t _) u = go t u
    go t (Ann u _) = go t u
    
    go (t1 :@: u1) (t2 :@: u2) = equal t1 t2 >> equal u1 u2

    go (Elim _ _) _ = error "elim in reduced"
    go _ (Elim _ _) = error "elim in reduced"
    
    go t u = throwError (ENeq t u)


tequal :: MonadTypeCheck m => Type -> Type -> m ()
tequal t u = unType t `equal` unType u

sequal :: MonadTypeCheck m => Sort -> Sort -> m ()
sequal s@(Set i) t@(Set j) =
  when (i /= j) (throwError (ENeq (Sort s) (Sort t)))

-- asumo que tipa, y que las branches estan correctas
bequal :: MonadTypeCheck m => Name -> Name -> [ElimBranch] -> [ElimBranch] -> m ()
bequal x y (ElimBranch c a1 r1 : bs) b2 =
  let (ElimBranch _ a2 r2, b2') = findBranch c b2
  in  doAndRestore id (do
        zipWithM_ unifyVars a1 a2
        let dx = Con c (map var a1)
            dy = Con c (map var a2)
        bindPattern x dx
        bindPattern y dy
        equal r1 r2)
      >> bequal x y bs b2'

findBranch :: ConHead -> [ElimBranch] -> (ElimBranch, [ElimBranch])
findBranch c [] = error "findBranch"
findBranch c (b : bs)
  | elimCon b == c = (b, bs)
  | otherwise = 
    let (b', bs') = findBranch c bs
    in  (b', b : bs')
