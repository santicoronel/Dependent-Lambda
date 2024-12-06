module Equality ( equal, tequal ) where

import Lang
import Reduce
import MonadTypeCheck
import Error

import Control.Monad.Except
import Control.Monad ( zipWithM_ )

-- NICETOHAVE usar reduceHead
-- TODO ver uf
equal :: MonadTypeCheck m => Term -> Term -> m ()
equal t u = do
  rt <- reduceNF t
  ru <- reduceNF u
  go rt ru
  where
    go :: MonadTypeCheck m => Term -> Term -> m ()
    go t1@(V (Local x)) t2@(V (Local y)) = do
      xeqy <- x `varEq` y
      unless xeqy (throwError (ENeq t1 t2))
    go (Lam a1 (Scope t)) (Lam a2 (Scope u)) = doAndRestore (do
      insertUnifNode (argName a1)
      insertUnifNode (argName a2)
      unifyVars (argName a1) (argName a2) -- aca no tengo nodo de uf
      go t u
      )
    go (Con c) (Con d)
      | c == d = return ()
    go (Data d1) (Data d2)
      | d1 == d2 = return ()
    go (Elim (V (Local x)) xbs) (Elim (V (Local y)) ybs) = do
      equal (V (Local x)) (V (Local y))
      bequalV x y xbs ybs
    go t1@(Elim t tbs) t2@(Elim u ubs) =do
      equal t u
      bequal tbs ubs
    go (Fix f fa _ t) (Fix g ga _ u) = doAndRestore (do
      insertUnifNode f
      insertUnifNode g
      unifyVars f g
      insertUnifNode (argName fa)
      insertUnifNode (argName ga)
      unifyVars (argName fa) (argName ga)
      go t u
      )
    go (Pi a1 (Scope ty)) (Pi a2 (Scope uy)) = doAndRestore (do
      insertUnifNode (argName a1)
      insertUnifNode (argName a2)
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
bequalV :: MonadTypeCheck m => Name -> Name -> [ElimBranch] -> [ElimBranch] -> m ()
bequalV x y (ElimBranch c a1 r1 : bs) b2 =
  let (ElimBranch _ a2 r2, b2') = findBranch c b2
  in  doAndRestore (do
        mapM_ insertUnifNode a1
        mapM_ insertUnifNode a2
        zipWithM_ unifyVars a1 a2
        let dx = foldl (:@:) (Con c) (map var a1)
            dy = foldl (:@:) (Con c) (map var a2)
        bindPattern x dx
        bindPattern y dy
        equal r1 r2)
      >> bequalV x y bs b2'

bequal :: MonadTypeCheck m => [ElimBranch] -> [ElimBranch] -> m ()
bequal (b1 : bs1) bs2 =
  let (b2, bs2') = findBranch (elimCon b1) bs2
  in  doAndRestore (do
    mapM_ insertUnifNode (elimConArgs b1)
    mapM_ insertUnifNode (elimConArgs b2)
    zipWithM_ unifyVars (elimConArgs b1) (elimConArgs b2)
    equal (elimRes b1) (elimRes b2)  
    )
    >> bequal bs1 bs2'

findBranch :: ConHead -> [ElimBranch] -> (ElimBranch, [ElimBranch])
findBranch c [] = error "findBranch"
findBranch c (b : bs)
  | elimCon b == c = (b, bs)
  | otherwise = 
    let (b', bs') = findBranch c bs
    in  (b', b : bs')