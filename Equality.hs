module Equality ( equal, tequal ) where

import Lang
import Reduce
import MonadTypeCheck
import Error

import Control.Monad.Except
import Control.Monad.State
import Control.Monad ( zipWithM_ )
import Context (freshVar)
import Substitution

-- NICETOHAVE usar reduceHead
-- TODO ver uf
equal :: MonadTypeCheck m => Term -> Term -> m ()
equal t u = do
  rt <- reduceNF t
  ru <- reduceNF u
  go rt ru
  where
    go :: MonadTypeCheck m => Term -> Term -> m ()
    go t1@(V (Free x)) t2@(V (Free y)) = do
      xeqy <- x `varEq` y
      unless xeqy (throwError (ENeq t1 t2))
    go (Lam a1 t) (Lam a2 u) = doAndRestore (do
      -- TODO hacer en MonadTypeCheck
      i1 <- state (freshVar (argName a1))
      i2 <- state (freshVar (argName a2))
      unifyVars i1 i2
      go (open i1 t) (open i2 u)
      )
    go (Con c) (Con d)
      | c == d = return ()
    go (Data d1) (Data d2)
      | d1 == d2 = return ()
    go (Elim (V (Free x)) xbs) (Elim (V (Free y)) ybs) = do
      equal (V (Free x)) (V (Free y))
      bequalV x y xbs ybs
    go t1@(Elim t tbs) t2@(Elim u ubs) =do
      equal t u
      bequal tbs ubs
    go (Fix f fa _ t) (Fix g ga _ u) = doAndRestore (do
      fi <- state (freshVar f)
      gi <- state (freshVar g)
      unifyVars fi gi
      fai <- state (freshVar (argName fa))
      gai <- state (freshVar (argName ga))
      unifyVars fai gai
      go (open2 fi fai t) (open2 gi gai u)
      )
    go (Pi a1 ty) (Pi a2 uy) = doAndRestore (do
      i1 <- state (freshVar (argName a1))
      i2 <- state (freshVar (argName a2))
      unifyVars i1 i2
      openType i1 ty `tequal` openType i2 uy)
    go (Sort s) (Sort t) = s `sequal` t
    go (Ann t _) u = go t u
    go t (Ann u _) = go t u
    
    go (t1 :@: u1) (t2 :@: u2) = equal t1 t2 >> equal u1 u2

    go (V (Bound _)) _ = error "bound in reduced"
    go _ (V (Bound _)) = error "bound in reduced"
    
    go (Elim _ _) _ = error "elim in reduced"
    go _ (Elim _ _) = error "elim in reduced"
    

    go t u = throwError (ENeq t u)


tequal :: MonadTypeCheck m => Type -> Type -> m ()
tequal t u = unType t `equal` unType u

sequal :: MonadTypeCheck m => Sort -> Sort -> m ()
sequal s@(Set i) t@(Set j) =
  when (i /= j) (throwError (ENeq (Sort s) (Sort t)))

-- asumo que tipa, y que las branches estan correctas
bequalV :: MonadTypeCheck m => Int -> Int -> [ElimBranch] -> [ElimBranch] -> m ()
bequalV x y (ElimBranch c a1 r1 : bs) b2 =
  let (ElimBranch _ a2 r2, b2') = findBranch c b2
  in  doAndRestore (do
        is1 <- mapM (state . freshVar) a1
        is2 <- mapM (state . freshVar) a2
        zipWithM_ unifyVars is1 is2
        let dx = foldl (:@:) (Con c) (map var is1)
            dy = foldl (:@:) (Con c) (map var is2)
        bindPattern x dx
        bindPattern y dy
        let r1' = foldr open r1 is1
            r2' = foldr open r2 is2
        equal r1' r2')
      >> bequalV x y bs b2'

bequal :: MonadTypeCheck m => [ElimBranch] -> [ElimBranch] -> m ()
bequal (b1 : bs1) bs2 =
  let (b2, bs2') = findBranch (elimCon b1) bs2
  in  doAndRestore (do
    is1 <- mapM (state . freshVar) (elimConArgs b1)
    is2 <- mapM (state . freshVar) (elimConArgs b2)
    zipWithM_ unifyVars is1 is2
    let r1 = foldr open (elimRes b1) is1
        r2 = foldr open (elimRes b2) is2
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