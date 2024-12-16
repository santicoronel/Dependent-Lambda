module Equality ( equal, tequal ) where

import Lang
import Reduce
import MonadTypeCheck
import Error
import Common

import Control.Monad.Except
import Control.Monad.State
import Control.Monad ( zipWithM_ )
import Context (freshVar)
import Substitution
import Control.Monad.Extra ( unlessM )


-- TODO no tiene sentido abrir lambdas/fix/elims
-- con de brujin tengo alfa equivalencia gratis

equal :: MonadTypeCheck m => Term -> Term -> m ()
equal t u = do
  rt <- reduceNF t
  ru <- reduceNF u
  equal' rt ru

equal' :: MonadTypeCheck m => Term -> Term -> m ()
equal' t1@(V (Free x)) t2@(V (Free y)) =
  unlessM (x `varEq` y) (throwError (ENeq t1 t2))
equal' (Lam a1 t) (Lam a2 u) = doAndRestore (do
  i1 <- newVar (argName a1)
  i2 <- newVar (argName a2)
  unifyVars i1 i2
  equal' (open i1 t) (open i2 u)
  )
equal' (Con c) (Con d)
  | c == d = return ()
equal' (Data (Eq t u)) (Data (Eq r s)) = equal' t r >> equal' u s
equal' (Data d1) (Data d2)
  | d1 == d2 = return ()
equal' (Elim (V (Free x)) xbs) (Elim (V (Free y)) ybs) = do
  equal' (V (Free x)) (V (Free y))
  bequalV x y xbs ybs
equal' t1@(Elim t tbs) t2@(Elim u ubs) = do
  equal' t u
  bequal tbs ubs
equal' (Fix f fa _ t) (Fix g ga _ u) = doAndRestore (do
  fi <- newVar f
  gi <- newVar g
  unifyVars fi gi
  fai <- newVar (argName fa)
  gai <- newVar (argName ga)
  unifyVars fai gai
  equal' (open2 fi fai t) (open2 gi gai u)
  )
equal' (Pi a1 ty) (Pi a2 uy) = doAndRestore (do
  i1 <- newVar (argName a1)
  i2 <- newVar (argName a2)
  unifyVars i1 i2
  openType i1 ty `tequal` openType i2 uy)
equal' (Sort s) (Sort t) = s `sequal` t
equal' (Ann t _) u = equal' t u
equal' t (Ann u _) = equal' t u

equal' (t1 :@: u1) (t2 :@: u2) = equal' t1 t2 >> equal' u1 u2

equal' (V (Bound i)) _ = error $ "equal: bound " ++ show i ++ " in reduced"
equal' _ (V (Bound i)) = error $ "equal: bound " ++ show i ++ " in reduced"

equal' t u = throwError (ENeq t u)


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
        -- TODO por que uso dos listas de variables??
        is1 <- mapM newVar a1
        is2 <- mapM newVar a2
        zipWithM_ unifyVars is1 is2
        let dx = foldl (:@:) (Con c) (map var is1)
            dy = foldl (:@:) (Con c) (map var is2)
        bindPattern x dx
        bindPattern y dy
        let r1' = openMany is1 r1
            r2' = openMany is2 r2
        equal' r1' r2')
      >> bequalV x y bs b2'
bequalV x y [] [] = return ()
bequalV x y bs b2 = error $ "Equality: error en branches " ++ show bs ++ " = " ++ show b2

bequal :: MonadTypeCheck m => [ElimBranch] -> [ElimBranch] -> m ()
bequal (b1 : bs1) bs2 =
  let (b2, bs2') = findBranch (elimCon b1) bs2
  in  doAndRestore (do
    is1 <- mapM newVar (elimConArgs b1)
    is2 <- mapM newVar (elimConArgs b2)
    zipWithM_ unifyVars is1 is2
    let r1 = openMany is1 (elimRes b1)
        r2 = openMany is2 (elimRes b2)
    equal' r1 r2
    )
    >> bequal bs1 bs2'
bequal [] [] = return ()
bequal bs b2 = error $ "Equality: error en branches " ++ show bs ++ " = " ++ show b2

findBranch :: ConHead -> [ElimBranch] -> (ElimBranch, [ElimBranch])
findBranch c [] = error "findBranch"
findBranch c (b : bs)
  | elimCon b == c = (b, bs)
  | otherwise = 
    let (b', bs') = findBranch c bs
    in  (b', b : bs')