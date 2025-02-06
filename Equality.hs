module Equality ( equal, tequal ) where

import Lang
import Reduce
import MonadTypeCheck
import Error

import Control.Monad.Except
import Control.Monad.Extra ( unlessM )

equal :: MonadTypeCheck m => Term -> Term -> m ()
equal t u = do
  rt <- reduceNF t
  ru <- reduceNF u
  equal' rt ru

equal' :: MonadTypeCheck m => Term -> Term -> m ()
equal' (V x) (V y) = case (x, y) of
  (Bound i, Bound j) -> unless (i == j) $ throwError (ENeq (V x) (V y))
  (Free i, Free j) -> unlessM (i `varEq` j) $ throwError (ENeq (V x) (V y))
  (Global n, Global m) -> unless (n == m) $ throwError (ENeq (V x) (V y))
  _ -> throwError (ENeq (V x) (V y))
equal' (Lam _ t) (Lam _ u) = equal' t u
equal' (Con c) (Con d)
  | c == d = return ()
equal' (Data (Eq t u)) (Data (Eq r s)) = equal' t r >> equal' u s
equal' (Data d1) (Data d2)
  | d1 == d2 = return ()
equal' (Elim t tbs) (Elim u ubs) = do
  equal' t u
  bequal tbs ubs
equal' (Fix _ _ t) (Fix _ _ u) = equal' t u
equal' (Pi _ ty) (Pi _ uy) = equal' (unType ty) (unType uy)
equal' (Sort s) (Sort t) = s `sequal` t
equal' (Ann t _) u = equal' t u
equal' t (Ann u _) = equal' t u

equal' (t1 :@: u1) (t2 :@: u2) = equal' t1 t2 >> equal' u1 u2

equal' t u = throwError (ENeq t u)

tequal :: MonadTypeCheck m => Type -> Type -> m ()
tequal t u = unType t `equal` unType u

sequal :: MonadTypeCheck m => Sort -> Sort -> m ()
sequal s@(Set i) t@(Set j) =
  when (i /= j) (throwError (ENeq (Sort s) (Sort t)))

bequal :: MonadTypeCheck m => [ElimBranch] -> [ElimBranch] -> m ()
bequal (b1 : bs1) bs2 =
  case findBranch (elimCon b1) bs2 of
    Nothing -> bequal bs1 bs2
    Just (b2, bs2') -> do
      equal' (elimRes b1) (elimRes b2)
      bequal bs1 bs2'
bequal [] [] = return ()
bequal _ _ = throwError ENeqBranch