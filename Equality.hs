module Equality ( equal, tequal ) where

import Lang
import Reduce
import MonadTypeCheck
import Error

import Control.Monad.Except
import Control.Monad ( zipWithM_ )

equal :: MonadTypeCheck m => Term -> Term -> m ()
equal t u = do
  rt <- reduce t
  ru <- reduce u
  go rt ru
  where
    go t1@(V (Local x) xes) t2@(V (Local y) yes) = do
      x' <- findVar x
      y' <- findVar y
      if x' == y'
        then zipWithM_ go xes yes
        else do
          dx <- getLocalDef x
          case dx of
            Just t -> do
              t1' <- reduce (foldl (:@:) t xes)
              go t1' t2
            Nothing -> do
              dy <- getLocalDef y
              case dy of
                Just t -> do
                  t2' <- reduce (foldl (:@:) t yes)
                  go t1 t2'
                Nothing -> throwError (ENeq t1 t2)
    go t1@(V (Local x) xes) t2 = do
      dx <- getLocalDef x
      case dx of
        Nothing -> throwError (ENeq t1 t2)
        Just t -> do
          t1' <- reduce (foldl (:@:) t xes)
          go t1' t2
    go t1 t2@(V (Local y) yes) = do
      dy <- getLocalDef y
      case dy of
        Nothing -> throwError (ENeq t1 t2)
        Just t -> do
          t2' <- reduce (foldl (:@:) t yes)
          go t1 t2'
    go (V (Global x) xes) (V (Global y) yes)
      | x == y = catchError (zipWithM_ go xes yes)
        (\e -> case e of
          ENeq _ _ -> do
            dx <- getGlobalDef x
            dy <- getGlobalDef y
            t <- reduce (foldl (:@:) dx xes)
            u <- reduce (foldl (:@:) dy yes)
            go t u
          _ -> throwError e
        )
      | otherwise = do
        dx <- getGlobalDef x
        dy <- getGlobalDef y
        t <- reduce (foldl (:@:) dx xes)
        u <- reduce (foldl (:@:) dy yes)
        go t u
    go t1@(V (Global x) xes) t2 = do
      dx <- getGlobalDef x
      t <- reduce (foldl (:@:) dx xes)
      go t t2
    go t1 t2@(V (Global y) yes) = do
      dy <- getGlobalDef y
      t <- reduce (foldl (:@:) dy yes)
      go t1 t
    go (Lit i) (Lit j) | i == j = return ()
    go (Lam a1 (Scope t)) (Lam a2 (Scope u)) = doAndRestore id (do
      unifyVars (argName a1) (argName a2)
      go t u
      )
    go (_ :@: _) _ = error "aplicacion en reduced"
    go _ (_ :@: _) = error "aplicacion en reduced"
    go (Con c cas) (Con d das)
      | c == d && length cas == length das = zipWithM_ go cas das
    go (Data d1) (Data d2) | d1 == d2 = return ()
    -- falta matchear Elim a ambos lados
    go t1@(Elim (V (Local x) xes) tbs) t2@(Elim (V (Local y) yes) ubs) = do
      x' <- findVar x
      y' <- findVar y
      if x' == y'
        then do
          zipWithM_ go xes yes
          bequal x y tbs ubs
        else do
          dx <- getLocalDef x
          case dx of
            Just t -> do
              t1' <- reduce (Elim (foldl (:@:) t xes) tbs)
              go t1' t2
            Nothing -> do
              dy <- getLocalDef y
              case dy of
                Just t -> do
                  t2' <- reduce (Elim (foldl (:@:) t yes) ubs)
                  go t1 t2'
                Nothing -> throwError (ENeq t1 t2)
    go (Elim _ _) _ = error "elim in reduced"
    go _ (Elim _ _) = error "elim in reduced"
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
        let tx = Con c (map var a1)
            ty = Con c (map var a2)
        equal (substitute x tx r1) (substitute y ty r2))
      >> bequal x y bs b2'

findBranch :: ConHead -> [ElimBranch] -> (ElimBranch, [ElimBranch])
findBranch c [] = error "findBranch"
findBranch c (b : bs)
  | c == elimCon b = (b, bs)
  | otherwise = 
    let (b', bs') = findBranch c bs
    in  (b', b : bs')
