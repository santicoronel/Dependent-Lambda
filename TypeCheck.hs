module TypeCheck where

import Lang
import Error
import MonadTypeCheck
import Context
import Unify
import Equality
import Reduce
import Substitution

import Control.Monad.Except
import Control.Monad.State

infer :: MonadTypeCheck m => Term -> m Type
infer (V v) = case v of
  Bound x -> error "typecheck: bound"
  Free x -> getLocalType x
  Global x -> getGlobalType x
infer (Lam arg t) = doAndRestore (do
  shouldBeType (argType arg)
  i <- bindArg (argName arg) (argType arg)
  infer (open i t)
  )
infer (t :@: u) = do  tt <- infer t
                      tt' <- reduceType tt
                      case unType tt' of
                        Pi arg ty -> do
                          check u (argType arg)
                          i <- bindLocal (argName arg) (argType arg) u
                          reduceType (openType i ty)
                        _ -> throwError $ EFun tt'
infer (Con ch) = inferCon ch
infer (Data dt) = inferData dt
infer (Elim t bs) = inferElim t bs
-- todo factorizar esto dios
infer t@(Fix f arg ty u) = doAndRestore (do
  shouldBeType (argType arg)
  --
  xi <- bindArg (argName arg) (argType arg)
  let ty' = openType xi ty
  --
  shouldBeType ty'
  rty <- reduceType ty'
  let rty' = closeType xi rty
  --
  fi <- bindLocal f (Type $ Pi arg rty') u
  check (open2 fi xi t) rty'
  return (Type (Pi arg rty'))
  )
infer (Pi arg ty) = doAndRestore (do
  tty <- inferSort (argType arg)
  i <- bindArg (argName arg) (Type $ Sort tty)
  sty <- inferSort (openType i ty)
  let sty' = closeSort i sty
  return (pisort tty arg sty')
  )
infer (Sort (Set i)) = return (set (i + 1))
infer (Ann t tt) = do
  shouldBeType tt
  check t tt
  return tt

inferCon :: MonadTypeCheck m => ConHead -> m Type
inferCon Zero = return natTy
inferCon Suc = return (Type (Pi (Arg natTy "_") natTy))
inferCon Refl = throwError (EIncomplete (Con Refl))
inferCon (DataCon c) = return (conType c)

inferData :: MonadTypeCheck m => DataType -> m Type
inferData Nat = return (set 0)
inferData (Eq t u) = do
  ty <- retryWithError
          (inferAndCheck t u)
          (inferAndCheck u t)
          (EEq t u)
  sty <- inferSort ty
  return (eqsort sty)
  where inferAndCheck t1 t2 = do
          ty <- infer t1
          check t2 ty
          return ty
inferData (DataT dn) = do
  dd <- getDataDef dn
  return (dataType dd)

inferElim :: MonadTypeCheck m => Term -> [ElimBranch] -> m Type
inferElim t bs = do
  tt <- infer t
  tt' <- reduceType tt
  case unType tt' of
    Data dt -> inferElim' dt bs
    _ -> throwError (ENotData tt')

inferElim' :: MonadTypeCheck m => DataType -> [ElimBranch] -> m Type
-- NICETOHAVE tratar de inferir ambas branches
inferElim' Nat bs = doAndRestore (do
  (zb, sb) <- casesNat bs
  ty <- infer (elimRes zb)
  let [n] = elimConArgs sb
  i <- bindArg n natTy
  let sr = open i (elimRes sb)
  check sr ty
  return ty
  )
inferElim' (Eq t u) bs = case bs of
  [] -> throwError EIncompleteBot
  [ElimBranch Refl [] r] -> doAndRestore (do
    unifyTerms t u
    infer r)
  [ElimBranch Refl _ _] -> throwError (ENumberOfArgs Refl)
  _ -> throwError EManyCases
inferElim' (DataT d) bs = do
  dd <- getDataDef d
  inferElimDataT dd bs
  where
    -- TODO
    inferElimDataT :: MonadTypeCheck m => DataDef -> [ElimBranch] -> m Type
    inferElimDataT = undefined


inferSort :: MonadTypeCheck m => Type -> m Sort
inferSort (Type t) = do
  tt <- infer t
  tt' <- reduceType tt
  case unType tt' of
    Sort s -> return s
    _ -> throwError (ENotType t)

check :: MonadTypeCheck m => Term -> Type -> m ()
check (Elim t ts) ty = do
  shouldBeType ty
  checkElim t ts ty
check (Con ch) ty = do
  shouldBeType ty
  checkCon ch ty
check t ty = do
  shouldBeType ty
  tt <- infer t
  ty `tequal` tt

checkCon :: MonadTypeCheck m => ConHead -> Type -> m ()
checkCon Refl ty = do
  ty' <- reduceType ty
  case unType ty' of
    (Data (Eq t u)) -> t `equal` u
    _ -> throwError (ECheckEq ty)
checkCon c ty = do
  tt <- infer (Con c)
  ty `tequal` tt

-- NICETOHAVE manejar otro caso ademas de variables
checkElim :: MonadTypeCheck m => Term -> [ElimBranch] -> Type -> m ()
checkElim (V (Free x)) bs ty = do
  tt <- getLocalType x
  tt' <- reduceType tt
  case unType tt' of
    Data d -> checkElim' x d bs ty
    _ -> throwError (ENotData tt')
checkElim t bs ty = do
  et <- inferElim t bs
  et `tequal` ty

checkElim' :: MonadTypeCheck m => Int -> DataType -> [ElimBranch] -> Type ->  m ()
-- Nat
checkElim' x Nat bs rty = do
  (zb, sb) <- casesNat bs
  checkElimZero x (elimRes zb)
  let [n] = elimConArgs sb
  checkElimSuc x (elimRes sb) n
  where
    checkElimZero :: MonadTypeCheck m => Int -> Term -> m ()
    checkElimZero x t = do
      bindPattern x zero
      check t rty
      unbindPattern x
    checkElimSuc :: MonadTypeCheck m => Int -> Term -> Name -> m ()
    checkElimSuc x t n = doAndRestore (do
      i <- bindArg n natTy
      bindPattern x (suc (var i))
      check t (openType i rty)
      )
-- Eq
checkElim' x (Eq t u) bs rty = case bs of
  [] -> notUnifiable t u
  [ElimBranch Refl [] r] -> doAndRestore (do
    unifyTerms t u
    bindPattern x (Con Refl)
    ty <- infer r
    ty `tequal` rty)
  [ElimBranch Refl _ _] -> throwError (ENumberOfArgs Refl)
  _ -> throwError EManyCases
-- DataT
checkElim' x (DataT d) bs rty = do
  dd <- getDataDef d
  checkElimDataT x dd bs rty
  where
    -- TODO
    checkElimDataT :: MonadTypeCheck m => Int -> DataDef -> [ElimBranch] -> Type -> m ()
    checkElimDataT = undefined

casesNat :: MonadTypeCheck m => [ElimBranch] -> m (ElimBranch, ElimBranch)
casesNat bs = do
  (zb, bs') <- zeroBranch bs
  (sb, bs'') <- sucBranch bs'
  unless (null bs'') (throwError EManyCases)
  return (zb, sb)

zeroBranch :: MonadTypeCheck m => [ElimBranch] -> m (ElimBranch, [ElimBranch])
zeroBranch [] = throwError ECasesMissing
zeroBranch (b:bs) = case elimCon b of
  Zero -> do
    unless (null $ elimConArgs b) (throwError (ENumberOfArgs Zero))
    return (b, bs)
  _ -> do
    (zb, bs') <- zeroBranch bs
    return (zb, b : bs')

sucBranch :: MonadTypeCheck m => [ElimBranch] -> m (ElimBranch, [ElimBranch])
sucBranch [] = throwError ECasesMissing
sucBranch (b:bs) = case elimCon b of
  Suc -> do
    unless (length (elimConArgs b) == 1) (throwError (ENumberOfArgs Suc))
    return (b, bs)
  _ -> do
    (sb, bs') <- sucBranch bs
    return (sb, b : bs')

shouldBeType :: MonadTypeCheck m => Type -> m ()
shouldBeType ty = void (inferSort ty)

eqsort :: Sort -> Type
eqsort (Set i) = set i

-- x ahora el argumento no puede aparecer en el sort
pisort :: Sort -> Arg -> Sort -> Type
pisort (Set i) _ (Set j) = set (max i j)