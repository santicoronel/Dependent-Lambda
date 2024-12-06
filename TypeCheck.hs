module TypeCheck where

import Lang
import Error
import MonadTypeCheck
import Context
import Unify
import Equality
import Reduce

import Control.Monad.Except
import Control.Monad.State


-- TODO chequear CUANDO y DONDE se reducen terminos/tipos
--
-- NICETOHAVE uando hago pattern matching, reemplazar
-- las ocurrencias de la variable en los tipos bindeados
-- Ahora mismo podria tomar los argumentos *despues* de hacer pm
--
-- TODO termination checking
-- creo q tiene sentido hacerlo antes (si es solo sintactico)
-- NICETOHAVE permitir recursion mutua (foetus)

-- POST el tipo resultado esta reducido
-- estaria bueno no reducir var globales
infer :: MonadTypeCheck m => Term -> m Type
infer (V v) = case v of
  Local x -> getLocalType x
  Global x -> getGlobalType x
infer (Lam arg st) = do shouldBeType (argType arg)
                        argty <- reduceType (argType arg)
                        bindArg (argName arg) argty
                        ty <- infer (unscope st)
                        unbind (argName arg)
                        return ty
infer (t :@: u) = do  tt <- infer t
                      case unType tt of
                        Pi arg sty -> do
                          check u (argType arg)
                          bindLocal (argName arg) (argType arg) u
                          ty' <- reduceType (unscope sty)
                          unbind (argName arg)
                          return ty'
                        _ -> throwError $ EFun tt
infer (Con ch) = inferCon ch
infer (Data dt) = inferData dt
infer (Elim t bs) = inferElim t bs
infer (Fix f arg ty t) = do
  shouldBeType ty
  ty' <- reduceType ty
  shouldBeType (argType arg)
  argty <- reduceType (argType arg)
  let arg' = arg { argType = argty }
  bindRec f ty' t arg'
  bindArg (argName arg') (argType arg')
  check t ty'
  unbind f
  unbind (argName arg')
  return (Type (Pi arg' (Scope ty')))
infer (Pi arg sty) = do shouldBeType (argType arg)
                        tty <- inferSort (argType arg)
                        bindArg (argName arg) (Type $ Sort tty)
                        rty <- inferSort (unscope sty)
                        unbind (argName arg)
                        return $
                          pisort tty arg rty
infer (Sort (Set i)) = return (set (i + 1))
infer (Ann t tt) = do
  shouldBeType tt
  check t tt
  return tt

inferCon :: MonadTypeCheck m => ConHead -> m Type
inferCon Zero = return natTy
inferCon Suc = return (Type (Pi (Arg natTy "_") (Scope natTy)))
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
  case unType tt of
    Data dt -> inferElim' dt bs
    _ -> throwError (ENotData tt)

inferElim' :: MonadTypeCheck m => DataType -> [ElimBranch] -> m Type
-- NICETOHAVE tratar de inferir ambas branches
inferElim' Nat bs = do
  (zb, sb) <- casesNat bs
  ty <- infer (elimRes zb)
  let [n] = elimConArgs sb
  bindArg n natTy
  check (elimRes sb) ty
  unbind n
  return ty
-- deberia cheqeuar q t y u esten bien formados
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
  case unType tt of
    Sort s -> return s
    _ -> throwError (ENotType t)

check :: MonadTypeCheck m => Term -> Type -> m ()
check (Elim t ts) ty = do
  checkElim t ts ty
check (Con ch) ty = checkCon ch ty
check t ty = do
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
checkElim (V (Local x)) bs ty = do
  tt <- getLocalType x
  case unType tt of
    Data d -> checkElim' x d bs ty
    tt' -> throwError (ENotData tt)
checkElim t bs ty = do
  et <- inferElim t bs
  et `tequal` ty

checkElim' :: MonadTypeCheck m => Name -> DataType -> [ElimBranch] -> Type ->  m ()
-- Nat
checkElim' x Nat bs rty = do
  (zb, sb) <- casesNat bs
  checkElimZero x (elimRes zb)
  let [n] = elimConArgs sb
  checkElimSuc x (elimRes sb) n
  where
    checkElimZero :: MonadTypeCheck m => Name -> Term -> m ()
    checkElimZero x t = do
      bindLocal x natTy zero
      check t rty
      unbind x
    checkElimSuc :: MonadTypeCheck m => Name -> Term -> Name -> m ()
    checkElimSuc x t n = do
      bindArg n natTy
      bindLocal x natTy (suc (var n))
      check t rty
      unbind x
      unbind n
-- Eq
checkElim' _ (Eq t u) bs rty = case bs of
  [] -> notUnifiable t u
  [ElimBranch Refl [] r] -> doAndRestore (do
    tt <- infer t 
    unifyTerms t u
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
    checkElimDataT :: MonadTypeCheck m => Name -> DataDef -> [ElimBranch] -> Type -> m ()
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
    -- TODO chequear q no se repitan nombres en los argumentos
    return (b, bs)
  _ -> do
    (sb, bs') <- sucBranch bs
    return (sb, b : bs')

shouldBeType :: MonadTypeCheck m => Type -> m ()
shouldBeType (Type t) = do
  tt <- infer t
  case unType tt of
    Sort _ -> return ()
    _ -> throwError (ENotType t)

appType :: MonadTypeCheck m => Type -> [Type] -> m Type
appType ty [] = return ty
appType (Type (Pi arg (Scope t))) (ty : tys) = do
  argType arg `tequal` ty
  appType t tys
appType ty _ = throwError (EFun ty)

eqsort :: Sort -> Type
eqsort (Set i) = set i

-- x ahora el argumento no puede aparecer en el sort
pisort :: Sort -> Arg -> Sort -> Type
pisort (Set i) _ (Set j) = set (max i j)