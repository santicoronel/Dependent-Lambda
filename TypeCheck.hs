{-# LANGUAGE FlexibleContexts #-}
module TypeCheck where

import Lang

import Control.Monad.Except
import Control.Monad.State

data TypeError =
  EVar Name
  | EFun Type
  | EIncomplete Term
  | EEq Term Term

data TBinding = TBound { getTBound :: Type }

type UnionFind x = ()

data TypeBinder = TyBinder {
  binderName :: Name,
  binderType :: Type,
  binderDef :: Maybe Term}

-- solo tipos reducidos
data Context = TC {
  local :: [TypeBinder],
  unif :: UnionFind Name }

class (
  Monad m,
  MonadError TypeError m,
  MonadState Context m
  ) => MonadTypeCheck m where

doAndRestore :: MonadState s m => (s -> s) -> m a -> m a
doAndRestore mod m = do
  s <- get
  put (mod s)
  x <- m
  put s
  return x 

lookupType :: Name -> [TypeBinder] -> Maybe Type
lookupType x [] = Nothing
lookupType x (TyBinder y ty _ : xs)
  | x == y = Just ty
  | otherwise = lookupType x xs

boundType :: MonadTypeCheck m => Name -> m Type
boundType x = do  ctx <- gets local
                  case lookupType x ctx of
                    Just t -> return t
                    Nothing -> throwError $ EVar x

bindType :: MonadState Context m => Name -> Type -> m ()
bindType x ty = do  ctx <- get
                    let bc = local ctx                    
                    put (ctx { local = TyBinder x ty Nothing : bc } )

bindDef :: MonadState Context m => Name -> Type -> Term -> m ()
bindDef x ty t = do ctx <- get
                    let bc = local ctx
                    put (ctx { local = TyBinder x ty (Just t) : bc })

delete :: Name -> [TypeBinder] -> Maybe [TypeBinder]
delete _ [] = Nothing
delete x (TyBinder y ty md:ys)
  | x == y = Just ys
  | otherwise = (TyBinder y ty md :) <$> delete x ys

unbindType :: MonadTypeCheck m => Name -> m ()
unbindType x = do ctx <- get
                  case delete x (local ctx) of
                    Just tc -> put ctx { local = tc }
                    Nothing -> error ("unbindtype " ++ x)

retry :: MonadError e m => m a -> m a -> m a
retry a b = a `catchError` const b

retryWithError :: MonadError e m => m a -> m a -> e -> m a
retryWithError a b e = retry a b `catchError` const (throwError e)

-- TODO vamo a tener q hacer unificacion
-- tener datatypes implica introducir axiomas de
-- desigualdad entre constructores
-- y de inyectividad (¿¿alguno mas??)
-- me parece un poco engorroso, mejor unificar
infer :: MonadTypeCheck m => Term -> m Type
infer (V v) = case v of
  Bound x -> boundType x
  Global x -> boundType x -- aca puede q quiera boundGlobal
infer (Lit i) | i >= 0 = return (Type (Data Nat))
infer (Lam arg st) = do checkType (argType arg)
                        bindType (argName arg) (argType arg)
                        ty <- infer (unscope st)
                        unbindType (argName arg)
                        return ty
infer (t :@: u) = do  tt <- infer t
                      case unType tt of
                        Pi arg sty -> do
                          check u (argType arg)
                          bindDef (argName arg) (argType arg) u
                          ty' <- reduceType (unscope sty)
                          unbindType (argName arg)
                          return (Type ty')
                        _ -> throwError $ EFun tt
infer (Con ch) = inferCon ch
infer (Data dt) = inferData dt
infer t@(Elim _ _) = throwError (EIncomplete t)
infer (Pi (Arg ty x) sty) = do  checkType ty
                                tty <- inferSort ty -- inferSort reduce?
                                bindType x tty
                                Type rty <- inferSort (unscope sty)
                                unbindType x
                                let sarg = Arg tty x
                                return $
                                  pisort tty (Lam sarg (Scope rty))
infer (Sort (Set i)) = return (set (i + 1))
infer (Ann t tt) = do
  checkType tt
  check t tt
  return tt

inferCon :: MonadTypeCheck m => ConHead -> m Type
inferCon Zero = return natTy
inferCon Suc = return (Type (Pi (Arg natTy "_") (Scope natTy)))
inferCon Refl = throwError (EIncomplete (Con Refl))

inferData :: MonadTypeCheck m => DataType -> m Type
infer (Eq t u) = do ty <- retryWithError 
                            (inferApp t u)
                            (inferApp u t)
                            (EEq t u)
                    return (eqsort (inferSort ty))
  where inferApp t1 t2 = do
          ty <- infer t1
          check t2 ty
          return ty

-- reducir tipo antes o despues? ahora lo hacemos aca
check :: MonadTypeCheck m => Term -> Type -> m ()
-- voy a querer determinar relacion de orden estructural
-- pensar ejemplo mod2: 
--  l = suc m => m < l
--  m = suc n => n < m
--  plt n < l
{-check (Elim t [zt, st]) ty = do
  -- caso 0
  check zt ty
  -- caso inductivo { (suc n) [rec(n)] -> ... }
  bindType (Type Nat)
  bindType rty
  check st rty
  unbindType
  unbindType -}
check t ty = do
  ty' <- reduce ty
  check' t ty'
  where 
    check' (Elim t ts) ty =do
      tt <- infer t
      checkElim tt ts ty
    check' (Con Refl) (Eq t u) = t `equal` u
    check' t ty = do
      tt <- infer t
      unType ty `tequal` unType tt