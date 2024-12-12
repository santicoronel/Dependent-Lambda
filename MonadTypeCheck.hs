{-# LANGUAGE FlexibleContexts #-}

module MonadTypeCheck where

import Lang
import Context
import Error
import UnionFind


import Control.Monad.Except
import Control.Monad.State
import Data.Maybe ( isJust )
import Data.List.Extra ( (!?) )

class (
  Monad m,
  MonadError TypeError m,
  MonadState Context m
  ) => MonadTypeCheck m where


-- TODO meter en otro modulo

doAndRestore :: MonadState s m => m a -> m a
doAndRestore m = do
  s <- get
  x <- m
  put s
  return x

lookupWith :: Eq i => i -> [a] -> (a -> i) -> (a -> b) -> Maybe b
lookupWith _ [] _ _ = Nothing
lookupWith x (b : bs) gn gt
  | x == gn b = Just (gt b)
  | otherwise = lookupWith x bs gn gt

updateWith :: Eq i => (a -> i) -> (a -> a) -> i -> [a] -> Maybe [a]
updateWith _ _ _ [] = Nothing
updateWith gn up x (y:ys)
  | gn y == x = Just (up y : ys)
  | otherwise = (y :) <$> updateWith gn up x ys

deleteWith :: Eq i => (a -> i) -> i -> [a] -> Maybe [a]
deleteWith gn _ [] = Nothing
deleteWith gn x (b : bs)
  | x == gn b = Just bs
  | otherwise = (b :) <$> deleteWith gn x bs

retry :: MonadError e m => m a -> m a -> m a
retry a b = a `catchError` const b

retryWithError :: MonadError e m => m a -> m a -> e -> m a
retryWithError a b e = retry a b `catchError` const (throwError e)

------------------------------------------------------------------------

newVar :: MonadState Context m => Name -> m Int
newVar = state . freshVar

getLocalType :: MonadTypeCheck m => Int -> m Type
getLocalType i = do ctx <- get
                    case lookupWith i (local ctx) localVar localType of
                      Just ty -> return ty
                      Nothing -> error "free var not in type context"

getGlobalType :: MonadTypeCheck m => Name -> m Type
getGlobalType x = do  ctx <- gets global
                      case lookupWith x ctx globalName globalType of
                        Just t -> return t
                        Nothing -> throwError $ EGlobal x

getLocalDef :: MonadTypeCheck m => Int -> m (Maybe Term)
getLocalDef i = do
  ctx <- get
  return $ lookupWith i (localDefs ctx) defVar localDef

getGlobalDef :: MonadTypeCheck m => Name -> m Term
getGlobalDef x = do
  ctx <- gets global
  case lookupWith x ctx globalName globalDef of
    Just t -> return t
    Nothing -> throwError $ EGlobal x 

bindGlobal :: MonadTypeCheck m => Decl -> Type -> m ()
-- bindGlobal (Decl n ty t) = do
bindGlobal (Decl n t) ty = do
  ctx <- get
  when (n `elem` map globalName (global ctx))
    (throwError $ EGlobalEx n)
  -- let gb = GBinder n ty t
  let gb = GBinder n ty t
  put (ctx { global = gb : global ctx })

bindArg :: MonadState Context m => Name -> Type -> m Int
bindArg x ty = do
  i <- newVar x
  ctx <- get
  let lc = local ctx
      uf = unif ctx
      bx = LBinder i ty
  put (ctx { local = bx : lc, unif = insert uf i })
  return i

-- TODO esto es horrible
-- mejor algo como bindFun / bindCall
bindFun :: MonadState Context m => Name -> Type -> Term -> Arg -> Maybe Term -> m (Int, Int)
bindFun f ty df arg dx = do
  fi <- newVar f
  xi <- newVar (argName arg)
  ctx <- get
  let lc = local ctx
      ld = localDefs ctx
      fty = Type (Pi arg ty)
      bf = LBinder fi fty
      bdf = LDef fi df
      bx = LBinder xi (argType arg)
      lc' = bx : bf : lc
      ld' = case dx of
        Nothing -> bdf : ld
        Just d -> LDef xi d : bdf : ld
  put (ctx { local = lc', localDefs = ld' })
  return (fi, xi)

bindLocal :: MonadState Context m => Name -> Type -> Term -> m Int
bindLocal x ty d = do 
  i <- state (freshVar x)
  ctx <- get
  let lc = local ctx
      lds = localDefs ctx
      lb = LBinder i ty
      ld = LDef i d
  put (ctx { local = lb : lc, localDefs = ld : lds })
  return i

bindPattern :: MonadState Context m => Int -> Term -> m ()
bindPattern x p = do
  ctx <- get
  let lds = localDefs ctx
  put ctx { localDefs = LDef x p : lds}

unbindPattern :: MonadState Context m => Int -> m ()
unbindPattern x = do
  ctx <- get
  let ml = deleteWith defVar x (localDefs ctx)
  case ml of
    Nothing -> error "unbindPatter"
    Just lc -> put (ctx { localDefs = lc })

getDataDef :: MonadTypeCheck m => Name -> m DataDef
getDataDef d = do
  dds <- gets datadefs
  case lookupWith d dds dataName id of
    Just dd -> return dd
    Nothing -> throwError (EDataNoDef d)

unifyVars :: MonadTypeCheck m => Int -> Int -> m ()
unifyVars x y = do
  ctx <- get
  let uf = union (unif ctx) x y
  put ctx { unif = uf }

varEq :: MonadTypeCheck m => Int -> Int -> m Bool
varEq x y = do
  ctx <- get
  case equivalent (unif ctx) x y of
    Nothing -> error $ "unionfind.equivalent " ++ show x ++ " " ++ show y
    Just (uf, res) -> do
      put ctx { unif = uf }
      return res