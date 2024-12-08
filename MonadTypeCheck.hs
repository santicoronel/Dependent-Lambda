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

getLocalType :: MonadTypeCheck m => Int -> m Type
getLocalType i = do ctx <- get
                    case lookupWith i (local ctx) localVar localType of
                      Just ty -> return ty
                      Nothing -> throwError $ EFree i

getGlobalType :: MonadTypeCheck m => Name -> m Type
getGlobalType x = do  ctx <- gets global
                      case lookupWith x ctx globalName globalType of
                        Just t -> return t
                        Nothing -> throwError $ EGlobal x

getLocalDef :: MonadTypeCheck m => Int -> m (Maybe Term)
getLocalDef i = do
  ctx <- get
  case lookupWith i (local ctx) localVar localDef of
    Just d -> return d
    Nothing -> throwError $ EFree i

getGlobalDef :: MonadTypeCheck m => Name -> m Term
getGlobalDef x = do
  ctx <- gets global
  case lookupWith x ctx globalName globalDef of
    Just t -> return t
    Nothing -> throwError $ EGlobal x 

bindArg :: MonadState Context m => Name -> Type -> m Int
bindArg x ty = do
  i <- state (freshVar x)
  ctx <- get
  let lc = local ctx
      uf = unif ctx
      bx = LBinder i ty Nothing
  put (ctx { local = bx : lc, unif = insert uf i })
  return i

bindFun :: MonadState Context m => Name -> Type -> Term -> Arg -> Maybe Term -> m (Int, Int)
bindFun f ty df arg dx = do
  fi <- state (freshVar f)
  xi <- state (freshVar (argName arg))
  ctx <- get
  let lc = local ctx
      fty = Type (Pi arg ty)
      bf = LBinder fi fty (Just df)
      bx = LBinder xi (argType arg) dx
  put (ctx { local =  bx : bf : lc })
  return (fi, xi)

bindLocal :: MonadState Context m => Name -> Type -> Term -> m Int
bindLocal x ty d = do 
  i <- state (freshVar x)
  ctx <- get
  let bc = local ctx
      b = LBinder i ty (Just d)
  put (ctx { local = b : bc })
  return i

updateWith :: Eq i => (a -> i) -> (a -> a) -> i -> [a] -> Maybe [a]
updateWith _ _ _ [] = Nothing
updateWith gn up x (y:ys)
  | gn y == x = Just (up y : ys)
  | otherwise = (y :) <$> updateWith gn up x ys

bindPattern :: MonadState Context m => Int -> Term -> m ()
bindPattern x p = do
  ctx <- get
  let l = updateWith localVar (\lb -> lb { localDef = Just p }) x (local ctx)
  case l of
    Nothing -> error "bindPattern" 
    Just lc -> put (ctx { local = lc })

unbindPattern :: MonadState Context m => Int -> m ()
unbindPattern x = do
  ctx <- get
  let l = updateWith localVar (\lb -> lb { localDef = Nothing }) x (local ctx)
  case l of
    Nothing -> error "unbindPatter"
    Just lc -> put (ctx { local = lc })

getDataDef :: MonadTypeCheck m => Name -> m DataDef
getDataDef d = do
  dds <- gets datadefs
  case lookupWith d dds dataName id of
    Just dd -> return dd
    Nothing -> throwError (EDataNoDef d)

deleteWith :: Eq i => (a -> i) -> i -> [a] -> Maybe [a]
deleteWith gn _ [] = Nothing
deleteWith gn x (b : bs)
  | x == gn b = Just bs
  | otherwise = (b :) <$> deleteWith gn x bs

unbind :: MonadTypeCheck m => Int -> m ()
unbind x = do ctx <- get
              case deleteWith localVar x (local ctx) of
                Just lc -> put ctx { local = lc }
                Nothing -> error ("unbind " ++ show x)

unifyVars :: MonadTypeCheck m => Int -> Int -> m ()
unifyVars x y = do
  ctx <- get
  case union (unif ctx) x y of
    Nothing -> error $ "union: " ++ show x ++ show y ++ "??"
    Just uf -> put (ctx { unif = uf })

varEq :: MonadTypeCheck m => Int -> Int -> m Bool
varEq x y = do
  ctx <- get
  case equivalent (unif ctx) x y of
    Nothing -> error $ "unionfind.equivalent " ++ show x ++ " " ++ show y
    Just (uf, res) -> do
      put ctx { unif = uf }
      return res

retry :: MonadError e m => m a -> m a -> m a
retry a b = a `catchError` const b

retryWithError :: MonadError e m => m a -> m a -> e -> m a
retryWithError a b e = retry a b `catchError` const (throwError e)