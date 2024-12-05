{-# LANGUAGE FlexibleContexts #-}

module MonadTypeCheck where

import Lang
import Context
import Error
import UnionFind


import Control.Monad.Except
import Control.Monad.State
import Data.Maybe ( isJust )

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

lookupWith :: Name -> [a] -> (a -> Name) -> (a -> b) -> Maybe b
lookupWith _ [] _ _ = Nothing
lookupWith x (b : bs) gn gt
  | x == gn b = Just (gt b)
  | otherwise = lookupWith x bs gn gt

getLocalType :: MonadTypeCheck m => Name -> m Type
getLocalType x = do ctx <- gets local
                    case lookupWith x ctx localName localType of
                      Just t -> return t
                      Nothing -> throwError $ EVar x

getGlobalType :: MonadTypeCheck m => Name -> m Type
getGlobalType x = do  ctx <- gets global
                      case lookupWith x ctx globalName globalType of
                        Just t -> return t
                        Nothing -> throwError $ EVar x

getLocalDef :: MonadTypeCheck m => Name -> m (Maybe Term)
getLocalDef x = do
  ctx <- gets local
  case lookupWith x ctx localName localDef of
    Just t -> return t
    Nothing -> throwError $ EVar x

getGlobalDef :: MonadTypeCheck m => Name -> m Term
getGlobalDef x = do
  ctx <- gets global
  case lookupWith x ctx globalName globalDef of
    Just t -> return t
    Nothing -> throwError $ EVar x 

bindArg :: MonadState Context m => Name -> Type -> m ()
bindArg x ty = do
  ctx <- get
  let lc = local ctx
      bx = LBinder x ty Nothing Nothing
  put (ctx { local = bx : lc})

bindRec :: MonadState Context m => Name -> Type -> Term -> Arg -> m ()
bindRec f ty df arg = do
  ctx <- get
  let lc = local ctx
      fty = Type (Pi arg (Scope ty))
      bf = LBinder f fty (Just df) (Just (argName arg))
      bx = LBinder (argName arg) (argType arg) Nothing Nothing
  put (ctx { local =  bx : bf : lc})

bindLocal :: MonadState Context m => Name -> Type -> Term -> m ()
bindLocal x ty d = do ctx <- get
                      let bc = local ctx
                          b = LBinder x ty ( Just d) Nothing
                      put (ctx { local = b : bc })

updateWith :: (a -> Name) -> (a -> a) -> Name -> [a] -> Maybe [a]
updateWith _ _ _ [] = Nothing
updateWith gn up x (y:ys)
  | gn y == x = Just (up y : ys)
  | otherwise = (y :) <$> updateWith gn up x ys

bindPattern :: MonadState Context m => Name -> Term -> m ()
bindPattern x p = do
  ctx <- get
  let l = updateWith localName (\lb -> lb { localDef = Just p }) x (local ctx)
  case l of
    Nothing -> error "bindPattern" 
    Just lc -> put (ctx { local = lc })

unbindPattern :: MonadState Context m => Name -> m ()
unbindPattern x = do
  ctx <- get
  let l = updateWith localName (\lb -> lb { localDef = Nothing }) x (local ctx)
  case l of
    Nothing -> error "unbindPatter"
    Just lc -> put (ctx { local = lc })

getDataDef :: MonadTypeCheck m => Name -> m DataDef
getDataDef d = do
  dds <- gets datadefs
  case lookupWith d dds dataName id of
    Just dd -> return dd
    Nothing -> throwError (EDataNoDef d)

deleteWith :: Name -> [a] -> (a -> Name) -> Maybe [a]
deleteWith _ [] gn = Nothing
deleteWith x (b : bs) gn
  | x == gn b = Just bs
  | otherwise = (b :) <$> deleteWith x bs gn

unbind :: MonadTypeCheck m => Name -> m ()
unbind x = do ctx <- get
              case deleteWith x (local ctx) localName of
                Just lc -> put ctx { local = lc }
                Nothing -> error ("unbind " ++ x)

isRec :: MonadState Context m => Name -> m Bool
isRec x = do
  ctx <- get
  case lookupWith x (local ctx) localName recArg of
    Nothing -> error "isRec"
    Just r -> return (isJust r)

unifyVars :: MonadTypeCheck m => Name -> Name -> m ()
unifyVars x y = do
  ctx <- get
  case union (unif ctx) x y of
    Nothing -> error $ "union: " ++ x ++ y ++ "??"
    Just uf -> put (ctx { unif = uf })

findVar :: MonadTypeCheck m => Name -> m Name
findVar x = do
  ctx <- get
  case find (unif ctx) x of
    Nothing -> error $ "find " ++ x ++ "??"
    Just x' -> return x'

retry :: MonadError e m => m a -> m a -> m a
retry a b = a `catchError` const b

retryWithError :: MonadError e m => m a -> m a -> e -> m a
retryWithError a b e = retry a b `catchError` const (throwError e)