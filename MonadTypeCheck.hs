{-# LANGUAGE FlexibleContexts #-}

module MonadTypeCheck where

import Lang
import Context
import Error
import UnionFind
import Common
import Substitution

import Control.Monad.Except
import Control.Monad.State
import Data.Maybe ( isJust )
import Data.List.Extra ( (!?) )

class (
  Monad m,
  MonadError TypeError m,
  MonadState Context m,
  MonadIO m
  ) => MonadTypeCheck m where


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

addBinder :: MonadState Context m => Int -> Type -> m ()
addBinder x ty = do
  ctx <- get
  let lc = local ctx
      uf = unif ctx
      bx = LBinder x ty
  put (ctx { local = bx : lc, unif = insert uf x })

bindArg :: MonadState Context m => Name -> Type -> m Int
bindArg x ty = do
  i <- newVar x
  addBinder i ty
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
      bdf = LDef fi df True
      bx = LBinder xi (argType arg)
      lc' = bx : bf : lc
      ld' = case dx of
        Nothing -> bdf : ld
        Just d -> LDef xi d False : bdf : ld
  put (ctx { local = lc', localDefs = ld' })
  return (fi, xi)

bindLocal :: MonadState Context m => Name -> Type -> Term -> m Int
bindLocal x ty d = do 
  i <- state (freshVar x)
  ctx <- get
  let lc = local ctx
      lds = localDefs ctx
      lb = LBinder i ty
      ld = LDef i d False
  put (ctx { local = lb : lc, localDefs = ld : lds })
  return i

bindPattern :: MonadState Context m => Int -> Term -> m ()
bindPattern x p = do
  ctx <- get
  let lds = localDefs ctx
  put ctx { localDefs = LDef x p False : lds}

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

addDataDef :: MonadTypeCheck m => DataDef -> m ()
addDataDef d = do
  ctx <- get
  put ctx { datadefs = d : datadefs ctx }

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

isRec :: MonadTypeCheck m => Int -> m Bool
isRec i = do
  ctx <- get
  case lookupWith i (localDefs ctx) defVar localRec of
    Just t -> return t
    Nothing -> error "isRec: variable no definida"