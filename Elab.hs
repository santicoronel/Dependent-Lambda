{-# LANGUAGE FlexibleContexts #-}

module Elab where

import Lang

import Control.Monad.State
import Control.Monad.Except
import Data.List ( elemIndex, group )

data ElabError = ElabError String

data ElabContext = ElabContext {
    local :: [Name],
    global :: [Name],
    datatypes :: [Name],
    cons :: [Constructor]
}

emptyElabContext :: ElabContext
emptyElabContext = ElabContext [] [] [] []

class (MonadError ElabError m, MonadState ElabContext m) =>
  MonadElab m

-- TODO hacer una sola jijis
lookupWith :: Eq i => i -> [a] -> (a -> i) -> (a -> b) -> Maybe b
lookupWith _ [] _ _ = Nothing
lookupWith x (b : bs) gn gt
  | x == gn b = Just (gt b)
  | otherwise = lookupWith x bs gn gt

elabProgram :: MonadElab m => SProgram -> m Program
elabProgram = mapM go
  where
    go sd = do
      modify (\ctx -> ctx { local = [] })
      elabDecl sd

elabDecl :: MonadElab m => SDecl -> m Decl
elabDecl (SDecl n args ty t) = do
  ctx <- get
  when (n `elem` global ctx) 
    (throwError $ ElabError $ "variable global " ++ n ++ " ya existe")
  let t' = foldr  SLam (SAnn t ty) args
  rt <- elab t'
  put ctx { global = n : global ctx }
  return (Decl n rt)

elab :: MonadElab m => STerm -> m Term
elab (Lit n)
  | n >= 0 = return (iterate suc zero !! n)
  | otherwise = error "elab: negative integer"
elab SZero = return zero
elab SSuc = return (Lam (Arg "n" natTy) (suc (bound 0)))
elab SNat = return (Data Nat)
elab SRefl = return refl
elab (SEq t u) = do
  t' <- elab t
  u' <- elab u
  return (Data $ Eq t' u')
elab (SV x) = do
  mv <- gets variable
  case mv of
    Nothing -> throwError (ElabError $ "var " ++ x ++ " not defined")
    Just v -> return v 
  where
    variable (ElabContext lc gc dt cs)
      | x `elem` lc = let Just i = elemIndex x lc in return (bound i)
      | x `elem` gc = return (V (Global x))
      | x `elem` dt = return (Data (DataT x))
      | x `elem` map conName cs =
        let Just c = lookupWith x cs conName id
        in  return (Con (DataCon c))
      | otherwise = Nothing
elab (SLam arg t) = go arg t
  where
    go (Arg [] _) t = elab t
    go (Arg (x:xs) ty) t = do
      ctx <- get
      put ctx { local = x : local ctx}
      t' <- go (Arg xs ty) t
      put ctx
      ty' <- elabType ty
      return (Lam (Arg x ty') t')

elab (SApp t u) = (:@:) <$> elab t <*> elab u
elab (SElim t bs) = do
  t' <- elab t
  bs' <- elabBranches bs
  return (Elim t' bs')
elab (SFix f arg ty t) = do
  case argName arg of
    [] -> error "elab: sin argumento"
    (a:as) -> do
      ty' <- elabFixType a as (argType arg) ty
      t' <- elabFix f a as (argType arg)
      argty <- elabType (argType arg)
      return (Fix f (Arg a argty) ty' t')

  where
    elabFixType a as aty ty = do
      ctx <- get
      put (ctx { local = a : local ctx })
      ty' <- elab (SPi (Arg as aty) ty)
      put ctx
      return (Type ty')
    elabFix f a as aty = do
      ctx <- get
      put (ctx { local = a : f : local ctx })
      t' <- elab (SLam (Arg as aty) t)
      put ctx
      return t'
elab (SPi arg ty) = go arg ty
  where
    go (Arg [] _) ty = unType <$> elabType ty
    go (Arg (x:xs) aty) ty = do
      ctx <- get
      put ctx { local = x : local ctx}
      ty' <- go (Arg xs aty) ty
      put ctx
      aty' <- elabType aty
      return (Pi (Arg x aty') (Type ty'))
elab (SSort s) = return (Sort s)
elab (SAnn t ty) = Ann <$> elab t <*> elabType ty

elabType :: MonadElab m => SType -> m Type
elabType (Type ty) = Type <$> elab ty


-- TODO pensar si quiero chequear mas cosas aca
--
-- podria chequear q sean constructores del mismo datatype
-- agregando nombre del dt al ElabContexto de constructores
elabBranches :: MonadElab m => [SElimBranch] -> m [ElimBranch]
elabBranches bs = do
  when (duplicateName (map elimCon bs))
    (throwError (ElabError "branches redundantes"))
  mapM_ checkArgNames bs
  mapM elabBranch bs

checkArgNames :: MonadElab m => SElimBranch -> m ()
checkArgNames (ElimBranch _ as _ ) =
  when (duplicateName as) (throwError (ElabError "nombre duplicado en case"))

elabBranch :: MonadElab m => SElimBranch -> m ElimBranch
elabBranch (ElimBranch "zero" as t) = case as of
  [] -> ElimBranch Zero [] <$> elab t
  _ -> throwError (ElabError "too many cases for zero")
elabBranch (ElimBranch "suc" as t) = case as of
  [] -> throwError (ElabError "not enough cases for suc")
  [n] -> do
    ctx <- get
    put ctx { local = n : local ctx }
    t' <- elab t
    put ctx
    return (ElimBranch Suc [n] t')
  _ -> throwError (ElabError "too many cases for suc") 
elabBranch (ElimBranch "refl" as t) = case as of
  [] -> ElimBranch Refl [] <$> elab t
  _ -> throwError (ElabError "too many cases for refl")
elabBranch (ElimBranch nc as t) = do
  ctx <- get
  case lookupWith nc (cons ctx) conName id of
    Nothing ->
      throwError (ElabError $ "constructor nc " ++ nc ++ " not defined")
    Just c -> do
      unless (length as == conArity c) $
        throwError (ElabError $ "too many cases for " ++ nc)
      put ctx { local = reverse as ++ local ctx }
      t' <- elab t
      put ctx
      return (ElimBranch (DataCon c) as t')