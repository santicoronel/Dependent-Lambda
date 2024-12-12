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

duplicateName :: Eq a => [a] -> Bool
duplicateName xs = not $ all unary $ group xs
  where unary [_] = True
        unary _ = False

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
elab (SLam arg t) = do
  ty <- elabType (argType arg)
  ctx <- get
  put (ctx { local = argName arg : local ctx })
  t' <- elab t
  put ctx
  return (Lam arg { argType = ty } t')
elab (SApp t u) = (:@:) <$> elab t <*> elab u
elab (SElim t bs) = do
  t' <- elab t
  bs' <- elabBranches bs
  return (Elim t' bs')
elab (SFix f arg ty t) = do
  argty <- elabType (argType arg)
  let arg' = arg { argType = argty }
  ty' <- elabFixType arg' ty
  t' <- elabFix f arg'
  return (Fix f arg' ty' t')

  where
    elabFixType arg ty = do
      ctx <- get
      put (ctx { local = argName arg : local ctx })
      ty' <- elabType ty
      put ctx
      return ty'
    elabFix f arg = do
      ctx <- get
      put (ctx { local = argName arg : f : local ctx })
      t' <- elab t
      put ctx
      return t'
elab (SPi arg ty) = do
  argty <- elabType (argType arg)
  let arg' = arg { argType = argty }
  ctx <- get
  put (ctx { local = argName arg' : local ctx })
  ty' <- elabType ty
  put ctx
  return (Pi arg' ty')
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
    (throwError (ElabError "yadayada"))
  mapM elabBranch bs

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