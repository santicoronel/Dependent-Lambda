{-# LANGUAGE FlexibleContexts #-}

module Elab where


import Lang
import Common
import Datatype

import Control.Monad.State
import Control.Monad.Except
import Data.List ( elemIndex, group )

data ElabError = ElabError String | DataError String

-- NICETOHAVE mejores mensajes de error

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

globalNames :: MonadState ElabContext m => m [Name]
globalNames = do
  ctx <- get
  return (global ctx ++ datatypes ctx ++ map conName (cons ctx))

elabProgram :: MonadElab m => SProgram -> m Program
elabProgram = mapM go
  where
    go (PDecl d) = do
      modify (\ctx -> ctx { local = [] })
      PDecl <$> elabDecl d
    go (PData sdt) = do
      modify (\ctx -> ctx { local = [] })
      dt <- elabData sdt
      case checkData dt of
        Left (DError e) -> throwError (DataError e)
        Right dt' -> do
          modify (\ctx -> ctx { cons = dataCons dt' ++ cons ctx })
          return (PData dt')

elabDecl :: MonadElab m => SDecl -> m Decl
elabDecl (SDecl n args ty t) = do
  gnames <- globalNames
  when (n `elem` gnames) 
    (throwError $ ElabError $ "nombre " ++ n ++ " repetido")
  let t' = foldr  SLam (SAnn t ty) args
  rt <- elab t'
  ctx <- get
  put ctx { global = n : global ctx }
  return (Decl n rt)

elabData :: MonadElab m => SDataDecl -> m DataDecl
elabData (DataDecl n sty scons) = do
  gnames <- globalNames
  when (n `elem` gnames)
    (throwError $ ElabError $ "nombre " ++ n ++ " repetido")
  ty <- elabType sty
  ctx <- get
  put ctx { datatypes = n : datatypes ctx }
  DataDecl n ty <$> mapM elabCons scons


elabCons :: MonadElab m => SConsDecl -> m ConsDecl
elabCons (ConsDecl n sty) = do
  gnames <- globalNames
  when (n `elem` gnames )
    (throwError $ ElabError $ "nombre " ++ n ++ " repetido")
  ty <- elabType sty
  return (ConsDecl n ty)


elab :: MonadElab m => STerm -> m Term
elab (Lit n)
  | n >= 0 = return (iterate suc zero !! n)
  | otherwise = error "elab: negative integer"
elab SSuc = return (Con Suc)
elab SNat = return (Data Nat)
elab SRefl = return refl
elab (SEq t u) = do
  t' <- elab t
  u' <- elab u
  return (Data $ Eq t' u')
elab (SV x) = do
  mv <- gets variable
  case mv of
    Nothing -> throwError (ElabError $ "var " ++ x ++ " no definida")
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
    (throwError (ElabError "casos repetidos en cláusula elim"))
  mapM_ checkArgNames bs
  mapM elabBranch bs

checkArgNames :: MonadElab m => SElimBranch -> m ()
checkArgNames (ElimBranch _ as _ ) =
  when (duplicateName as) (throwError (ElabError "nombre duplicado en case"))

elabBranch :: MonadElab m => SElimBranch -> m ElimBranch
elabBranch (ElimBranch "zero" as t) = case as of
  [] -> ElimBranch Zero [] <$> elab t
  _ -> throwError (ElabError "el constructor 'zero' no toma argumentos")
elabBranch (ElimBranch "suc" as t) = case as of
  [] -> throwError (ElabError "faltan argumentos para el constructor 'suc'")
  [n] -> do
    ctx <- get
    put ctx { local = n : local ctx }
    t' <- elab t
    put ctx
    return (ElimBranch Suc [n] t')
  _ -> throwError (ElabError "el constructor 'suc' toma un solo argumento") 
elabBranch (ElimBranch "refl" as t) = case as of
  [] -> ElimBranch Refl [] <$> elab t
  _ -> throwError (ElabError "el constructor 'refl' toma un solo argumento")
elabBranch (ElimBranch nc as t) = do
  ctx <- get
  case lookupWith nc (cons ctx) conName id of
    Nothing ->
      throwError (ElabError $ "el constructor '" ++ nc ++ "' no está definido")
    Just c -> do
      unless (length as == conArity c) $
        throwError (ElabError $
        "cantidad de argumentos incorrecta para el construcor '" ++ nc ++ "'")
      put ctx { local = reverse as ++ local ctx }
      t' <- elab t
      put ctx
      return (ElimBranch (DataCon c) as t')