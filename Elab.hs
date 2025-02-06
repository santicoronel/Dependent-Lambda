{-# LANGUAGE FlexibleContexts #-}

module Elab where


import Lang
import Common
import Datatype
import Error

import Control.Monad.State
import Control.Monad.Except
import Data.List ( elemIndex )



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
elabDecl (SDecl n args ty t r) = do
  gnames <- globalNames
  when (n `elem` gnames) 
    (throwError $ ElabError $ "nombre " ++ n ++ " repetido")
  let t' = if r
          then SAnn (SFix n args t) (Type $ SPi args ty)
          else SLam args (SAnn t ty)
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
  | n >= 0 = return (iterate (suc :@:) zero !! n)
  | otherwise = error "elab: negative integer"
elab SSuc = return suc
elab SNat = return (unType natTy)
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
elab (SLam args t) = goArgs (concatMap flattenArg args) t
  where
    goArgs :: MonadElab m => [(Name, SType)] -> STerm -> m Term
    goArgs [] t = elab t
    goArgs (a:as) t = do
      ctx <- get
      arg <- uncurry goArg a
      t' <- goArgs as t
      put ctx
      return $ Lam arg t'
    goArg :: MonadElab m => Name -> SType -> m Arg
    goArg x ty = do
      ty' <- elabType ty
      ctx <- get
      put ctx { local = x : local ctx }
      return (Arg x ty')

elab (SApp t u) = (:@:) <$> elab t <*> elab u
elab (SElim t bs) = do
  t' <- elab t
  bs' <- elabBranches bs
  return (Elim t' bs')
elab (SFix f args t) = do
  let (a, aty, as) = unconsArgs args
  t' <- elabFix a aty as
  argty <- elabType aty
  return (Fix f (Arg a argty) t')
  where
    elabFix a aty args = do
      ctx <- get
      put (ctx { local = a : f : local ctx })
      t' <- elab (SLam args t)
      put ctx
      return t'
elab (SPi args ty) = goArgs (concatMap flattenArg args) ty
  where
    goArgs :: MonadElab m => [(Name, SType)] -> SType -> m Term
    goArgs [] ty = unType <$> elabType ty
    goArgs (a:as) ty = doAndRestore $ do
      arg <- uncurry goArg a
      ty' <- goArgs as ty
      return $ Pi arg (Type ty')
    goArg :: MonadElab m => Name -> SType -> m Arg
    goArg x ty = do
      ty' <- elabType ty
      ctx <- get
      put ctx { local = x : local ctx }
      return (Arg x ty')

elab (SFun aty rty) = doAndRestore $ do
  aty' <- elabType aty
  ctx <- get
  put ctx { local = "__fun-arg__" : local ctx }
  rty' <- elabType rty
  return $ Pi (Arg "__fun-arg__" aty') rty'

elab (SSort s) = return (Sort s)
elab (SAnn t ty) = Ann <$> elab t <*> elabType ty

elabType :: MonadElab m => SType -> m Type
elabType (Type ty) = Type <$> elab ty


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