module TypeCheck ( infer, check, inferSort, shouldBeType ) where

import Lang
import Error
import MonadTypeCheck
import Context
import Unify
import Equality
import Reduce
import Substitution
import Common

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Extra (whenM, ifM, unlessM)


infer :: MonadTypeCheck m => Term -> m Type
infer (V v) = case v of
  Bound x -> error $ "typecheck: bound " ++ show x
  Free x -> getLocalType x
  Global x -> getGlobalType x
infer (Lam arg t) = doAndRestore (do
  shouldBeType (argType arg)
  i <- bindArg (argName arg) (argType arg)
  ty <- infer (open i t)
  return (Type $ Pi arg (closeType i ty))
  )
infer (t :@: u) = do
  tt <- infer t
  tt' <- reduceType tt
  case unType tt' of
    Pi arg ty -> do
      check u (argType arg)
      i <- bindLocal (argName arg) (argType arg) u
      reduceType (openType i ty)
    _ -> throwError $ EFun tt'
infer (Con ch) = inferCon ch
infer (Data dt) = inferData dt
infer (Elim t bs) = inferElim t bs
infer t@(Fix f arg u) = throwError $ EIncomplete t
infer (Pi arg ty) = doAndRestore (do
  tty <- inferSort (argType arg)
  i <- bindArg (argName arg) (argType arg)
  sty <- inferSort (openType i ty)
  let sty' = closeSort i sty
  return (pisort tty arg sty')
  )
infer (Sort (Set i)) = return (set (i + 1))
infer (Ann t tt) = do
  shouldBeType tt
  check t tt
  return tt

inferCon :: MonadTypeCheck m => ConHead -> m Type
inferCon Refl = throwError (EIncomplete (Con Refl))
inferCon (DataCon c) = return (conType c)

inferData :: MonadTypeCheck m => DataType -> m Type
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
  tt' <- reduceType tt
  case inspectData (unType tt') of
    Just (dt, as) -> inferElim' dt as bs
    Nothing -> throwError (ENotData tt')

inferElim' :: MonadTypeCheck m => DataType -> [Term] -> [ElimBranch] -> m Type
inferElim' (Eq t u) [] bs = case bs of
  [] -> throwError EIncompleteBot
  [ElimBranch Refl [] r] -> doAndRestore (do
    ifM (unifyTerms t u)
      (infer r)
      (throwError EManyCases)
    )
  [ElimBranch Refl _ _] -> error "typecheck: illformed branch"
  _ -> throwError EManyCases
inferElim' (DataT d) as bs = do
  dd <- getDataDef d
  inferElimDataT dd as bs
inferElim' _ _ _ = error "typerror in inferElim"

inferElimDataT :: MonadTypeCheck m => DataDef -> [Term] -> [ElimBranch] -> m Type
inferElimDataT dd as bs =
  case findAllBranches (map DataCon $ dataCons dd) bs of
    Left b -> throwError (EWrongCons (elimCon b))
    Right ms -> inferBranches dd as ms

inferBranches :: MonadTypeCheck m => DataDef -> [Term] -> [(ConHead, Maybe ElimBranch)] -> m Type
inferBranches _ _ [] = throwError EIncompleteBot
inferBranches dd as ((DataCon c, mb) : ms) = case mb of
  Nothing -> throwError EIncompleteBot
  Just b -> do
    ty <- inferBranch dd as b
    checkBranches dd as ms ty
    return ty

inferBranch :: MonadTypeCheck m => DataDef -> [Term] -> ElimBranch -> m Type
inferBranch dd as b = case elimCon b of
  DataCon c -> doAndRestore (do
    is <- mapM newVar (elimConArgs b)
    let (cty, args) = dataConsArgTypes c
        cty' = openMany is (unType cty)
        (_, cas) = getArgs cty'
    ru <- foldM (\r p -> (r &&) <$> uncurry unifyTerms p) True (zip cas as)
    unless ru (throwError EManyCases)
    -----------------------------------------------------------
    let tys = map argType args
    let tys' = openManyTypes is tys
    zipWithM_ addBinder is tys'
    infer (openMany is (elimRes b))
    )
  c -> throwError (EWrongCons c)


inferSort :: MonadTypeCheck m => Type -> m Sort
inferSort (Type t) = do
  tt <- infer t
  tt' <- reduceType tt
  case unType tt' of
    Sort s -> return s
    _ -> throwError (ENotType t)

check :: MonadTypeCheck m => Term -> Type -> m ()
check (Lam arg t) ty = doAndRestore (do
  shouldBeType (argType arg)
  ty' <- reduceType ty
  case unType ty' of
    Pi piarg pity -> do
      argType arg `tequal` argType piarg
      i <- bindArg (argName arg) (argType piarg)
      check (open i t) (openType i pity)
    _ -> throwError $ ECheckFun (Lam arg t) ty'
  )
check t@(Fix f arg u) ty = do
  shouldBeType (argType arg)
  -- MAYBE tratar a f como un lambda a partir de aca
  -- pero marcada como recursiva
  -- tendria q abrir `a` solo para f
  ty' <- reduceType ty
  case unType ty' of
    Pi piarg rty -> do
      argType arg `tequal` argType piarg
      (fi, xi) <- bindFix f rty t arg
      check (open2 fi xi u) (openType xi rty)
    _ -> throwError $ EFun ty
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

checkElim :: MonadTypeCheck m => Term -> [ElimBranch] -> Type -> m ()
checkElim t bs ty = do
  t' <- reduce t
  case t' of
    (V (Free x)) -> do
      tt <- getLocalType x
      tt' <- reduceType tt
      case inspectData (unType tt') of
        Just (dt, as) -> checkElim' x dt as bs ty
        _ -> throwError (ENotData tt')
    _ -> do
      -- NICETOHAVE hacer esto menos croto
      let bs' = map (\b -> b { elimRes = Ann (elimRes b) ty }) bs
      et <- inferElim t bs'
      et `tequal` ty

checkBranches :: MonadTypeCheck m =>
  DataDef -> [Term] -> [(ConHead, Maybe ElimBranch)] -> Type -> m ()
checkBranches dd as ms ty = mapM_ (flip (checkBranch dd as) ty) ms

checkBranch :: MonadTypeCheck m =>
  DataDef -> [Term] -> (ConHead, Maybe ElimBranch) -> Type -> m ()
checkBranch dd as (DataCon c, mb) ty = case mb of
  Nothing -> doAndRestore (do
    let (cty, args) = dataConsArgTypes c
    is <- mapM (newVar . argName) args
    let cty' = openMany is (unType cty)
        (_, cas) = getArgs cty'
    -- ver si hay una mejor alternativa a foldM
    ru <- foldM (\r p -> (r &&) <$> uncurry unifyTerms p) True (zip cas as)
    when ru $ throwError ECasesMissing
    )
  Just b -> do
    et <- inferBranch dd as b
    et `tequal` ty

checkElim' :: MonadTypeCheck m => Int -> DataType -> [Term] -> [ElimBranch] -> Type ->  m ()
-- Eq
checkElim' x (Eq t u) [] bs rty = case bs of
  [] -> doAndRestore $
    whenM (unifyTerms t u) $ throwError ECasesMissing
  [ElimBranch Refl [] r] -> doAndRestore (do
    unlessM (unifyTerms t u) (throwError EManyCases)
    bindPattern x (Con Refl)
    check r rty)
  [ElimBranch Refl _ _] -> error "checkElim': Refl args"
  _ -> throwError EManyCases
-- DataT
checkElim' x (DataT d) as bs rty = do
  dd <- getDataDef d
  checkElimDataT x dd as bs rty
checkElim' _ _ _ _ _ = error "typeerror in checkElim"

checkElimDataT :: MonadTypeCheck m =>
  Int -> DataDef -> [Term] -> [ElimBranch] -> Type -> m ()
checkElimDataT x dd as bs ty =
  case findAllBranches (map DataCon $ dataCons dd) bs of
    Left b -> throwError (EWrongCons (elimCon b))
    Right ms -> checkBranches' x dd as ms ty

checkBranches' :: MonadTypeCheck m =>
  Int -> DataDef -> [Term] -> [(ConHead, Maybe ElimBranch)] -> Type -> m ()
checkBranches' x dd as ms ty = do
  mapM_ (flip (checkBranch' x dd as) ty) ms

checkBranch' :: MonadTypeCheck m =>
  Int -> DataDef -> [Term] -> (ConHead, Maybe ElimBranch) -> Type -> m ()
checkBranch' x dd as (DataCon c, mb) ty = case mb of
  Nothing -> doAndRestore (do
    let (cty, args) = dataConsArgTypes c
    is <- mapM (newVar . argName) args
    let cty' = openMany is (unType cty)
        (_, cas) = getArgs cty'
    -- ver si hay una mejor alternativa a foldM
    ru <- foldM (\r p -> (r &&) <$> uncurry unifyTerms p) True (zip cas as)
    when ru $ throwError ECasesMissing
    )
  Just b -> doAndRestore (do
    is <- mapM newVar (elimConArgs b)
    let (cty, args) = dataConsArgTypes c
        cty' = openMany is (unType cty)
        (_, cas) = getArgs cty'
    -- ver si hay una mejor alternativa a foldM
    ru <- foldM (\r p -> (r &&) <$> uncurry unifyTerms p) True (zip cas as)
    unless ru $ throwError EManyCases
    --------------------------------------------------------------------------
    let tys = map argType args
    let tys' = openManyTypes is tys
    zipWithM_ addBinder is tys'
    let consVal = foldl (:@:) (Con (DataCon c)) (map var is)
    bindPattern x consVal
    check (openMany is (elimRes b)) ty
    )

shouldBeType :: MonadTypeCheck m => Type -> m ()
shouldBeType ty = void (inferSort ty)

eqsort :: Sort -> Type
eqsort (Set i) = set i

-- x ahora el argumento no puede aparecer en el sort
pisort :: Sort -> Arg -> Sort -> Type
pisort (Set i) _ (Set j) = set (max i j)