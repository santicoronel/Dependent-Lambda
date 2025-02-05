module Datatype where

import Lang
import Common
import MonadTypeCheck
import TypeCheck
import Error
import Reduce (reduceNF)
import Substitution

import Control.Monad.Except
import Control.Monad.Extra ( ifM )



data DataError = DError String

checkData :: DataDecl -> Either DataError DataDef
checkData (DataDecl n ty cs) = do
  (s, ar) <- checkDataType ty
  when (duplicateName (map consDeclName cs))
    (throwError $ DError $ "nombre de constructor " ++ n ++ " duplicado") 
  cs <- mapM (checkDataCons n ar) cs
  return (DataDef n [] ty s ar cs)

checkDataType :: Type -> Either DataError (Sort, Int)
checkDataType = go . unType
  where
    go (Sort s) = return (s, 0)
    go (Pi arg ty) = (\(s, ar) -> (s, ar + 1)) <$> checkDataType ty
    go t = Left (DError $ show t ++ " inesperado en dataype definition")

checkDataCons :: Name -> Int -> ConsDecl -> Either DataError Constructor
checkDataCons d ar (ConsDecl n ty) = do
  car <- checkConsType d ar ty
  return (Constructor n ty car)


checkConsType :: Name -> Int -> Type -> Either DataError Int
checkConsType d ar = go . unType
  where
    go :: Term -> Either DataError Int
    go (Pi arg ty) = (1 + ) <$> go (unType ty)
    go t = checkReturn 0 t >> return 0

    checkReturn n (Data (DataT e))
      | d == e = if n == ar 
        then return ()
        else Left (DError $ "datatype " ++ d ++ " aplicado parcialmente")
      | otherwise = Left (DError $ "datatype " ++ e ++ " en tipo de retorno")
    checkReturn n (t :@: u) = checkReturn (n + 1) t


checkConsSort :: MonadTypeCheck m => DataDef -> m ()
checkConsSort dd = mapM_ checkCons (dataCons dd)
  where
    checkCons c = do
      p <- checkType (unType $ conType c)
      case p of
        Left ty -> throwError (EDataSort c ty (dataSort dd))
        Right _ -> return ()
    checkType :: MonadTypeCheck m => Term -> m (Either Type ())
    checkType (Pi arg ty) = do
      s <- inferSort (argType arg)
      if subSort s (dataSort dd)
        then return (Right ())
        else return (Left (argType arg))
    checkType _ = return (Right ())

checkPositivity :: MonadTypeCheck m => DataDef -> m ()
checkPositivity d = mapM_ (\c -> positivityCheck (conType c) d d) (dataCons d) 

positivityCheck :: MonadTypeCheck m => Type -> DataDef -> DataDef -> m ()
positivityCheck ty dx di = go (unType ty)
  where
    go (Pi arg ty) = doAndRestore (do
      strictPositivityCheck (argType arg) dx
      i <- bindArg (argName arg) (argType arg)
      positivityCheck (openType i ty) dx di
      )
    go t = goApp t

    goApp :: MonadTypeCheck m => Term -> m ()
    goApp (Data (DataT n)) | n == dataName di = return ()
    goApp (t :@: u) = do
      when (dx `dataOccurs` u)
        $ throwError $ EPositivity (Type u) dx di
      goApp t
    goApp _ = error "positivityCheck"

strictPositivityCheck :: MonadTypeCheck m => Type -> DataDef -> m ()
strictPositivityCheck ty dx = reduceNF (unType ty) >>= go
  where
    go t | not (dx `dataOccurs` t) = return ()
    go (Pi arg ty) = doAndRestore (do
      when (dx `dataOccurs` unType (argType arg))
        $ throwError $ EPositivity (argType arg) dx dx
      i <- bindArg (argName arg) (argType arg)
      strictPositivityCheck (openType i ty) dx
      )
    go t = goApp t

    goApp t@(Data (Eq u v)) = do
      when ((dx `dataOccurs` u) || (dx `dataOccurs` v))
        $ throwError $ EPositivity (Type t) dx dx
    goApp (Data (DataT n))
      | n == dataName dx = return ()
      | otherwise = do
        di <- getDataDef n
        mapM_ (\c -> positivityCheck (conType c) dx di)
              (dataCons di)
    goApp (t :@: u) = do
      when (dx `dataOccurs` u)
        $ throwError $ EPositivity (Type u) dx dx
      goApp t

dataOccurs :: DataDef -> Term -> Bool
dataOccurs d = go 
  where
    go (Lam arg t) = 
      go (unType $ argType arg) || argName arg /= dataName d && go t
    go (t :@: u) = go t || go u
    go (Data (Eq t u)) = go t || go u
    go (Data (DataT n)) = n == dataName d
    go (Elim t bs) = go t || any goBranch bs
    go (Fix f arg t) =
      go (unType $ argType arg) ||
      argName arg /= f && argName arg /= dataName d && go t
    go (Pi arg ty) =
      go (unType $ argType arg) || argName arg /= dataName d && go (unType ty)
    go (Ann t ty) =  go t || go (unType ty)
    go _ = False

    goBranch b = notElem (dataName d) (elimConArgs b) && go (elimRes b)
    