module Reduce (
  reduceNF,
  reduce,
  reduceNFType,
  reduceType
) where

import Lang
import MonadTypeCheck
import Substitution

import Control.Monad ( mapM, zipWithM_, zipWithM )
import Data.Maybe ( isJust )
import Data.Foldable (foldrM)
import Context ( freshVar )

-- TODO llevar variables libres/frescas para poder
-- dejar variables sin expandir
-- asi podemos hacer reduceHead y tmb reducir fix una vez
-- si hago esto no puedo restorear el entorno jeje


reduceNF :: MonadTypeCheck m => Term -> m Term
reduceNF (V v) = case v of
  Bound i -> error "bound in reduce"
  Free i -> do
    dx <- getLocalDef i
    case dx of
      Nothing -> return (V v)
      Just dx -> return dx
  (Global x) -> getGlobalDef x
-- TODO hace falta restorear??
-- creo q si por el uf
reduceNF (Lam arg t) = doAndRestore (do
  i <- bindArg (argName arg) (argType arg)
  let t' = open i t
  rt <- reduceNF t
  return (Lam arg (close i rt))
  )
reduceNF (t :@: u) = do
  t' <- reduceNF t
  u' <- reduceNF u
  case t' of
    (V _) -> return (t' :@: u')
    (Lam arg t) -> do
      i <- bindLocal (argName arg) (argType arg) u'
      reduceNF (open i t)
    (_ :@: _) -> return (t' :@: u')
    (Fix f arg ty s) -> do
      -- TODO aplicar con var fresca
      -- ahora puedo :) pero tengo q manejarlo en otro lado
      -- i.e. agregar isRec, manejar bien en todos los usos
      if isCons u'
        then do
          (fi, xi) <- bindFun f ty t arg (Just u') -- mm eto ta mal
          reduceNF (open2 fi xi s)
          -- TODO close??
        else return (t' :@: u')
    _ -> error "type error en reduce"
reduceNF (Elim t bs) = do
  t' <- reduceNF t
  case inspectCons t' of
    Just (ch, as) -> doAndRestore (do
      let b = match ch bs
      is <- mapM newVar (elimConArgs b)
      zipWithM_ bindPattern is as
      reduceNF (openMany is (elimRes b))
      )
    Nothing -> Elim t' <$> reduceNFBranches bs
reduceNF t@(Fix f arg ty s) = doAndRestore (do
  (fi, xi) <- bindFun f ty t arg Nothing
  reduceNF (open2 fi xi s)
  )
reduceNF (Pi arg ty) = doAndRestore (do
  i <- bindArg (argName arg) (argType arg)
  ty' <- reduceNFType (openType i ty)
  argty <- reduceNFType (openType i (argType arg))
  return (Pi arg ty')
  )
reduceNF (Ann t ty) = reduceNF t
reduceNF t = return t

reduceNFType :: MonadTypeCheck m => Type -> m Type
reduceNFType (Type t) = Type <$> reduceNF t

-- TODO aca hay un problema
-- necesito informacion de tipo
reduceNFBranches :: MonadTypeCheck m => [ElimBranch] -> m [ElimBranch]
reduceNFBranches = mapM reduceNFBranch
  where
    reduceNFBranch :: MonadTypeCheck m => ElimBranch -> m ElimBranch
    reduceNFBranch b = doAndRestore (do
      let atys = consArgTypes (elimCon b)
      -- TODO esto esta mal!!
      is <- zipWithM bindArg (elimConArgs b) atys
      let res = openMany is (elimRes b)
      res' <- reduceNF res
      return b { elimRes = openMany is res' }
      )

inspectCons :: Term -> Maybe (ConHead, [Term])
inspectCons = go []
  where
    go [] (Con Zero) = Just (Zero, [])
    go [n] (Con Suc) = Just (Suc, [n])
    go [] (Con Refl) = Just (Refl, [])
    go as (Con (DataCon c))
      | length as == conArity c = Just (DataCon c, as)
      | length as < conArity c = Nothing
    go _ (Con _) = error "inspectCons: type error"
    go as (t :@: u) = go (u : as) t
    go _ _ = Nothing

isCons :: Term -> Bool
isCons = isJust . inspectCons

match :: ConHead -> [ElimBranch] -> ElimBranch
match _ [] = error "match"
match ch (b:bs)
  | ch == elimCon b = b
  | otherwise = match ch bs

reduce :: MonadTypeCheck m => Term -> m Term
reduce = reduceNF

reduceType :: MonadTypeCheck m => Type -> m Type
reduceType = reduceNFType


-- NICETOHAVE hacer bien esto

{-
reduceH :: MonadTypeCheck m => Term -> m (Maybe Term)
-- TODO chequear si es rec
reduceH (V (Local x)) = do
  mdx <- getLocalDef
  case mdx of
    Nothing -> do
      res <- mapM reduceHead xes
      return (V (Local x) <$> res)
    (Just dx, _) -> reduceHead (foldl (:@:) dx x)
reduceH (V (Global x) xes) = do
  dx <- getGlobalDef x
  reduceHead (foldl (:@:) dx xes)
reduceH t = reduceHead t

reduceHead :: MonadTypeCheck m => Term -> m (Maybe Term)
reduceHead (V (Local x) xes) = do
  res <- mapM reduceHead xes
  return (V (Local x) <$> res)
reduceHead (V (Global x) xes) = do
  res <- mapM reduceHead xes
  return (V (Global x) <$> res)
reduceHead (Lam arg (Scope t)) = do
  bindArg (argName arg) (argType arg)
  t' <- reduceHead t
  unbind (argName arg)
  return (Lam arg . Scope <$> t')
reduceHead (t :@: u) = do
  rt <- reduceHead t
  ru <- reduceHead u
  case (rt, ru) of
    (Nothing, Nothing) -> return Nothing
    (Just t', _) ->
      let u' = fromJust u ru
      in case t' of
        (V (Local x) xes) -> return (Just $ (V (Local x) (xes ++ [u'])))
        (V (Global x) xes) -> return (Just $ (V (Global x) (xes ++ [u'])))
        (Lam arg (Scope s)) -> do
          bindLocal (argName arg) (argType arg) u'
          reduceHead s
        (Fix f arg ty s) -> do
          bindRec f ty t arg
          bindLocal (argName arg) (argType arg) u'
          reduceHead s
        _ -> error "reduceHead: type error en rt"
    (Nothing, Just u') -> return (Just $ t :@: u') 
reduceHead (Elim t bs) = do
  -- NICETOHAVE no reducir todas las branches si voy a eliminar
  mt <- reduceHead t
  mbs <- reduceHeadBranches
  case (mt, mbs) of
    (Nothing, Nothing) -> return Nothing
    (Nothing, Just bs') -> return (Just $ Elim t bs')
    (Just t', _) ->
      let bs' = fromJust bs mbs
      in case t' of
        V _ _ -> return (Just $ Elim t' bs')
        Con ch as -> matchHead ch as bs'
        _ -> error "reduceHead: type error"
reduceHead t@(Fix f arg ty s) = do
  bindRec f ty t arg
  s' <- reduceHead s
  unbind (argName arg)
  unbind f
  return (Fix f arg ty <$> s')
reduceHead (Pi arg (Scope ty)) = do
  bindArg (argName arg) (argType arg)
  ty' <- reduceHeadType ty
  unbind (argName arg)
  return (Pi arg  . Scope <$> ty')
reduceHead (Ann t ty) = reduceHead t
reduceHead t = return Nothing

reduceHeadType :: MonadTypeCheck m => Type -> m (Maybe Type)
reduceHeadType (Type t) = do
  t' <- reduceHead t
  return (Type <$> t')

-}