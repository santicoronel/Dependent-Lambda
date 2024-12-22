module Reduce (
  reduceNF,
  reduce,
  reduceNFType,
  reduceType
) where

import Lang
import MonadTypeCheck (
  MonadTypeCheck,
  getLocalDef,
  isRec,
  getGlobalDef,
  newVar,
  bindLocalDef,
  bindPattern,
  bindRecDef
  )
import Substitution
import Context ( freshVar )
import Common

import Control.Monad ( mapM, zipWithM_, zipWithM )
import Data.Maybe ( isJust )
import Data.Foldable (foldrM)
import Control.Monad.Extra ( ifM )

-- TODO eta reducccion
-- TODO reduccion parcial

data Kont =
  KFun Term
  | KArg Term
  | KElim [ElimBranch] deriving Show

type Stack = [Kont]

-- TODO pensar si de verdad quiero reducir fix una vez
reduceNF :: MonadTypeCheck m => Term -> m Term
reduceNF t = seek [] t
  where
    seek s (V (Bound i)) = error $ "bound " ++ show i ++ " in reduceNF"
    seek s (V (Free i)) = do
      dx <- getLocalDef i
      case dx of
        Nothing -> destroy s (V (Free i))
        Just d -> ifM (isRec i)
          (destroy s (V (Free i)))
          (seek s d)
    seek s (V (Global x)) = do
      dx <- getGlobalDef x
      seek s dx
    seek s (t :@: u) = seek (KArg u : s) t
    seek s (Elim t bs) = seek (KElim bs : s) t
    seek s (Pi arg ty) = do
      i <- newVar (argName arg)
      ty' <- reduceNFType (openType i ty)
      destroy s (Pi arg (closeType i ty'))
    seek s (Ann t ty) = seek s t
    seek s t = destroy s t

    destroy (KFun f : s) t = destroyFun s f t
    destroy (KArg t : s) u = case u of
      Lam arg a -> do
        i <- bindLocalDef (argName arg) t
        seek s (open i a)
      Con _ -> destroy s (u :@: t)
      (_:@:_) -> destroy s (u :@: t)
      _ -> seek (KFun u : s) t
    destroy (KElim bs : s) t = case inspectCons t of
      Just (ch, as) -> do
        let b = match ch bs
        is <- mapM newVar (elimConArgs b)
        zipWithM_ bindPattern is as
        seek s (openMany is (elimRes b))
      Nothing -> destroy s (Elim t bs)
    destroy [] t = case t of
      Lam arg t -> doAndRestore (do
        i <- newVar (argName arg)
        t' <- reduceNF (open i t)
        return (Lam arg $ close i t')
        )
      Fix f arg ty u -> doAndRestore (do
        fi <- bindRecDef f t
        xi <- newVar (argName arg)
        u' <- seek [] (open2 fi xi u)
        return (Fix f arg ty (close2 fi xi u'))
        )
      Elim t bs -> Elim <$> reduceNF t <*> reduceNFBranches bs
      (a :@: b) -> (:@:) <$> reduceNF a <*> reduceNF b
      (Data (Eq a b)) -> Data <$> (Eq <$> reduceNF a <*> reduceNF b)
      _ -> return t

    destroyFun s (V (Free i)) u = do
      dx <- getLocalDef i
      case dx of
        Nothing -> do
          -- puede q esto no haga falta
          -- reducimos argumentos al final
          u' <- reduceNF u
          destroy s (V (Free i) :@: u')
        Just t -> if isCons u
          then destroy (KArg u : s) t
          else destroy s (V (Free i) :@: u)
    destroyFun s t@(Fix f arg ty a) u = if isCons u
        then do
          -- MAYBE tratar a f como un lambda a partir de aca
          -- pero marcada como recursiva
          -- tendria q abrir `a` solo para f
          fi <- bindRecDef f t
          xi <- bindLocalDef (argName arg) u
          a' <- seek s (open2 fi xi a)
          t' <- reduceNF t
          return (substFree fi t' a') -- esta bien esto??
        else destroy s (t :@: u)
    destroyFun s t u = destroy s (t :@: u)

reduceNFType :: MonadTypeCheck m => Type -> m Type
reduceNFType (Type t) = Type <$> reduceNF t

reduceNFBranches :: MonadTypeCheck m => [ElimBranch] -> m [ElimBranch]
reduceNFBranches = mapM reduceNFBranch
  where
    reduceNFBranch :: MonadTypeCheck m => ElimBranch -> m ElimBranch
    reduceNFBranch b = doAndRestore (do
      let atys = consArgTypes (elimCon b)
      -- NICETOHAVE abstraer este patron
      is <- mapM newVar (elimConArgs b)
      let res = openMany is (elimRes b)
      res' <- reduceNF res
      return b { elimRes = closeMany is res' }
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