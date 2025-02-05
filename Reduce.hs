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
import Common

import Control.Monad ( mapM, zipWithM_, zipWithM )
import Data.Maybe ( isJust )
import Data.Foldable (foldrM)
import Control.Monad.Extra ( ifM, (>=>) )
import Control.Monad.State (state)


data Kont =
  KFun Term
  | KArg Term
  | KElim [ElimBranch] deriving Show

type Stack = [Kont]

reduce :: MonadTypeCheck m => Term -> m Term
reduce = reduceNF

reduceType :: MonadTypeCheck m => Type -> m Type
reduceType = reduceNFType

reduceNF :: MonadTypeCheck m => Term -> m Term
reduceNF = betaReduceNF >=> etaReduce

reduceNFType :: MonadTypeCheck m => Type -> m Type
reduceNFType = betaReduceNFType >=> etaReduceType 

betaReduceNF :: MonadTypeCheck m => Term -> m Term
betaReduceNF t = seek [] t
  where
    seek s (V (Bound i)) = error $ "bound " ++ show i ++ " in betaReduceNF"
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
    seek s t@(Pi arg ty) = doAndRestore $ do
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
        t' <- betaReduceNF (open i t)
        return (Lam arg $ close i t')
        )
      Fix f arg u -> doAndRestore (do
        fi <- bindRecDef f t
        xi <- newVar (argName arg)
        u' <- seek [] (open2 fi xi u)
        return (Fix f arg (close2 fi xi u'))
        )
      Elim t bs -> Elim <$> betaReduceNF t <*> betaReduceNFBranches bs
      (a :@: b) -> (:@:) <$> betaReduceNF a <*> betaReduceNF b
      (Data (Eq a b)) -> Data <$> (Eq <$> betaReduceNF a <*> betaReduceNF b)
      _ -> return t

    destroyFun s (V (Free i)) u = do
      dx <- getLocalDef i
      case dx of
        Nothing -> do
          u' <- betaReduceNF u
          destroy s (V (Free i) :@: u')
        Just t -> if isCons u
          then destroy (KArg u : s) t
          else destroy s (V (Free i) :@: u)
    destroyFun s t@(Fix f arg a) u = if isCons u
        then do
          fi <- bindRecDef f t
          xi <- bindLocalDef (argName arg) u
          a' <- seek s (open2 fi xi a)
          t' <- betaReduceNF t
          return (substFree fi t' a')
        else destroy s (t :@: u)
    destroyFun s t u = destroy s (t :@: u)

betaReduceNFType :: MonadTypeCheck m => Type -> m Type
betaReduceNFType (Type t) = Type <$> betaReduceNF t

betaReduceNFBranches :: MonadTypeCheck m => [ElimBranch] -> m [ElimBranch]
betaReduceNFBranches = mapM betaReduceNFBranch
  where
    betaReduceNFBranch :: MonadTypeCheck m => ElimBranch -> m ElimBranch
    betaReduceNFBranch b = doAndRestore (do
      let atys = consArgTypes (elimCon b)
      is <- mapM newVar (elimConArgs b)
      let res = openMany is (elimRes b)
      res' <- betaReduceNF res
      return b { elimRes = closeMany is res' }
      )

inspectCons :: Term -> Maybe (ConHead, [Term])
inspectCons = go []
  where
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


etaReduce :: MonadTypeCheck m => Term -> m Term
etaReduce t = go t
  where
    go :: MonadTypeCheck m => Term -> m Term
    go (Lam arg t) = do
      ty <- etaReduceType (argType arg)
      let arg' = arg { argType = ty }
      t' <- etaReduce t
      case t' of
        f :@: (V (Bound 0)) ->
          if Bound 0 `occursIn` f
            then return (Lam arg' t')
            else return (shift (-1) f)
        _ -> return (Lam arg' t')
    go (t :@: u) = (:@:) <$> go t <*> go u
    go (Elim t bs) = Elim <$> go t <*> mapM goBranch bs
    go (Fix f arg t) = do
      aty <- etaReduceType (argType arg)
      let arg' = arg { argType = aty }
      t' <- etaReduce t
      return (Fix f arg' t')
    go (Pi arg ty) = do
      aty <- etaReduceType (argType arg)
      let arg' = arg { argType = aty }
      ty' <- etaReduceType ty
      return (Pi arg' ty')
    go (Ann t ty) = Ann <$> go t <*> etaReduceType ty
    go t = return t

    goBranch (ElimBranch c ns t) = do
      t' <- etaReduce t
      return (ElimBranch c ns t')

etaReduceType ty = Type <$> etaReduce (unType ty)