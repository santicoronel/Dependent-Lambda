module Resugar (
  resugar,
  resugarType,
  resugarDecl
  ) where

import Lang
import Substitution
import Common

import Control.Monad.State

data NamingContext = NContext {
  usedNames :: [Name],
  boundNames :: [Name]
} deriving Show


trimSPiArgs :: Int -> SType -> SType
trimSPiArgs n (Type t) = go n t
  where
    go 0 (SPi [] ty) = ty
    go 0 t = Type t
    go n (SPi (Arg as aty : args) ty) | n > 0 =
      let l = length as
      in if l > n 
        then Type $ SPi (Arg (drop n as) aty : args) ty
        else go (n - l) (SPi args ty)
    go n t = error $ "trimSPiArgs: go " ++ show n ++ " " ++ show t

trimPiArgs :: Int -> Type -> Type
trimPiArgs n (Type t) | n > 0 = go 0 t
  where
    go i t | i == n = Type t
    go i (Pi arg ty) = go (i + 1) (open i $ unType ty)

resugarDecl :: [Name] -> Decl -> Type -> SDecl
resugarDecl rs d ty = case resugar [] rs (declDef d) of
  u@(SLam args t) ->
    let ns = concatMap argName args
        ty' = trimPiArgs (length ns) ty
    in SDecl (declName d) args (resugarType ns rs ty') t False
  t@(SFix f args ty' u) -> if f == declName d
    then SDecl f args ty' u True
    else SDecl (declName d) [] (resugarType [] rs ty) t False
  t -> SDecl (declName d) [] (resugarType [] rs ty) t False

resugarType :: [Name] -> [Name] -> Type -> SType
resugarType ns rs = Type . resugar ns rs . unType

resugar :: [Name] -> [Name] -> Term -> STerm
resugar ns rs t = evalState (go t) (NContext [] [])
  where
    go :: Term -> State NamingContext STerm
    go (V (Bound i)) = do
      bn <- gets boundNames
      if i >= length bn 
        then error $ show i ++ " " ++ show bn
        else return (SV (bn !! i))
    go (V (Free i)) = SV <$> freshen rs (ns !! i)
    go (V (Global x)) = return (SV x)
    go (Lam arg t) = doAndRestore $ do
      ty <- Type <$> go (unType $ argType arg)
      n <- freshen rs (argName arg)
      bindName n
      t' <- go t
      case t' of
        SLam args st -> 
          let sarg = Arg [argName arg] ty
          in  return $ SLam (sarg <:> args) st
        _ -> return (SLam [Arg [n] ty] t')
    go (t :@: u) = do
      t' <- go t
      u'<- go u
      case (t', u') of
        (SSuc, Lit n) -> return (Lit (n + 1))
        _ -> return (SApp t' u')  
    go (Con ch) = return (resugarConHead ch)
    go (Data dt) = case dt of
      Eq t u -> SEq <$> go t <*> go u
      DataT d -> return (SV d)
    go (Elim t bs) = SElim <$> go t <*> mapM goBranch bs
    go (Fix f arg ty t) = doAndRestore $ do
      argty <- Type <$> go (unType $ argType arg)
      ctx <- get
      x <- freshen rs (argName arg)
      bindName x
      ty' <- Type <$> go (unType ty)
      put ctx
      f' <- freshen rs f
      bindName f'
      bindName x
      t' <- go t
      case t' of
        SLam args st ->
          let sarg = Arg [argName arg] argty
              ty'' = trimSPiArgs (length $ concatMap argName args) ty'
          in  return $ SFix f' (sarg <:> args) ty'' st
        _ -> return (SFix f' [Arg [x] argty] ty' t')
    go (Pi arg ty) = doAndRestore $ do
      argty <- Type <$> go (unType $ argType arg)
      n <- freshen rs (argName arg)
      bindName n
      ty' <- go (unType ty)
      case ty' of
        SPi args sty -> 
          let sarg = Arg [argName arg] argty
          in  return $ SPi (sarg <:> args) sty
        _ -> return (SPi [Arg [n] argty] (Type ty'))
    go (Sort (Set i)) = return (SSort (Set i))
    go (Ann t ty) = SAnn <$> go t <*> (Type <$> go (unType ty))

    resugarConHead Refl = SRefl
    resugarConHead (DataCon c)
      | c == zeroCons = Lit 0
      | c == sucCons = SSuc
      | otherwise = SV $ conName c
    
    goBranch :: ElimBranch -> State NamingContext SElimBranch
    goBranch (ElimBranch c as t) = doAndRestore $ do
      as' <- mapM (freshen rs) as
      mapM_ bindName as'
      t' <- go t
      return (ElimBranch (conHeadName c) as' t')


appPi :: STerm -> [Name] -> Term
appPi (SPi arg ty) = undefined 

bindName :: Name -> State NamingContext ()
bindName n = do
  ctx <- get
  put ctx { boundNames = n : boundNames ctx }

freshen :: [Name] -> Name -> State NamingContext Name
freshen rs n = do
  ctx <- get
  if n `elem` usedNames ctx
    then go (map show [1..]) rs n
    else do
      put ctx { usedNames = n : usedNames ctx }
      return n
  where 
    go :: [Name] -> [Name] -> Name -> State NamingContext Name
    go (i:is) rs n = do
      ctx <- get
      let ns = usedNames ctx
          ni = n ++ "_" ++ i
      if ni `elem` ns || ni `elem` rs
        then go is rs n
        else do
          put ctx { usedNames = ni : ns }
          return ni