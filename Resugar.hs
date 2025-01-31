module Resugar (
  resugar,
  resugarType,
  resugarDecl
  ) where

import Lang
import Common
import Substitution ( open )

import Control.Monad.State

data NamingContext = NContext {
  freeNames :: [(Int, Name)],
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
  -- NICETOHAVE reemplazar f por declName
  t@(SFix f args u) -> if f == declName d
    then  let ns = concatMap argName args
              ty' = trimPiArgs (length ns) ty
          in  SDecl f args (resugarType ns rs ty') u True
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
    go (V (Free i)) = SV <$> freshenFree ns rs i
    go (V (Global x)) = return (SV x)
    go (Lam arg t) = doAndRestore $ do
      ty <- Type <$> go (unType $ argType arg)
      n <- freshenBound rs (argName arg)
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
    go (Fix f arg t) = doAndRestore $ do
      argty <- Type <$> go (unType $ argType arg)
      ctx <- get
      x <- freshenBound rs (argName arg)
      f' <- freshenBound rs f
      bindName f'
      bindName x
      t' <- go t
      case t' of
        SLam args st ->
          let sarg = Arg [argName arg] argty
          in  return $ SFix f' (sarg <:> args) st
        _ -> return (SFix f' [Arg [x] argty] t')
    go (Pi arg ty) | not (Bound 0 `occursInType` ty) = doAndRestore $ do
      aty <- Type <$> go (unType $ argType arg)
      n <- freshenBound rs (argName arg)
      bindName n
      rty <- Type <$> go (unType ty)
      return (SFun aty rty)
    go (Pi arg ty) = doAndRestore $ do
      argty <- Type <$> go (unType $ argType arg)
      n <- freshenBound rs (argName arg)
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
      as' <- mapM (freshenBound rs) as
      mapM_ bindName as'
      t' <- go t
      return (ElimBranch (conHeadName c) as' t')


appPi :: STerm -> [Name] -> Term
appPi (SPi arg ty) = undefined 

bindName :: Name -> State NamingContext ()
bindName n = do
  ctx <- get
  put ctx { boundNames = n : boundNames ctx }


usedNames :: NamingContext -> [Name]
usedNames ctx = boundNames ctx ++ map snd (freeNames ctx)

freshenBound :: [Name] -> Name -> State NamingContext Name
freshenBound rs n = do
  ctx <- get
  return $ freshen (usedNames ctx) rs n
  

freshenFree :: [Name] -> [Name] -> Int -> State NamingContext Name
freshenFree ns rs i = do
  ctx <- get
  case lookup i (freeNames ctx) of
    Just n -> return n
    Nothing -> do 
      let n = freshen (usedNames ctx) rs (ns !! i)
      put ctx { freeNames = (i, n) : freeNames ctx }
      return n

freshen :: [Name] -> [Name] -> Name -> Name
freshen used rs n = if n `elem` used
    then go (map show [1..]) n
    else n
  where 
    go :: [Name] -> Name -> Name
    go (i:is) n =
      let ni = n ++ "_" ++ i
      in if ni `elem` used || ni `elem` rs
          then go is n
          else ni