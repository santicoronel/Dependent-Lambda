module Resugar ( resugar, resugarType, resugarDecl ) where

import Lang
import Substitution
import Common

import Control.Monad.State

data NamingContext = NContext {
  usedNames :: [Name],
  boundNames :: [Name]
} deriving Show

-- TODO agrupar lambdas
resugarDecl :: Decl -> Type -> SDecl
resugarDecl d ty = case resugar [] [] (declDef d) of
  SLam arg t -> SDecl (declName d) [arg] (resugarType [] [] ty) t
  t -> SDecl (declName d) [] (resugarType [] [] ty) t

resugarType :: [Name] -> [Name] -> Type -> SType
resugarType ns rs = Type . resugar ns rs . unType

resugar :: [Name] -> [Name] -> Term -> STerm
resugar ns rs t = evalState (go t) (NContext [] [])
  where
    go :: Term -> State NamingContext STerm
    go (V (Bound i)) = do
      bn <- gets boundNames
      return (SV (bn !! i))
    go (V (Free i)) = SV <$> freshen rs (ns !! i)
    go (V (Global x)) = return (SV x)
    go (Lam arg t) = doAndRestore $ do
      ty <- Type <$> go (unType $ argType arg)
      n <- freshenBound (argName arg)
      bindName n
      t' <- go t
      case t' of
        SLam sarg st -> if argType sarg == ty
          then return $ SLam (Arg (n : argName sarg) ty) st
          else return (SLam (Arg [n] ty) t')
        _ -> return (SLam (Arg [n] ty) t')
    go (t :@: u) = do
      t' <- go t
      u'<- go u
      case (t', u') of
        (SSuc, Lit n) -> return (Lit (n + 1))
        _ -> return (SApp t' u')  
    go (Con ch) = goConHead ch
    go (Data dt) = case dt of
      Nat -> return SNat
      Eq t u -> SEq <$> go t <*> go u
      DataT d -> return (SV d)
    go (Elim t bs) = SElim <$> go t <*> mapM goBranch bs
    go (Fix f arg ty t) = doAndRestore $ do
      argty <- Type <$> go (unType $ argType arg)
      ctx <- get
      x <- freshenBound (argName arg)
      bindName x
      ty' <- Type <$> go (unType ty)
      put ctx
      f' <- freshenBound f
      bindName f'
      bindName x
      t' <- go t
      case t' of
        SLam sarg st -> if argType sarg == argty
          then
            -- TODO hacer bien esto (como??)
            let sns = argName sarg
                -- sty = appPi (unType ty) sns
            in return $
            --SFix f' (Arg (x : argName sarg) argty) ty' st
            SFix f' (Arg [x] argty) ty' t'
          else return (SFix f' (Arg [x] argty) ty' t')
        _ -> return (SFix f' (Arg [x] argty) ty' t')
    go (Pi arg ty) = doAndRestore $ do
      argty <- Type <$> go (unType $ argType arg)
      n <- freshenBound (argName arg)
      bindName n
      ty' <- go (unType ty)
      case ty' of
        SPi sarg sty -> if argType sarg == argty
          then return (SPi (Arg (n : argName sarg) argty) sty)
          else return (SPi (Arg [n] argty) (Type ty'))
        _ -> return (SPi (Arg [n] argty) (Type ty'))
    go (Sort (Set i)) = return (SSort (Set i))
    go (Ann t ty) = SAnn <$> go t <*> (Type <$> go (unType ty))

    goConHead Zero = return (Lit 0)
    goConHead Suc = return SSuc
    goConHead Refl = return SRefl
    goConHead (DataCon c) = return (SV $ conName c)

    goBranch :: ElimBranch -> State NamingContext SElimBranch
    goBranch (ElimBranch c as t) = doAndRestore $ do
      as' <- mapM freshenBound as
      mapM_ bindName as'
      t' <- go t
      return (ElimBranch (conHeadName c) as' t')
    
    conHeadName Zero = "zero"
    conHeadName Suc = "suc"
    conHeadName Refl = "refl"
    conHeadName (DataCon c) = conName c


appPi :: STerm -> [Name] -> Term
appPi (SPi arg ty) = undefined 

bindName :: Name -> State NamingContext ()
bindName n = do
  ctx <- get
  put ctx { boundNames = n : boundNames ctx }

freshenBound :: Name -> State NamingContext Name
freshenBound = freshen []

-- TODO chequear que no pise un constructor
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
          ni = n ++ i
      if n ++ i `elem` ns || n ++ i `elem` rs
        then go is rs n
        else do
          put ctx { usedNames = ni : ns }
          return ni