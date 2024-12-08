module Substitution where

import Lang

varChanger :: (Int -> Int -> Term)
           -> (Int -> Int -> Term)
           -> Term -> Term
varChanger bound local = go 0
  where
    go d (V (Bound i)) = bound d i
    go d (V (Free n)) = local d n
    go d (Lam arg  t) =
      let arg' = arg { argType = goType d (argType arg)}
      in  Lam (goArg d arg) (go (d + 1) t)
    go d (t :@: u) = go d t :@: go d u
    go d (Elim t bs) = Elim (go d t) (map (goBranch d) bs)
    go d (Fix f arg ty t) = Fix f (goArg d arg) (goType (d + 1) ty) (go (d + 2) t)
    go d (Pi arg ty) = Pi (goArg d arg) (goType (d + 1) ty)
    go d (Ann t ty) = Ann (go d t) (goType d ty)

    goType d (Type t) = Type $ go d t

    goArg d (Arg ty n) = Arg (goType d ty) n
    
    goBranch d (ElimBranch c as t) =
      let ar = length as
      in  ElimBranch c as (go (d + 1) t)

open :: Int -> Term -> Term
open x = varChanger bnd (\_ n -> V (Free n))
  where
    bnd d i
      | i < d = V (Bound i)
      | i == d = V (Free x)
      | otherwise = error "open: bound fuera de rango"

openType :: Int -> Type -> Type
openType x = Type . open x . unType

open2 :: Int -> Int -> Term -> Term
open2 f x = varChanger bnd (\_ n -> V (Free n))
  where
    bnd d i
      | i < d = V (Bound i)
      | i == d = V (Free x)
      | i == d + 1 = V (Free f)
      | otherwise = error "open2: bound fuera de rango"

open2Type :: Int -> Int -> Type -> Type
open2Type f x = Type . open2 f x . unType

close :: Int -> Term -> Term
close x = varChanger (\_ i -> V (Bound i)) lcl
  where
    lcl d n
      | n == x = V (Bound d)
      | otherwise = V (Free n)

closeType :: Int -> Type -> Type
closeType x = Type . close x . unType

close2 :: Int -> Int -> Term -> Term
close2 f x = varChanger (\_ i -> V (Bound i)) lcl
  where
    lcl d n
      | n == x = V (Bound d)
      | n == f = V (Bound (d + 1))
      | otherwise = V (Free n)

close2Type :: Int -> Int -> Type -> Type
close2Type f x = Type . close2 f x . unType

subst :: Term -> Term -> Term
subst u = varChanger bnd (\_ n -> V (Free n))
  where
    bnd d i
      | i < d = V (Bound i)
      | i == d = u
      | otherwise = error "subst: bound fuera de rango"

substType :: Term -> Type -> Type
substType u = Type . subst u . unType

subst2 :: Term -> Term -> Term -> Term
subst2 f x = varChanger bnd (\_ n -> V (Free n))
  where
    bnd d i
      | i < d = V (Bound i)
      | i == d = x
      | i == d + 1 = f
      | otherwise = error "subst2: bound fuera de rango"

subst2Type :: Term -> Term -> Type -> Type
subst2Type f x = Type . subst2 f x . unType