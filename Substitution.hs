module Substitution where

import Lang
import Data.List (inits)

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
    go d (Fix f arg ty t) =
      Fix f (goArg d arg) (goType (d + 1) ty) (go (d + 2) t)
    go d (Pi arg ty) = Pi (goArg d arg) (goType (d + 1) ty)
    go d (Ann t ty) = Ann (go d t) (goType d ty)
    go d (Data (Eq t u)) = Data (Eq (go d t) (go d u))
    go _ t = t

    goType d (Type t) = Type $ go d t

    goArg d (Arg n ty) = Arg n (goType d ty)

    goBranch d (ElimBranch c as t) =
      let ar = length as
      in  ElimBranch c as (go (d + ar) t)

openi :: Int -> Int -> Term -> Term
openi i x = varChanger bnd (\_ n -> V (Free n))
  where
    bnd d j
      | j < d + i = V (Bound j)
      | j == d + i = V (Free x)
      | otherwise = error $ "open: bound fuera de rango: " ++ show j

open :: Int -> Term -> Term
open = openi 0

openType :: Int -> Type -> Type
openType x = Type . open x . unType

openSort :: Int -> Sort -> Sort
openSort i s = s

open2 :: Int -> Int -> Term -> Term
open2 f x = openMany [f, x]

open2Type :: Int -> Int -> Type -> Type
open2Type f x = Type . open2 f x . unType

openMany :: [Int] -> Term -> Term
openMany is t =
  let len = length is
  in  foldl (flip $ uncurry openi) t (zip [len - j | j <- [1..len]] is)

openManyType :: [Int] -> Type -> Type
openManyType is = Type . openMany is . unType

openManyTerms :: [Int] -> [Term] -> [Term]
openManyTerms is ts
  | length is /= length ts = error "openManyTerms"
  | otherwise = zipWith openMany (inits is) ts

openManyTypes :: [Int] -> [Type] -> [Type]
openManyTypes is = map Type . openManyTerms is . map unType

closei :: Int -> Int -> Term -> Term
closei i x = varChanger (\_ j -> V (Bound j)) lcl
  where
    lcl d n
      | n == x = V (Bound (d + i))
      | otherwise = V (Free n)

close :: Int -> Term -> Term
close = closei 0

closeType :: Int -> Type -> Type
closeType x = Type . close x . unType

closeSort :: Int -> Sort -> Sort
closeSort i s = s

close2 :: Int -> Int -> Term -> Term
close2 f x = closeMany [f, x]

close2Type :: Int -> Int -> Type -> Type
close2Type f x = Type . close2 f x . unType

closeMany :: [Int] -> Term -> Term
closeMany is t =
  let len = length is
  in  foldl (flip $ uncurry closei) t (zip [len - j | j <- [1..len]] is)

closeManyType :: [Int] -> Type -> Type
closeManyType is = Type . closeMany is . unType

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

substFree :: Int -> Term -> Term -> Term
substFree x t = varChanger (\_ i -> V (Bound i)) lcl
  where
    lcl _ i
      | i == x = t
      | otherwise = V (Free i)