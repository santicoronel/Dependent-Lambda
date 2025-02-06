module Unify where

import Lang
import MonadTypeCheck
import Error
import Reduce

import Control.Monad.State
import Control.Monad.Except


unifyTerms :: MonadTypeCheck m => Term -> Term -> m Bool
unifyTerms t u = do
  nft <- reduceNF t
  nfu <- reduceNF u
  go nft nfu
  where
    go (V (Free x)) (V (Free y)) = do
      unifyVars x y
      return True
    go (V (Free x)) t =
      if x `freeIn` t
        then return False
        else bindPattern x t >> return True
    go t (V (Free x)) =
      if x `freeIn` t
        then return False
        else bindPattern x t >> return True
    go t u = case (inspectCons t, inspectCons u) of
      (Just (ct, at), Just (cu, au)) ->
        if ct == cu
          then if length at == length au
            then and <$> zipWithM unifyTerms at au
            else error "unifyTerms: type error"
          else return False
      _ -> throwError (EUnifError t u)


inspectCons :: Term -> Maybe (ConHead, [Term])
inspectCons = go []
  where
    go as (Con ch) = Just (ch, as)
    go as (t :@: u) = go (u : as) t
    go _ _ = Nothing

notUnifiable :: MonadTypeCheck m => Term -> Term -> m Bool
notUnifiable t u = not <$> unifyTerms t u