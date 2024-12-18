module Unify where

import Lang
import MonadTypeCheck
import Context -- TODO no quiero importar esto siempre (ver abajo)
import Error
import Reduce
import Common

import Control.Monad.State -- medio paja importar esto TODO extender interfaz MonadTypeCheck
import Control.Monad.Except
import Control.Monad ( zipWithM_ )
import Data.Maybe ( fromMaybe )

-- NICETOHAVE hacer unificacion mas piola

-- TODO revisar (y quizas hacer mejor)


unifyTerms :: MonadTypeCheck m => Term -> Term -> m Bool
unifyTerms t u = do
  nft <- reduceNF t
  nfu <- reduceNF u
  liftIO $ print nft >> print nfu >> putStrLn "" 
  go nft nfu
  where
    go t1@(V (Free x)) t2@(V (Free y)) = do
      ctx <- get
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
      _ -> error (show t ++ "  " ++ show u) >> throwError EUnifError


inspectCons :: Term -> Maybe (ConHead, [Term])
inspectCons = go []
  where
    go as (Con ch) = Just (ch, as)
    go as (t :@: u) = go (u : as) t
    go _ _ = Nothing

notUnifiable :: MonadTypeCheck m => Term -> Term -> m Bool
notUnifiable t u = not <$> unifyTerms t u