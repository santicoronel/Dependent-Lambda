module Unify where

import Lang
import MonadTypeCheck
import Context -- TODO no quiero importar esto siempre (ver abajo)
import Error
import Reduce

import Control.Monad.State -- medio paja importar esto TODO extender interfaz MonadTypeCheck
import Control.Monad.Except
import Control.Monad ( zipWithM_ )
import Data.Maybe ( fromMaybe )

unifyTerms :: MonadTypeCheck m => Term -> Term -> m ()
unifyTerms t u = do
  nft <- reduceNF t
  nfu <- reduceNF u
  go nft nfu
  where
-- TODO chequeo primero si son iguales? eso lo podria hacer union
-- TODO cuando falla union??
-- tengo q saber si ya estan en el uf antes de hacerlo? medio choto
    go t1@(V (Local x)) t2@(V (Local y)) = do
      ctx <- get
      unifyVars x y
    go t u = case (inspectCons t, inspectCons u) of
      (Just (ct, at), Just (cu, au)) ->
        if ct == cu
          then if length at == length au
            then zipWithM_ unifyTerms at au
            else error "unifyTerms: type error"
          else throwError ENotUnif
      _ -> return ()


inspectCons :: Term -> Maybe (ConHead, [Term])
inspectCons = go []
  where
    go as (Con ch) = Just (ch, as)
    go as (t :@: u) = go (u : as) t
    go _ _ = Nothing

notUnifiable :: MonadTypeCheck m => Term -> Term -> m ()
notUnifiable t u = do
  ctx <- get
  catchError
    (do unifyTerms t u 
        put (ctx { unif = unif ctx }) 
        throwError EUnifiable)
    (\e -> case e of
      ENotUnif -> do
        put (ctx { unif = unif ctx})
        return ()
      _ -> throwError e)