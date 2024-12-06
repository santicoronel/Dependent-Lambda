{-# LANGUAGE FlexibleContexts #-}

module Termination where

import Lang
import qualified PartialOrder as PO

import Control.Monad.State
import Control.Monad.Writer
import MonadTypeCheck ( doAndRestore )

data TChecked = TOK | TE Term -- algo mas?

instance Semigroup TChecked where
  TOK <> TOK = TOK
  TE t <> _ = TE t
  TOK <> TE t = TE t 

instance Monoid TChecked where
  mempty = TOK


terminationCheck :: Term -> TChecked
terminationCheck t = execWriter $ evalStateT (check t) emptyContext



addVar :: MonadState TContext m => Name -> m ()
addVar x = do
  ctx <- get
  let (ix, lt') = PO.addVar (lt ctx)
  put ctx { mp = (x, ix) : mp ctx, lt = lt' }

recVar :: MonadState TContext m => Name -> m ()
recVar _ = _


data TContext = TC {
  mp :: [(Name, Int)],
  rb :: [(Int, Int)],
  lt :: PO.PO
  }

emptyContext :: TContext
emptyContext = TC [] [] PO.empty 

check :: Term -> StateT TContext (Writer TChecked) ()
check (V (Local f) :@: u) = do
  rf <- recVar f
  case rf of
    Nothing -> check u
    Just x -> checkSub u x
check (Lam arg (Scope t)) = doAndRestore (do
  checkType (argType arg)
  addVar (argName arg)
  check t
  )
check (Elim (V (Local x)) bs) = mapM_ (checkBranchWith x) bs
check (Elim t bs) = mapM_ checkBranch bs
check (Fix f arg _ t) = doAndRestore (do
  addFixOp f (argName arg)
  check t
  )
check (Pi arg (Scope ty)) = doAndRestore (do
  checkType (argType arg)
  addVar (argName arg)
  checkType ty
  )
check (Ann t ty) = do
  check t
  checkType ty

checkType :: Type -> StateT TContext (Writer TChecked) ()
checkType = check . unType