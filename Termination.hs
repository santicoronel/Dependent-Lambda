{-# LANGUAGE FlexibleContexts #-}

module Termination ( terminationCheck ) where

import Lang
import qualified PartialOrder as PO

import Control.Monad.State
import Control.Monad.Except
import MonadTypeCheck ( doAndRestore )

-- TODO hacer bien
newtype TError = TError Term

data TChecked = TE TError | TOK

terminationCheck :: Term -> TChecked
terminationCheck t = case evalStateT (check t) emptyContext of
  Left e -> TE e
  Right () -> TOK

type VarId = Int

data TContext = TC {
  mp :: [(Name, VarId)],
  rb :: [(VarId, VarId)],
  lt :: PO.PO
}

emptyContext :: TContext
emptyContext = TC [] [] PO.empty 


addVar :: MonadState TContext m => Name -> m VarId
addVar x = do
  ctx <- get
  let (ix, lt') = PO.newVar (lt ctx)
  put ctx { mp = (x, ix) : mp ctx, lt = lt' }
  return ix

addRel :: MonadState TContext m => Name -> Name -> m ()
addRel x y = do
  ix <- addVar x
  ctx <- get
  case lookup y (mp ctx) of
    Nothing -> error "Termination: addRel"
    Just iy ->
      let lt' = PO.addRel (lt ctx) ix iy
      in  put ctx { lt = lt' } 

recVar :: MonadState TContext m => Name -> m (Maybe VarId)
recVar f = do
  ctx <- get
  return $ case lookup f (mp ctx) of
    Nothing -> error "Termination: recVar"
    Just i -> lookup i (rb ctx)

lessThan :: MonadState TContext m => Name -> VarId -> m Bool
lessThan x i = do
  ctx <- get
  case lookup x (mp ctx) of
    Nothing -> error "Termination: lessThan"
    Just ix -> return (PO.rel (lt ctx) ix i)

addFixOp :: MonadState TContext m => Name -> Name -> m ()
addFixOp r x = do
  ir <- addVar r
  ix <- addVar x
  ctx <- get
  let rbinders = rb ctx
  put ctx { rb = (ir, ix) : rbinders}

type CheckedTerm = StateT TContext (Either TError) ()

check :: Term -> CheckedTerm
check (V (Local f) :@: u) = do
  rf <- recVar f
  case rf of
    Nothing -> check u
    Just ix -> checkSub u ix
check t@(V (Local x)) = do
  rf <- recVar x
  case rf of
    Nothing -> return ()
    Just _ -> throwError (TError t) 
check (Lam arg (Scope t)) = doAndRestore (do
  checkType (argType arg)
  addVar (argName arg)
  check t
  )
check (t :@: u) = check t >> check u
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
check _ = return ()

checkSub :: Term -> VarId -> CheckedTerm
checkSub t@(V (Local y)) ix = do
  y_lt_x <- y `lessThan` ix
  unless y_lt_x (throwError (TError t))
checkSub t _ = throwError (TError t)

checkBranchWith :: Name -> ElimBranch -> CheckedTerm
checkBranchWith x b = doAndRestore (do
  mapM_ (`addRel` x) (elimConArgs b)
  check (elimRes b) 
  )

checkBranch :: ElimBranch -> CheckedTerm
checkBranch b = check (elimRes b)


checkType :: Type -> CheckedTerm
checkType = check . unType