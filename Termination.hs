{-# LANGUAGE FlexibleContexts #-}

module Termination (
  TError( TError),
  TChecked( TE, TOK ),
  terminationCheck,
  terminationCheckType
)where

import Lang
import qualified Transitive as TR

import Control.Monad.State
import Control.Monad.Except
import Common
import Substitution

-- NICETOHAVE permitir recursion mutua (foetus)

-- TODO mejor error
newtype TError = TError Term deriving Show

data TChecked = TE TError [Name] | TOK

instance Semigroup TChecked where
  TOK <> TOK = TOK
  TE te ns <> _ = TE te ns
  _ <> TE te ns  = TE te ns

instance Monoid TChecked where
  mempty = TOK

terminationCheck :: Term -> TChecked
terminationCheck t = case runState (runExceptT (check t)) emptyContext of
  (Left e, ctx) -> TE e (ns ctx)
  (Right (), _) -> TOK

terminationCheckType :: Type -> TChecked
terminationCheckType (Type t) = terminationCheck t

type VarId = Int

data TContext = TC {
  vc :: VarId,
  ns :: [Name],
  rb :: [(VarId, VarId)],
  lt :: TR.Transitive VarId
}

emptyContext :: TContext
emptyContext = TC 0 [] [] TR.empty 


addVar :: MonadState TContext m => Name -> m VarId
addVar x = do
  ctx <- get
  let ix = vc ctx
  put ctx { ns = x : ns ctx, vc = vc ctx + 1 }
  return ix

addRel :: MonadState TContext m => VarId -> VarId -> m ()
addRel x y = do
  ctx <- get
  let lt' = TR.addRel (lt ctx) x y
  put ctx { lt = lt' } 

recVar :: MonadState TContext m => VarId -> m (Maybe VarId)
recVar f = do
  ctx <- get
  return $ lookup f (rb ctx)

lessThan :: MonadState TContext m => VarId -> VarId -> m Bool
lessThan x y = do
  ctx <- get
  return (TR.rel (lt ctx) x y)

addFixOp :: MonadState TContext m => Name -> Name -> m (VarId, VarId)
addFixOp r x = do
  ir <- addVar r
  ix <- addVar x
  ctx <- get
  let rbinders = rb ctx
  put ctx { rb = (ir, ix) : rbinders }
  return (ir, ix)

type CheckedTerm = ExceptT TError (State TContext) ()

check :: Term -> CheckedTerm
check (V (Bound i)) = error $ "Termination check: bound " ++ show i 
check (V (Free f) :@: u) = do
  rf <- recVar f
  case rf of
    Nothing -> check u
    Just x -> checkSub u x
check t@(V (Free x)) = do
  rf <- recVar x
  case rf of
    Nothing -> return ()
    Just _ -> throwError (TError t)
check (Lam arg t) = doAndRestore (do
  checkType (argType arg)
  x <- addVar (argName arg)
  check (open x t)
  )
check (t :@: u) = check t >> check u
check (Elim (V (Free x)) bs) = mapM_ (checkBranchWith x) bs
check (Elim t bs) = mapM_ checkBranch bs
check (Fix f arg _ t) = doAndRestore (do
  (fi, xi) <- addFixOp f (argName arg)
  check (open2 fi xi t)
  )
check (Pi arg ty) = do
  doAndRestore (checkType (argType arg))
  doAndRestore (do
    i <- addVar (argName arg)
    checkType (openType i ty)
    )
check (Ann t ty) = do
  check t
  checkType ty
check _ = return ()

checkSub :: Term -> VarId -> CheckedTerm
checkSub t@(V (Free x)) y = do
  x_lt_y <- x `lessThan` y
  unless x_lt_y (throwError (TError t))
checkSub t _ = throwError (TError t)

checkBranchWith :: VarId -> ElimBranch -> CheckedTerm
checkBranchWith x b = doAndRestore (do
  is <- mapM addVar (elimConArgs b)
  mapM_ (`addRel` x) is
  check (openMany is (elimRes b))
  )

checkBranch :: ElimBranch -> CheckedTerm
checkBranch b = check (elimRes b)


checkType :: Type -> CheckedTerm
checkType = check . unType