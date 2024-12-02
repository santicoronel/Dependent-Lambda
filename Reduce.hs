module Reduce (
  reduceNF,
  reduce,
  reduceNFType,
  reduceType,
  substitute
) where

import Lang
import MonadTypeCheck
import Control.Monad ( mapM )

-- MAYBE hacer substitucion, reduccion a forma normal y LISTO

-- TODO ver el caso fix f ... = ... f x ...
-- donde x es una variable (sin definicion)
-- solucion trivial: no reducir cuerpo de funciones recursivas
-- mejor solucion: identificar ese caso
reduceNF :: MonadTypeCheck m => Term -> m Term
reduceNF (V (Local x) xes) = do
  es <- mapM reduceNF xes
  dx <- getLocalDef x
  case dx of
    Nothing -> return (V (Local x) xes)
    Just d -> reduceNF (foldl (:@:) d es)
reduceNF (V (Global x) xes) = do
  dx <- getGlobalDef x
  es <- mapM reduceNF xes
  reduceNF (foldl (:@:) dx es)
reduceNF (Lam arg (Scope t)) = do
  bindArg (argName arg) (argType arg)
  t' <- reduceNF t
  unbind (argName arg)
  return (Lam arg (Scope t'))
reduceNF (t :@: u) = do
  t' <- reduceNF t
  u' <- reduceNF u
  case t' of
    (V (Local x) xes) -> return (V (Local x) (xes ++ [u']))
    (Lam arg (Scope s)) -> do
      bindLocal (argName arg) (argType arg) u'
      s' <- reduceNF s
      unbind (argName arg)
      return s'
    -- TODO hacer bien
    t@(Fix f arg ty s) -> do
      bindRec f ty t arg -- mm eto ta mal
      bindLocal (argName arg) (argType arg) u'
      s' <- reduceNF s
      unbind (argName arg) >> unbind (argName arg) -- lmao
      unbind f
      return s'
    _ -> error "type error en reduce"
reduceNF (Elim t bs) = do
  t' <- reduceNF t
  bs' <- reduceNFBranches
  case t' of
    V _ _ -> return (Elim t' bs')
    Con ch as -> match ch as bs'
reduceNF t@(Fix f arg ty s) = do
  bindRec f ty t arg
  s' <- reduceNF s -- TODO esto no termina
  unbind (argName arg)
  unbind f
  return s'
reduceNF (Pi arg (Scope ty)) = do
  bindArg (argName arg) (argType arg)
  ty' <- reduceNFType ty
  unbind (argName arg)
  return (Pi arg (Scope ty'))
-- TODO pensar bien este caso
-- pierdo info?? no deberia
reduceNF (Ann t ty) = reduceNF t
reduceNF t = return t

reduceNFType :: MonadTypeCheck m => Type -> m Type
reduceNFType (Type t) = Type <$> reduceNF t

-- TODO pensar bien esto
reduce :: MonadTypeCheck m => Term -> m Term
reduce = reduceNF
reduceType :: MonadTypeCheck m => Type -> m Type
reduceType = reduceNFType


-- tengo q sustituir en el entorno
-- TODO pensar mejor esto
substitute :: Name -> Term -> Term -> Term
substitute x tx (V (Local y) yes) 
  -- reduzco aca??
  | x == y = foldl (:@:) tx yes
  | otherwise = _
substitute x tx _ = _