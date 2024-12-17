module Datatype where

import Lang
import Common


import Control.Monad.Except


-- MAYBE parsear solo definiciones validas
-- Tendria q pensar que quiero parsear exactamente

data DataError = DError String

checkData :: DataDecl -> Either DataError DataDef
checkData (DataDecl n ty cs) = do
  (s, ar) <- checkDataType ty
  when (duplicateName (map consDeclName cs))
    (throwError $ DError $ "nombre de constructor: " ++ n ++ " duplicado") 
  cs <- mapM (checkDataCons n ar) cs
  return (DataDef n [] ty s ar cs)

checkDataType :: Type -> Either DataError (Sort, Int)
checkDataType = go . unType
  where
    go (Sort s) = return (s, 0)
    go (Pi arg ty) = (\(s, ar) -> (s, ar + 1)) <$> checkDataType ty
    go t = Left (DError $ show t ++ " inesperado en dataype def")

checkDataCons :: Name -> Int -> ConsDecl -> Either DataError Constructor
checkDataCons d ar (ConsDecl n ty) = do
  car <- checkConsType d ar ty
  return (Constructor n ty car)


-- TODO positivity check
checkConsType :: Name -> Int -> Type -> Either DataError Int
checkConsType d ar = go . unType
  where
    go :: Term -> Either DataError Int
    go (Pi arg ty) = (1 + ) <$> go (unType ty)
    go t = checkReturn 0 t >> return 0

    checkReturn n (Data (DataT e))
      | d == e = if n == ar 
        then return ()
        else Left (DError $ "datatype " ++ d ++ " aplicado parcialmente")
      | otherwise = Left (DError $ "datatype " ++ e ++ " en tipo de retorno")
    checkReturn n (t :@: u) = checkReturn (n + 1) t 