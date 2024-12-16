module Common where


import Control.Monad.State
import Control.Monad.Except
import Data.List (group)

--------------------- Utiles -------------------------------------
duplicateName :: Eq a => [a] -> Bool
duplicateName xs = not $ all unary $ group xs
  where unary [_] = True
        unary _ = False

lookupWith :: Eq i => i -> [a] -> (a -> i) -> (a -> b) -> Maybe b
lookupWith _ [] _ _ = Nothing
lookupWith x (b : bs) gn gt
  | x == gn b = Just (gt b)
  | otherwise = lookupWith x bs gn gt

updateWith :: Eq i => (a -> i) -> (a -> a) -> i -> [a] -> Maybe [a]
updateWith _ _ _ [] = Nothing
updateWith gn up x (y:ys)
  | gn y == x = Just (up y : ys)
  | otherwise = (y :) <$> updateWith gn up x ys

deleteWith :: Eq i => (a -> i) -> i -> [a] -> Maybe [a]
deleteWith gn _ [] = Nothing
deleteWith gn x (b : bs)
  | x == gn b = Just bs
  | otherwise = (b :) <$> deleteWith gn x bs

------------- MonadState -----------------------------------------
doAndRestore :: MonadState s m => m a -> m a
doAndRestore m = do
  s <- get
  x <- m
  put s
  return x

--------------------- MonadError ---------------------------------
retry :: MonadError e m => m a -> m a -> m a
retry a b = a `catchError` const b

retryWithError :: MonadError e m => m a -> m a -> e -> m a
retryWithError a b e = retry a b `catchError` const (throwError e)