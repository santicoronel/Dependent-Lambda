{-# LANGUAGE FlexibleInstances #-}

module Main where

import Lang
import Parse
import Elab
import MonadTypeCheck
import TypeCheck
import Context
import Error
import Termination

import Options.Applicative
    ( argument, fullDesc, idm, info, str, execParser )
import Control.Exception ( IOException, catch )
import System.IO ( stderr, hPutStrLn)
import Data.Char (isSpace)
import Text.Parsec ( ParseError )
import Control.Monad.Except
import Control.Monad.State


instance MonadElab (ExceptT ElabError (State ElabContext))

instance MonadTypeCheck (ExceptT TypeError (State Context))

main :: IO ()
main = execParser (info (argument str idm) fullDesc) >>= go
  where
    go :: FilePath -> IO ()
    go f = do
      mst <- loadFile f
      case mst of
        Nothing  -> return ()
        Just st -> case runState (runExceptT (elab st)) emptyElabContext of
          (Left e, ctx) -> case e of
            ElabError e -> putStrLn e
          (Right t, _) -> case terminationCheck t of
            TE e _ -> putStrLn $ "termination error: " ++ show e
            TOK -> case runState (runExceptT (inferTerm t)) emptyContext of
              (Left e, ctx) -> print e
              (Right ty, _) -> print ty


loadFile :: FilePath -> IO (Maybe STerm)
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- catch (readFile filename)
          (\e -> do let err = show (e :: IOException)
                    hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                    return "")
    -- setLastFile filename
    case parseIO filename sterm x of
      Left e -> print e >> return Nothing
      Right a -> return (Just a)


-- TODO meter error de IO aca
parseIO :: String -> P a -> String -> Either ParseError a
parseIO filename p x = runP p x filename