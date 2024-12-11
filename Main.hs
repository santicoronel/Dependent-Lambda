module Main where

import Lang
import Parse
import Elab
import MonadTypeCheck
import TypeCheck
import Reduce

import Options.Applicative
    ( argument, fullDesc, idm, info, str, execParser )
import Control.Exception ( IOException, catch )
import System.IO ( stderr, hPutStrLn)
import Data.Char (isSpace)
import Text.Parsec ( ParseError )

main :: IO ()
main = execParser (info (argument str idm) fullDesc) >>= go
  where
    go :: FilePath -> IO ()
    go f = do
      t <- loadFile f
      --let t' = ... elab t
      --let ty = ... infer t'
      -- print ty
      return ()


loadFile :: FilePath -> IO STerm
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- catch (readFile filename)
          (\e -> do let err = show (e :: IOException)
                    hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                    return "")
    -- setLastFile filename
    case parseIO filename expr x of
      Left e -> undefined
      Right p -> return p


-- TODO meter error de IO aca
parseIO ::String -> P a -> String -> Either ParseError a
parseIO filename p x = runP p x filename
