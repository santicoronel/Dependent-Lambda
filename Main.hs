{-# LANGUAGE FlexibleInstances #-}

module Main where

import Lang
import Parse
import Elab hiding ( global )
import MonadTypeCheck
import TypeCheck
import Context
import Error
import Termination
import Reduce ( reduce, reduceType )

import Options.Applicative
    ( argument, fullDesc, idm, info, str, execParser )
import Control.Exception ( IOException, catch )
import System.IO ( stderr, hPutStrLn)
import Data.Char (isSpace)
import Text.Parsec ( ParseError )
import Control.Monad.Except
import Control.Monad.State


instance MonadElab (ExceptT ElabError (State ElabContext))

instance MonadTypeCheck (ExceptT TypeError (StateT Context IO))

main :: IO ()
main = execParser (info (argument str idm) fullDesc) >>= go
  where
    go :: FilePath -> IO ()
    go f = do
      mst <- loadFile f
      case mst of
        Nothing  -> return ()
        Just sp -> case runElab sp of
          (Left e, ctx) -> case e of
            ElabError e -> putStrLn e
          (Right p, _) -> case runTerminationCheck p of
            TE e _ -> putStrLn $ "termination error: " ++ show e
            TOK -> runProgram p


runElab :: SProgram -> (Either ElabError Program, ElabContext)
runElab p = runState (runExceptT (mapM elabDecl p)) emptyElabContext

runTerminationCheck :: Program -> TChecked
runTerminationCheck = foldMap tcheckDecl
  where 
    tcheckDecl d =
      -- terminationCheckType (declType d) <>
      terminationCheck (declDef d)  

runProgram :: Program -> IO ()
runProgram p = do
  r <- runStateT (runExceptT (mapM_ runDecl p)) emptyContext
  case r of
    (Left e, ctx) -> print e -- TODO frees
    (Right (), _) -> putStrLn "Todo OK"
  where
    runDecl :: Decl -> ExceptT TypeError (StateT Context IO) () 
    runDecl d = do
      ty <- infer (declDef d)
      bindGlobal d ty
      when (declName d == "main") $ do
        t <- reduce (declDef d)
        liftIO $ do
          putStrLn "main := "
          print t
          putStrLn ":"
          print ty

{-
runTerm :: Term -> IO ()
runTerm t =
  let rt = do
      ty <- infer t
      ty' <- reduceType ty
      t' <- reduce t
      return (t', ty')
  in case runState (runExceptT rt) emptyContext of
      (Left e, ctx) -> print e -- TODO aca hay variables free
      (Right (t', ty), _) -> do
        putStrLn "Termino:"
        print t'
        putStrLn "Tipo:"
        print ty
-}

loadFile :: FilePath -> IO (Maybe SProgram)
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- catch (readFile filename)
          (\e -> do let err = show (e :: IOException)
                    hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                    return "")
    -- setLastFile filename
    case parseIO filename program x of
      Left e -> print e >> return Nothing
      Right a -> return (Just a)

parseIO :: String -> P a -> String -> Either ParseError a
parseIO filename p x = runP p x filename