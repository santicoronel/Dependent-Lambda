{-# LANGUAGE FlexibleInstances #-}

module Main where

import Lang
import Parse
import Elab hiding ( global, local )
import MonadTypeCheck
import TypeCheck
import Context
import Error
import Termination
import Reduce ( reduce, reduceType )
import Datatype
import Resugar
import PPrint

import Options.Applicative
    ( argument, fullDesc, idm, info, str, execParser )
import Control.Exception ( IOException, catch )
import System.IO ( stderr, hPutStrLn)
import Data.Char (isSpace)
import Text.Parsec ( ParseError )
import Control.Monad.Except
import Control.Monad.State


type RunTypeCheck = ExceptT TypeError (StateT Context IO)

instance MonadElab (ExceptT ElabError (State ElabContext))

instance MonadTypeCheck RunTypeCheck

-- NICETOHAVE cargar muchos archivos

main :: IO ()
main = execParser (info (argument str idm) fullDesc) >>= go
  where
    go :: FilePath -> IO ()
    go f = do
      mst <- loadFile f
      case mst of
        Nothing  -> return ()
        Just sp -> case runElab sp of
          (Left e, ctx) -> putStr "Error: " >> case e of
            ElabError e -> putStrLn e
            DataError e -> putStrLn e
          (Right p, _) -> runProgram p

onlyDecls :: Program -> [Decl]
onlyDecls [] = []
onlyDecls (PDecl d : p) = d : onlyDecls p
onlyDecls (PData _ : p) = onlyDecls p

initElabContext :: ElabContext
initElabContext = emptyElabContext {
  datatypes = ["Nat"],
  cons = [zeroCons, sucCons]
}

runElab :: SProgram -> (Either ElabError Program, ElabContext)
runElab p = runState (runExceptT (elabProgram p)) initElabContext

getNames :: Context -> [Name]
getNames ctx = 
  let gns = map globalName $ global ctx
      dns = map dataName $ datadefs ctx
      cns = [conName c | d <- datadefs ctx, c <- dataCons d]
  in  gns ++ dns ++ cns

initContext :: Context
initContext = emptyContext { datadefs = [natDef] }

runProgram :: Program -> IO ()
runProgram p = do
  r <- runStateT (runExceptT (mapM_ runDef p)) initContext
  case r of
    (Left e, ctx) -> do
      let emsg = ppTypeError (reverse $ names ctx) (getNames ctx) e
      putStrLn emsg
    (Right (), _) -> putStrLn "Todo OK"
  where
    runDef :: Definition Decl DataDef -> RunTypeCheck ()
    runDef (PDecl d) = runDecl d
    runDef (PData d) = runData d
    runDecl :: Decl -> RunTypeCheck ()
    runDecl d = case terminationCheck (declDef d) of
        TOK -> runTC d
        TE e -> throwError (Other $ ppTerminationError e)
    runTC :: Decl -> RunTypeCheck ()
    runTC d = do
      ty <- infer (declDef d)
      bindGlobal d ty
      ctx <- get
      put emptyContext
        { global = global ctx, datadefs = datadefs ctx }
      -- TODO sacar esto de aca
      when (declName d == "main") $ do
        t <- reduce (declDef d) -- NICETOHAVE no reducir globales
        ctx <- get
        let reserved = getNames ctx
            sd = resugarDecl reserved (Decl (declName d) t) ty
        liftIO $ putStrLn (ppDecl sd)
    runData :: DataDef -> RunTypeCheck ()
    runData d = do
      shouldBeType (dataType d)
      addDataDef d
      checkConsSort d
      checkPositivity d


loadFile :: FilePath -> IO (Maybe SProgram)
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- catch (readFile filename)
          (\e -> do let err = show (e :: IOException)
                    hPutStrLn stderr 
                      ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                    return "")
    -- setLastFile filename
    case parseIO filename program x of
      Left e -> print e >> return Nothing
      Right a -> return (Just a)

parseIO :: String -> P a -> String -> Either ParseError a
parseIO filename p x = runP p x filename