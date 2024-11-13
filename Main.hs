module Main where

main :: IO ()
main = return ()

{-
prompt :: IO String
prompt = do putStr "> "
            hFlush stdout
            getLine

main :: IO ()
main = do line <- prompt
          let r = runpCmd line
          case r of
            Left e -> do  putStrLn $ "error de parseo: " ++ e
                          main
            Right cmd -> handleCmd cmd main

handleCmd :: Cmd -> IO() -> IO ()
handleCmd Quit next = return ()
handleCmd (Go action) next = handleAction action >> next

handleAction :: Action -> IO ()
handleAction (Action Reduce (Left t)) = print $ reduceLam $ elabLam t
handleAction (Action Reduce (Right t)) = print (reduceSKI t)
handleAction (Action Eval (Left t)) = print (reduceSKI $ evalLam $ elabLam t)
handleAction (Action Eval (Right t)) = print (reduceLam $ evalSKI t)
handleAction (Action Test (Left nt)) =  let t = elabLam nt
                                            s = reduceLam $ evalSKI $ evalLam t
                                            t' = reduceLam t
                                        in test s t'
handleAction (Action Test (Right s)) =  let t = reduceSKI $ evalLam $ evalSKI s
                                            s' = reduceSKI s
                                        in test t s'

test :: (Show a, Eq a) => a -> a -> IO ()
test x y = if x == y then ok else notok
  where ok = putStrLn "OK" >> print x
        notok = do  putStrLn "FAIL"
                    putStrLn "----------------------"
                    print x
                    putStrLn "----------------------"
                    print y

-}