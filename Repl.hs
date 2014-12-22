{-# LANGUAGE RankNTypes, KindSignatures, BangPatterns #-}

module Repl where

import Language.LambdaBase.Core
import Language.LambdaBase.Eval
import Language.LambdaBase.Parser

import Core

import qualified Control.Exception as CE
import qualified Control.Exception.Base as CEB

import Control.Monad.Trans (liftIO)

import System.Console.Haskeline
import System.Console.Haskeline.MonadException

toContext string =
    case parseExpr code of
        Left _   -> []
        Right ex -> [ ( Name name Naked (fixityOf name) , (setFix ex (fixityOf name)) ) ]
  where (name,'\n':code) = span (/='\n') string

getMultipleInput :: forall (m :: * -> *).  MonadException m => String -> InputT m [Char]
getMultipleInput sim = do
    minput <- getInputLine sim
    case minput of
        Nothing -> return ""
        Just "" -> return ""
        Just a  -> do
            l <- getMultipleInput "| "
            return $ a ++ "\n" ++ l

repl :: IO ()
repl = do
    runInputT defaultSettings (loop [])
  where
    tryCode code context = CE.catch (parseAndRun code context) tryPrintE
    tryPrintE :: CEB.SomeException -> IO ()
    tryPrintE e = CE.catch (print e) tryPrintE
    loop :: Context -> InputT IO ()
    loop context = do
        code <- getMultipleInput "> "
        case code of
            --bind things to context
            ':' : 'q' : x                    -> return ()
            ':' : 'b' : '\n' : x             -> loop ( context ++ (toContext x) )
            ':' : 'l':'o':'a':'d' : '\n' : x -> do
                let (name,'\n':fileNameN) = span (/='\n') x
                let fileName = init fileNameN
                fileCode <- liftIO $ readFile fileName
                case parseExpr fileCode of
                    Left  e -> loop context
                    Right e -> loop ( ( Name name Naked (fixityOf name) , setFix e (fixityOf name) ) : context)
            x                                -> do
                outputStrLn "\nResult :"
                liftIO $ tryCode code context
                liftIO $ putStrLn ""
                loop context

startRepl :: IO ()
startRepl = do
    putStrLn "Repl mode"
    repl

parseAndRun :: String -> Context -> IO ()
parseAndRun code context = do
    case parseExpr code of
        Left e  -> putStrLn (show e)
        Right r -> runEval ((foldl (\r (from,to) -> substituteInExpr r from to) r context)::Expr Lits) >> (return ())

runEval :: Expr Lits -> IO Lits
runEval e = do
    case eval e of
        Lit x _ -> case x of
            LitIO a -> a
            l       -> (putStrLn $ show l) >> (return LitNil)
        y     -> (putStrLn $ show y) >> (return LitNil)
