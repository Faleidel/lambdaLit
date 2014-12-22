{-# LANGUAGE RankNTypes, KindSignatures, BangPatterns #-}

module Core where

import Language.LambdaBase.Core
import Language.LambdaBase.Eval
import Language.LambdaBase.Parser

import Data.List
import qualified Text.Read as TR

import Network.Socket hiding (send, sendTo, recv, recvFrom)
import Network.Socket.ByteString (send, recv)
import qualified Data.ByteString.Char8 as B8

netPrint :: String -> Int -> String -> IO ()
netPrint host port msg = withSocketsDo $ do
    addrInfo <- getAddrInfo Nothing (Just host) (Just $ show port)
    let serverAddr = head addrInfo
    sock <- socket (addrFamily serverAddr) Stream defaultProtocol
    connect sock (addrAddress serverAddr)
    msgSender msg sock
    sClose sock

netGetLine :: String -> Int -> IO String
netGetLine host port = withSocketsDo $ do
    addrInfo <- getAddrInfo Nothing (Just host) (Just $ show port)
    let serverAddr = head addrInfo
    sock <- socket (addrFamily serverAddr) Stream defaultProtocol
    connect sock (addrAddress serverAddr)
    m <- recv sock 100000
    sClose sock
    return $ B8.unpack m
 
msgSender :: String -> Socket -> IO ()
msgSender m sock = do
  let msg = B8.pack m
  send sock $ msg
  return ()

type Context = [(Expr Lits , Expr Lits)]

na :: String -> Expr a
na x = Name x Naked Prefix

appOp :: Expr a
appOp = Name "<->" Naked Infix

ex :: [Expr a] -> Expr a
ex l = Expr l Prefix

la :: String -> EVS -> Expr a -> Expr a
la n s e = Lambda (Arg n s) e Prefix

li :: a -> Expr a
li a = Lit a Prefix

data Lits =
    LitInt !Int
  | LitFloat !Float
  | LitString !String
  | LitList ![Lits]
  | LitMKList
  | LitAppend
  | LitCons
  | LitSplit
  | LitSplitF
  | LitAdd
  | LitMult
  | LitSub
  | LitPrint
  | LitNil
  | LitIf
  | LitExpr !(Expr Lits)
  | LitBool !Bool
  | LitEq
  | LitConcatO
  | LitFoldO
  | LitToLit
  | LitNetPrint
  | LitNetGetLine
  | LitPF !Lits ![Lits]
  | LitIO !(IO Lits)
  | LitLiftToIO
  | LitEval
  | LitReadFile
  | LitWriteFile

instance Eq Lits where
    LitNil == LitNil = True
    x == y = False

instance Show Lits where
    show (LitInt x)     = show x
    show (LitFloat x)   = show x
    show (LitList x)    = show x
    show LitMKList      = "single"
    show LitReadFile    = "readFile"
    show LitWriteFile   = "writeFile"
    show LitAppend      = "++"
    show LitNetPrint    = "netPrint"
    show LitNetGetLine  = "netGetLine"
    show LitCons        = ":"
    show (LitString x)  = "\"" ++ x ++ "\""
    show LitConcatO     = "concatO"
    show LitFoldO       = "foldO"
    show LitAdd         = "add"
    show LitSplit       = "split"
    show LitSplitF      = "splitF"
    show LitSub         = "sub"
    show LitMult        = "mult"
    show LitToLit       = "toLit"
    show (LitBool b)    = show b
    show LitEq          = "eq"
    show LitPrint       = "print"
    show LitEval        = "eval"
    show LitNil         = "nil"
    show LitIf          = "if"
    show LitLiftToIO    = "=>"
    show (LitExpr e)    = show e
    show (LitPF x y)    = (show x) ++ " " ++ ( concat . intersperse " " . reverse . map (show) $ y )
    show (LitIO a)      = "(IO Literal)"
    show _              = "can't show!?"

failPF l y argsLength | length l >= argsLength - 1 = True
                      | True = False

isFunction LitAdd        = True
isFunction LitEval       = True
isFunction LitSub        = True
isFunction LitReadFile   = True
isFunction LitWriteFile  = True
isFunction LitMult       = True
isFunction LitEq         = True
isFunction LitConcatO    = True
isFunction LitFoldO      = True
isFunction LitPrint      = True
isFunction LitIf         = True
isFunction LitToLit      = True
isFunction LitNetPrint   = True
isFunction LitNetGetLine = True
isFunction (LitPF x y)   = True
isFunction (LitIO x)     = True
isFunction (LitExpr x)   = True
isFunction LitLiftToIO   = True
isFunction LitSplit      = True
isFunction LitSplitF     = True
isFunction LitAppend     = True
isFunction LitCons       = True
isFunction LitMKList     = True
isFunction _             = False

litFromExpr (Lit e _) = e
litFromExpr e         = LitExpr e

toNiceString (LitString x) = x
toNiceString x             = show x

iOHelper (LitIO x) f = LitIO $ x >>= (\i -> f i)
iOHelper x         f = LitIO $ f x

tryUnpackLit (Lit (LitExpr x) _) = x
tryUnpackLit x                   = x

instance Lit Lits where
    -- if
    apply !(LitPF LitIf (x:(LitBool c):[])) !y = tryUnpackLit $ Lit ( if c then x else y ) Prefix
    apply !lpf@(LitPF LitIf l) !y | failPF l y 3 = error $ "Error with IF :" ++ (show lpf) ++ " " ++ (show y)
    
    -- add
    apply !(LitPF LitAdd [LitInt !x]) !(LitInt !y) = Lit ( LitInt (x+y) ) Prefix
    apply (LitPF LitAdd [LitString x]) (LitString y) = Lit ( LitString (x++y) ) Prefix
    apply !lpf@(LitPF LitAdd l) !y | failPF l y 2 = error $ "Error with ADD :" ++ (show lpf) ++ " " ++ (show y)
    
    -- sub
    apply !(LitPF LitSub [LitInt x]) !(LitInt y) = Lit ( LitInt (x-y) ) Prefix
    apply !lpf@(LitPF LitSub l) !y | failPF l y 2 = error $ "Error with SUB :" ++ (show lpf) ++ " " ++ (show y)
    
    -- eq
    apply !(LitPF LitEq [LitBool x]) !(LitBool y) = Lit ( LitBool (x==y) ) Prefix
    apply !(LitPF LitEq [LitString x]) !(LitString y) = Lit ( LitBool (x==y) ) Prefix
    apply !(LitPF LitEq [LitInt x]) !(LitInt y) = Lit ( LitBool (x==y) ) Prefix
    apply !lpf@(LitPF LitEq l) !y | failPF l y 2 = error $ "Error with EQ :" ++ (show lpf) ++ " " ++ (show y)
    
    -- mult
    apply !(LitPF LitMult [LitInt x]) !(LitInt y) = Lit ( LitInt (x*y) ) Prefix
    apply !lpf@(LitPF LitMult l) !y | failPF l y 2 = error $ "Error with MULT :" ++ (show lpf) ++ " " ++ (show y)
    
    -- =>
    -- I have a problème here.
    -- I am not tail recursive.
    {-
       Here I :
       
       return a Lit
           This is not a problème alone but if I do Lit eval Lit eval ... there will be a stack overflow
       Inside the Lit I return a LitIO
           This to should not be a problème.
       Then I unwrap x and apply it to l1
           This is so getLine => print do :
               getLine give x take x and do print x to return IO ()
       
       Lit $ LitIO $ x >>= (eval . (apply y))
       This is what I realy want :
           x >>= (eval . apply y) :: IO Expr Lits
	       But I don't know if it is tail recursive
	       And maybe there is a way to swap IO and Expr ( NOP!? )
	       So I could have Expr IO Lits but this is stil not what I want.
	       I want Expr LitIO io
       
       Ok so, how do I do monadic tail recursive fonction anyway?
       printr = do
           print 1
           printr
       
       This should work. But how?
       
       printr = print 1 >> printr
       
       Maybe Haskell just know how to do this case...
       
       OK, the solution to tail recursive monadic functions is itterators (lazy).
       
       Expr ( Lit a : Lit b : xs )
                  apply a b = newExpr
       Expr ( newExpr : xs )
       
       inside apply a b ->
       apply (a (l)) b ->
           apply l b = newExpr
           eval newExpr since it can be an reducible Expr
           a (newExpr)
       
       (Lit (a (newExpr))) : xs
       
       I need to see the eval/apply paire as an iterator.
       My itterator will need to work on a list and consume the list.
       
    -}
    apply !(LitPF LitLiftToIO [LitIO x]) !y = Lit ( LitIO $ (x >>= (\l1 ->
         case litFromExpr . eval $ apply y l1 of
             LitIO x -> x
             x       -> return x
      )) ) Prefix
    apply !lpf@(LitPF LitLiftToIO l) !y | failPF l y 2 = error $ "Error with (=>) :" ++ (show lpf) ++ " ====================================== \n" ++ (show y)
    
    -- toLit
    apply !LitToLit !(LitString x) = Lit ( toLit (Name x Naked Prefix) ) Prefix
    apply !LitToLit !y = error $ "Error with : toLit on :" ++ (show y)
    
    -- split
    apply !LitSplit !(LitString []) = la "<->" Strict $ ex (     [li $ LitString []]                                         )
    apply !LitSplit !(LitString !x) = la "<->" Strict $ ex (     intersperse appOp . map (\c -> li $ LitString [c] ) $ x     )
    apply !LitSplit !(LitList [])   = la "<->" Strict $ ex (     [li $ LitList []]                                           )
    apply !LitSplit !(LitList !x)   = la "<->" Strict $ ex (     intersperse appOp . map (\c -> li c ) $ x                   )
    apply !LitSplit !y = error $ "Error with : split on :" ++ (show y)
    
    -- splitF
    apply !LitSplitF !(LitString []) = la "<->" Strict $ ex ( [li $ LitString []] )
    apply !LitSplitF !(LitString !x) = la "<->" Strict $ ex (    [li (LitString "") , appOp]
                                                                ++ (intersperse appOp . map (\c -> li $ LitString [c] ) $ x))
    apply !LitSplitF !(LitList [])   = la "<->" Strict $ ex ( [li $ LitList[]] )
    apply !LitSplitF !(LitList !x)   = la "<->" Strict $ ex (    [li $ LitList [] , appOp ]
                                                                ++ (intersperse appOp . map (\c -> Lit c Prefix ) $ x))
    apply !LitSplitF !y = error $ "Error with : split on :" ++ (show y)
    
    -- print
    apply !LitPrint !x = Lit ( iOHelper x (\x -> ( putStrLn . toNiceString $ x ) >> return LitNil) ) Prefix
    
    -- readfile
    apply !LitReadFile !(LitString !x) = Lit ( LitIO ( readFile x >>= (return . LitString) ) ) Prefix
    
    -- writeFile
    apply !(LitPF !LitWriteFile ![LitString !file]) !(LitString !content) = Lit ( LitIO ( writeFile file content >> (return LitNil) ) ) Prefix
    
    -- eval
    apply !LitEval (LitString !x) = case parseExpr x of
        Left e  -> error $ "Can't parse : " ++ x
        Right c -> c
    
    -- netPrint
    apply !(LitPF LitNetPrint ![LitInt port, LitString ip]) !x = Lit ( iOHelper x (\x -> netPrint ip port (toNiceString x) >> return LitNil ) ) Prefix
    
    -- netGetLine
    apply !(LitPF !LitNetGetLine ![LitString !ip]) (LitInt !port) = Lit ( LitIO $ netGetLine ip port >>= (return . LitString) ) Prefix
    
    -- io io
    apply !(LitIO !a) !(LitIO !b) = Lit ( LitIO $ do {a;b} ) Prefix
    
    -- single
    apply !LitMKList !x = Lit ( LitList [x] ) Prefix
    
    -- ++
    apply !(LitPF LitAppend ![LitList x]) !(LitList y) = Lit ( LitList (x++y) ) Prefix
    apply !lpf@(LitPF LitAppend l) !y | failPF l y 2 = error $ "Error with (++) :" ++ (show lpf) ++ " " ++ (show y)
    
    -- :
    apply !(LitPF LitCons [x]) !(LitList y) = Lit ( LitList (x:y) ) Prefix
    apply !lpf@(LitPF LitCons l) !y | failPF l y 2 = error $ "Error with (:) :" ++ (show lpf) ++ " " ++ (show y)
    
    -- concatO
    apply !(LitPF LitConcatO x) !LitNil = Lambda (Arg "<->" Strict) ( tree . map (flip Lit Prefix) $ x ) Prefix
      where
        tree x = Expr (intersperse (Name "<->" Naked Infix) x) Prefix
    
    -- foldO
    apply !(LitPF LitFoldO x) !LitNil = Lambda (Arg  "<->" Strict) ( Lambda (Arg "ni" Strict) ( tree . map (flip Lit Prefix) $ x ) Prefix ) Prefix
      where
        tree x = Expr ( (Name "ni" Naked Prefix) : (Name "<->" Naked Infix) : (intersperse (Name "<->" Naked Infix) x) ) Prefix
    
    -- LitExpr
    apply !(LitExpr e) !y = Expr [e , Lit y Prefix] Prefix
    
    -- not a function error
    apply !f !y | isFunction f == False = error $ "Sorry," ++ (show f) ++ " is not a function and can't be applyed on " ++ (show y)
    
    -- partial function
    apply !(LitPF x l) !y = Lit ( LitPF x (y:l) ) Prefix
    apply !a !y = Lit ( LitPF a [y] ) Prefix
    
    fromExpr e = LitExpr e
    
    toLit (Name "if" _ _)                  = LitIf
    toLit (Name "eval" _ _)                = LitEval
    toLit (Name "single" _ _)              = LitMKList
    toLit (Name "emptyList" _ _)           = LitList []
    toLit (Name "++" _ _)                  = LitAppend
    toLit (Name ":" _ _)                   = LitCons
    toLit (Name "split" _ _)               = LitSplit
    toLit (Name "splitF" _ _)              = LitSplitF
    toLit (Name "=>" _ _)                  = LitLiftToIO
    toLit (Name "toLit" _ _)               = LitToLit
    toLit (Name "True" _ _)                = LitBool True
    toLit (Name "False" _ _)               = LitBool False
    toLit (Name "add" _ _)                 = LitAdd
    toLit (Name "+" _ _)                   = LitAdd
    toLit (Name "%" _ _)                   = LitInt 100
    toLit (Name "sub" _ _)                 = LitSub
    toLit (Name "readFile" _ _)            = LitReadFile
    toLit (Name "writeFile" _ _)           = LitWriteFile
    toLit (Name "mult" _ _)                = LitMult
    toLit (Name "print" _ _)               = LitPrint
    toLit (Name "netPrint" _ _)            = LitNetPrint
    toLit (Name "netGetLine" _ _)          = LitNetGetLine
    toLit (Name "getLine" _ _)             = LitIO ( getLine >>= ( return . LitString ) )
    toLit (Name "emptyIO" _ _)             = LitIO ( return LitNil )
    toLit (Name "nil" _ _)                 = LitNil
    toLit (Name "concatO" _ _)             = LitConcatO
    toLit (Name "foldO" _ _)               = LitFoldO
    toLit (Name "eq" _ _)                  = LitEq
    toLit (Name x (Delimited _ _) _)       = LitString x
    toLit (Name x t _)                     = case TR.readMaybe x of
        Just a  -> LitInt a
        Nothing -> case TR.readMaybe x of
            Just a  -> LitString a
            Nothing -> error ("Can't convert to literal : " ++ x)
    
    getEVS LitIf           = Strict
    getEVS (LitPF LitIf _) = Lazy
    getEVS (LitPF r _)     = getEVS r
    getEVS _               = Strict
