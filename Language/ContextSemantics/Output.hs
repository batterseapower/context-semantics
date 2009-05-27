module Language.ContextSemantics.Output where

import Language.ContextSemantics.Common

import qualified System.IO.UTF8


data Output a = Output PortName a

instance Show a => Show (Output a) where
    show (Output port what) = port ++ ": " ++ show what

showCompactList :: Show a => [a] -> ShowS
showCompactList = foldr (\x -> (shows x .)) id

printUTF8 :: Show a => a -> IO ()
printUTF8 = System.IO.UTF8.print