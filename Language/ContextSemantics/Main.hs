module Main (main) where

import Language.ContextSemantics.LinearLambda

import System.IO.UTF8
import Prelude hiding (print)


main :: IO ()
main = do
    print (identity [])
    print (normal [White, White])