module Main (main) where

import qualified Language.ContextSemantics.CallByNeedLambda as CBN
import qualified Language.ContextSemantics.LinearLambda as L


main :: IO ()
main = do
    putStrLn "Linear Lambda Calculus:"
    L.examples
    putStrLn "Call By Name Lambda Calculus:"
    CBN.examples