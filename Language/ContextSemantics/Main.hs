module Main (main) where

import qualified Language.ContextSemantics.CallByNeedLambda as CBN
import qualified Language.ContextSemantics.LinearLambda as L
import qualified Language.ContextSemantics.LinearLambdaExplicit as LE


main :: IO ()
main = do
    putStrLn "Linear Lambda Calculus:"
    L.examples
    putStrLn "Explicit Linear Lambda Calculus:"
    LE.examples
    putStrLn "Call By Name Lambda Calculus:"
    CBN.examples