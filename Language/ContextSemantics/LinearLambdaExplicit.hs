module Language.ContextSemantics.LinearLambdaExplicit where

import Language.ContextSemantics.Common
import Language.ContextSemantics.Expressions
import Language.ContextSemantics.Graph
import Language.ContextSemantics.Output
import Language.ContextSemantics.Utilities

import Control.Applicative ((<$>), (<*>))

import qualified Data.Foldable as F
import Data.Monoid
import qualified Data.Traversable as T


--
-- Interaction graphs
--

data Router a = Fan a a a
              | FV String a
              deriving (Show)

instance Functor Router where
    fmap f (Fan pr wh bl) = Fan (f pr) (f wh) (f bl)
    fmap f (FV s pr)      = FV s (f pr)

instance F.Foldable Router where
    foldMap f (Fan pr wh bl) = f pr `mappend` f wh `mappend` f bl
    foldMap f (FV _ pr) = f pr

instance T.Traversable Router where
    sequenceA (Fan apr awh abl) = Fan <$> apr <*> awh <*> abl
    sequenceA (FV s mpr) = FV s <$> mpr

data RouterSelector = FanPr | FanWh | FanBl | FVPr
                    deriving (Show, Eq)

instance Interactor Router where
    type Selector Router = RouterSelector
  
    selectors (Fan pr wh bl) = Fan (FanPr, pr) (FanWh, wh) (FanBl, bl)
    selectors (FV s pr)      = FV s (FVPr, pr)
  
    select FanPr (Fan pr _  _ ) = pr
    select FanWh (Fan _  wh _ ) = wh
    select FanBl (Fan _  _  bl) = bl
    select FVPr  (FV _ pr)      = pr

inputGraphSemantics :: Graph Router -> Route
inputGraphSemantics = lookupCertainly "Input" . graphSemantics

graphSemantics :: Graph Router -> [(PortName, Route)]
graphSemantics = foldPortwise routerSemantics

routerSemantics :: Router Route -> Router Route
routerSemantics (Fan pr wh bl) = Fan pr' wh' bl'
  where (pr', wh', bl') = fan pr wh bl
routerSemantics (FV s pr) = FV s (fv s pr)

graphToDot :: Graph Router -> String
graphToDot = toDot node_attrs edge_attrs
  where node_attrs (Fan _ _ _) = [("shape", "triangle")]
        node_attrs (FV s _)    = [("shape", "dot"), ("label", s)]
        
        edge_attrs from to = [("arrowtail", selector_shape from), ("arrowhead", selector_shape to),
                              ("tailport", selector_port from),   ("headport", selector_port to)]
        
        selector_shape FanPr = "none"
        selector_shape FanWh = "odot"
        selector_shape FanBl = "dot"
        selector_shape FVPr = "none"
        
        selector_port FanPr = "n"
        selector_port FanWh = "sw"
        selector_port FanBl = "se"
        selector_port FVPr = "n"

writeDot :: String -> Graph Router -> IO ()
writeDot nm gr = writeFile (nm ++ ".dot") (graphToDot gr)


--
-- Context semantics
--

data Token = White | Black

instance Show Token where
    show White = "⚪"
    show Black = "⚫"
    
    showList = showCompactList

type Route = [Token] -> Either String (Output [Token])

fan :: Route -> Route -> Route -> (Route, Route, Route)
fan princp_out white_out black_out = (princp_in, white_in, black_in)
  where
    princp_in (White:ts) = white_out ts
    princp_in (Black:ts) = black_out ts
    princp_in []         = Left "fan: empty incoming context at principal port"
    
    white_in ts = princp_out (White:ts)
    
    black_in ts = princp_out (Black:ts)

fv :: String -> Route -> Route
fv s _fv_out = Right . Output s


--
-- Translation from traditional linear lambda calculus
--

fvNode :: String -> LooseEnd -> GraphBuilderM Router ()
fvNode s wpr = newNode (FV s wpr)

fanNode :: LooseEnd -> LooseEnd -> LooseEnd -> GraphBuilderM Router ()
fanNode wpr wwh wbl = newNode (Fan wpr wwh wbl)

exprGraph :: Expr -> Graph Router
exprGraph e = runGraphBuilderM $ do
    let buildFVNode v = do
            (pfv1, pfv2) <- newWire
            fvNode v pfv1
            return ((v, pfv1), (v, pfv2))
    (env1, env2) <- fmap unzip $ mapM buildFVNode (freeVars e)

    (proot1, proot2) <- newWire
    fvNode "Input" proot1
    buildExprGraph env2 proot2 e
    return $ ("Input", proot1) : env1

buildExprGraph :: [(PortName, LooseEnd)] -> LooseEnd -> Expr -> GraphBuilderM Router ()
buildExprGraph env ptop (V v)
  | Just pbind <- lookup v env = join ptop pbind
  | otherwise                  = error $ "No binding for " ++ v
buildExprGraph env ptop (e1 :@ e2) = do
    (pfn1, pfn2) <- newWire
    buildExprGraph env pfn1 e1
    
    (parg1, parg2) <- newWire
    buildExprGraph env parg1 e2
    
    fanNode pfn2 ptop parg2
buildExprGraph env ptop (Lam v e) = do
    (pbody1, pbody2) <- newWire
    (pparam1, pparam2) <- newWire
    buildExprGraph ((v, pparam1) : env) pbody1 e
    
    fanNode ptop pbody2 pparam2


--
-- Readback
--

semanticsExpr :: [(PortName, Route)] -> Expr
semanticsExpr named_routes = undefined


--
-- Examples
--

examples :: IO ()
examples = do
    printUTF8 $ inputGraphSemantics xGraph [Black]
    printUTF8 $ inputGraphSemantics xyGraph [White]
    printUTF8 $ inputGraphSemantics identityAppGraph [Black]
    printUTF8 $ inputGraphSemantics normalGraph [White, White]

dots :: IO ()
dots = do
    writeDot "x" xGraph
    writeDot "xy" xyGraph
    writeDot "identityApp" identityAppGraph
    writeDot "normal" normalGraph

xGraph, xyGraph, identityAppGraph, normalGraph :: Graph Router

xGraph = exprGraph $ V "x"

xyGraph = exprGraph $ V "x" :@ V "y"

identityAppGraph = exprGraph $ (Lam "x" (V "x")) :@ (V "y")

normalGraph = exprGraph $ Lam "x" (Lam "y" (V "y" :@ V "z" :@ V "x"))
