module Language.ContextSemantics.LinearLambdaExplicit where

import Language.ContextSemantics.Expressions
import Language.ContextSemantics.Graph
import Language.ContextSemantics.Output

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

graphSemantics :: Graph Router -> Route
graphSemantics = foldPortwise routerSemantics

routerSemantics :: Router Route -> Router Route
routerSemantics (Fan pr wh bl) = Fan pr' wh' bl'
  where (pr', wh', bl') = fan pr wh bl
routerSemantics (FV s pr) = FV s (fv s pr)


--
-- Context semantics
--

data Token = White | Black

instance Show Token where
    show White = "⚪"
    show Black = "⚫"
    
    showList = showCompactList

type Route = [Token] -> Output [Token]

fan :: Route -> Route -> Route -> (Route, Route, Route)
fan princp_out white_out black_out = (princp_in, white_in, black_in)
  where
    princp_in (White:ts) = white_out ts
    princp_in (Black:ts) = black_out ts
    princp_in []         = error "fan: empty incoming context at principal port"
    
    white_in ts = princp_out (White:ts)
    
    black_in ts = princp_out (Black:ts)

fv :: String -> Route -> Route
fv s _fv_out = Output s

--
-- Translation from traditional linear lambda calculus
--

fvNode :: String -> Wire -> GraphBuilderM Router ()
fvNode s wpr = newNode (FV s wpr)

fanNode :: Wire -> Wire -> Wire -> GraphBuilderM Router ()
fanNode wpr wwh wbl = newNode (Fan wpr wwh wbl)

exprGraph :: Expr -> Graph Router
exprGraph e = runGraphBuilderM $ do
    let buildFVNode v = do
            pfv <- newWire
            fvNode v pfv
            return (v, pfv)
    env <- mapM buildFVNode (freeVars e)
    
    proot <- newWire
    fvNode "root" proot
    buildExprGraph env proot e
    return proot

buildExprGraph :: [(String, Wire)] -> Wire -> Expr -> GraphBuilderM Router ()
buildExprGraph env ptop (V v)
  | Just pbind <- lookup v env = join ptop pbind
  | otherwise                  = error $ "No binding for " ++ v
buildExprGraph env ptop (e1 :@ e2) = do
    pfn <- newWire
    buildExprGraph env pfn e1
    
    parg <- newWire
    buildExprGraph env parg e2
    
    fanNode pfn ptop parg
buildExprGraph env ptop (Lam v e) = do
    pbody <- newWire
    pparam <- newWire
    buildExprGraph ((v, pparam) : env) pbody e
    
    fanNode ptop pbody pparam


--
-- Examples
--

examples :: IO ()
examples = do
    printUTF8 $ exprSemantics (V "x") [Black]
    printUTF8 $ exprSemantics (V "x" :@ V "y") [White]
    printUTF8 $ identityApp [Black]
    printUTF8 $ normal [White, White]

exprSemantics :: Expr -> Route
exprSemantics = graphSemantics . exprGraph

identityApp :: Route
identityApp = exprSemantics $ (Lam "x" (V "x")) :@ (V "y")

normal :: Route
normal = exprSemantics $ Lam "x" (Lam "y" (V "y" :@ V "z" :@ V "x"))
