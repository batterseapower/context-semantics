module Language.ContextSemantics.LinearLambdaExplicit where

import Language.ContextSemantics.Expressions
import Language.ContextSemantics.Output

import Control.Arrow (second)

import Data.Maybe

import qualified Data.Map as M
import qualified Data.Graph.Inductive as G


--
-- Graphs
--

data Router = Fan
            | FV String
            deriving (Show)

data RouterPort = PrincipalPort | WhitePort | BlackPort
                deriving (Show, Enum, Bounded, Eq, Ord)

data Graph = Graph {
    graph_gr :: G.Gr Router [(G.Node, RouterPort)],
      -- ^ Labels on edges describe which ports of the two nodes in question are attached to the edge
    graph_root :: G.Node
  }

graphSemantics :: Graph -> Port
graphSemantics (Graph gr root_n) = fromJust $ M.lookup (root_n, PrincipalPort) input_ports
  where input_ports :: M.Map (G.Node, RouterPort) Port
        input_ports = M.fromList input_ports_l
        input_ports_l = G.ufold nodeSemantics [] gr
        
        nodeSemantics (to, node, rtr, _from) l = (++ l) $ case rtr of
            Fan  -> case fan (certainlyLookup PrincipalPort my_output_ports) (certainlyLookup WhitePort my_output_ports) (certainlyLookup BlackPort my_output_ports) of
                      (princp_in, white_in, black_in) -> [((node, PrincipalPort), princp_in), ((node, WhitePort), white_in), ((node, BlackPort), black_in)]
            FV s -> [((node, PrincipalPort), fv s)]
          where extractForeignPort (edge, foreign_node) = (certainlyLookup node edge, (foreign_node, certainlyLookup foreign_node edge))
                my_output_ports = map (second (fromJust . flip M.lookup input_ports) . extractForeignPort) to

certainlyLookup :: Eq a => a -> [(a, b)] -> b
certainlyLookup = (fromJust .) . lookup

--
-- Context semantics
--

data Token = White | Black

instance Show Token where
    show White = "⚪"
    show Black = "⚫"
    
    showList = showCompactList

type Port = [Token] -> Output [Token]

fan :: Port -> Port -> Port -> (Port, Port, Port)
fan princp_out white_out black_out = (princp_in, white_in, black_in)
  where
    princp_in (White:ts) = white_out ts
    princp_in (Black:ts) = black_out ts
    princp_in []         = error "fan: empty incoming context at principal port"
    
    white_in ts = princp_out (White:ts)
    
    black_in ts = princp_out (Black:ts)

fv :: String -> Port
fv = Output

--
-- Translation from traditional linear lambda calculus
--

newtype UniqM a = UniqM { unUniqM :: [Int] -> ([Int], a) }

instance Monad UniqM where
    return x = UniqM $ \is -> (is, x)
    mx >>= f = UniqM $ \is -> case unUniqM mx is of (is', x) -> unUniqM (f x) is'


fanRouter :: 


exprGraph :: Expr -> (Graph, [(String, G.Node)])
exprGraph e = exprGraph' --(fv "Input") [(v, fv v) | v <- freeVars e] e

exprGraph' :: (G.Node, RouterPort) -> [(String, (G.Node, RouterPort))] -> Expr -> UniqM ((G.Node, RouterPort), [(String, (G.Node, RouterPort))])
exprGraph' (out_port, out_rtrprt) env (V v)
  | Just p <- lookup v env = return (p, [(v, (out_port, out_rtrprt))])
  | otherwise              = error $ "No binding for " ++ v
exprGraph' (out_port, out_rtrprt) env (e1 :@ e2) = do
    ((e1_port, e1_rtrprt), usg1) <- exprSemantics' r env e1
    ((e2_port, e2_rtrprt), usg2) <- exprSemantics' a env e2
    
    
    
    let (r, c, a) = fan e1_port out_port e2_port
    c
exprSemantics' out_port env (Lam v e) = (r, filter ((/= v) . fst) usg)
  where (e_port, usg) = exprSemantics' b ((v, p) : env) e
        v_port = (error $ "Missing usage of " ++ v) `fromMaybe` lookup v usg
        (r, b, p) = fan out_port e_port v_port


exprSemantics :: Expr -> (Port, [(String, Port)])
exprSemantics e = exprSemantics' (fv "Input") [(v, fv v) | v <- freeVars e] e

exprSemantics' :: Port -> [(String, Port)] -> Expr -> (Port, [(String, Port)])
exprSemantics' out_port env (V v)
  | Just p <- lookup v env = (p,    [(v, out_port)])
  | otherwise              = error $ "No binding for " ++ v
exprSemantics' out_port env (e1 :@ e2) = (c, usg1 ++ usg2)
  where (e1_port, usg1) = exprSemantics' r env e1
        (e2_port, usg2) = exprSemantics' a env e2
        (r, c, a) = fan e1_port out_port e2_port
exprSemantics' out_port env (Lam v e) = (r, filter ((/= v) . fst) usg)
  where (e_port, usg) = exprSemantics' b ((v, p) : env) e
        v_port = (error $ "Missing usage of " ++ v) `fromMaybe` lookup v usg
        (r, b, p) = fan out_port e_port v_port

--
-- Examples
--

examples :: IO ()
examples = do
    printUTF8 $ identity []
    printUTF8 $ normal [White, White]
    printUTF8 $ normal_expr [White, White]
    printUTF8 $ normal_expr_th [White, White]

-- (\x.x) @ y
--  Port wired to the input of the application
identity :: Port
identity = cont_app
  where
    inp = fv "Input"
    y_out = fv "y"
    (princp_app, cont_app, _y_in) = fan princp_id inp y_out
    (princp_id, body_id, param_id) = fan princp_app param_id body_id

-- (\x.\y.(y @ z) @ x)
--  Port wired to the input of the lambda term
normal :: Port
normal = r1
  where
    inp = fv "Input"
    z = fv "z"
    (r1, b1, p1) = fan inp r2 a3
    (r2, b2, p2) = fan b1 c3 r4
    (r3, c3, a3) = fan c4 b2 p1
    (r4, c4, _a4) = fan p2 r3 z

normal_expr :: Port
normal_expr = fst $ exprSemantics $ Lam "x" (Lam "y" (V "y" :@ V "z" :@ V "x"))

normal_expr_th :: Port
normal_expr_th = fst $ exprSemantics $ $(expr [| \x -> \y -> y $(fvTH "z") x |])