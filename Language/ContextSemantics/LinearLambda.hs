module Language.ContextSemantics.LinearLambda where

import Language.ContextSemantics.Expressions
import Language.ContextSemantics.Output

import Data.Maybe

--
-- Context semantics
--

data Token = White | Black

instance Show Token where
    show White = "⚪"
    show Black = "⚫"
    
    showList = showCompactList

type Port = [Token] -> Either String (Output [Token])

app :: Port -> Port -> Port -> (Port, Port, Port)
app princp_out cont_out arg_out = (princp_in, cont_in, arg_in)
  where
    princp_in (White:ts) = cont_out ts
    princp_in (Black:ts) = arg_out ts
    princp_in []         = Left "app: empty incoming context at principal port"
    
    cont_in ts = princp_out (White:ts)
    
    arg_in ts = princp_out (Black:ts)

lam :: Port -> Port -> Port -> (Port, Port, Port)
lam princp_out body_out param_out = (princp_in, body_in, param_in)
  where
    princp_in (White:ts) = body_out ts
    princp_in (Black:ts) = param_out ts
    princp_in []         = Left "lam: empty incoming context at principal port"
    
    body_in ts = princp_out (White:ts)
    
    param_in ts = princp_out (Black:ts)

fv :: String -> Port
fv = (Right .) . Output

--
-- Translation from traditional linear lambda calculus
--

exprSemantics :: Expr -> (Port, [(String, Port)])
exprSemantics e = exprSemantics' (fv "Input") [(v, fv v) | v <- freeVars e] e

exprSemantics' :: Port -> [(String, Port)] -> Expr -> (Port, [(String, Port)])
exprSemantics' out_port env (V v)
  | Just p <- lookup v env = (p,    [(v, out_port)])
  | otherwise              = error $ "No binding for " ++ v
exprSemantics' out_port env (e1 :@ e2) = (c, usg1 ++ usg2)
  where (e1_port, usg1) = exprSemantics' r env e1
        (e2_port, usg2) = exprSemantics' a env e2
        (r, c, a) = app e1_port out_port e2_port
exprSemantics' out_port env (Lam v e) = (r, filter ((/= v) . fst) usg)
  where (e_port, usg) = exprSemantics' b ((v, p) : env) e
        v_port = (error $ "Missing usage of " ++ v) `fromMaybe` lookup v usg
        (r, b, p) = lam out_port e_port v_port

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
    (princp_app, cont_app, _y_in) = app princp_id inp y_out
    (princp_id, body_id, param_id) = lam princp_app param_id body_id

-- (\x.\y.(y @ z) @ x)
--  Port wired to the input of the lambda term
normal :: Port
normal = r1
  where
    inp = fv "Input"
    z = fv "z"
    (r1, b1, p1) = lam inp r2 a3
    (r2, b2, p2) = lam b1 c3 r4
    (r3, c3, a3) = app c4 b2 p1
    (r4, c4, _a4) = app p2 r3 z

normal_expr :: Port
normal_expr = fst $ exprSemantics $ Lam "x" (Lam "y" (V "y" :@ V "z" :@ V "x"))

normal_expr_th :: Port
normal_expr_th = fst $ exprSemantics $ $(expr [| \x -> \y -> y $(fvTH "z") x |])