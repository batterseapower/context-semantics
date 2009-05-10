module Language.ContextSemantics.LinearLambda where

import Language.ContextSemantics.Output


data Token = White | Black

instance Show Token where
    show White = "⚪"
    show Black = "⚫"
    
    showList = showCompactList

type Port = [Token] -> Output [Token]

app :: Port -> Port -> Port -> (Port, Port, Port)
app princp_out cont_out arg_out = (princp_in, cont_in, arg_in)
  where
    princp_in (White:ts) = cont_out ts
    princp_in (Black:ts) = arg_out ts
    princp_in []         = error "app: empty incoming context at principal port"
    
    cont_in ts = princp_out (White:ts)
    
    arg_in ts = princp_out (Black:ts)

lam :: Port -> Port -> Port -> (Port, Port, Port)
lam princp_out body_out param_out = (princp_in, body_in, param_in)
  where
    princp_in (White:ts) = body_out ts
    princp_in (Black:ts) = param_out ts
    princp_in []         = error "lam: empty incoming context at principal port"
    
    body_in ts = princp_out (White:ts)
    
    param_in ts = princp_out (Black:ts)

fv :: String -> Port
fv = Output

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