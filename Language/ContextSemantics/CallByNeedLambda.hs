module Language.ContextSemantics.CallByNeedLambda where

import Language.ContextSemantics.Expressions
import Language.ContextSemantics.Output

import Data.List.Zipper


data Token = White | Black | LeftT | RightT | Bracket [Token] [Token] | Symbol String

instance Show Token where
    show White = "⚪"
    show Black = "⚫"
    show LeftT = "L"
    show RightT = "R"
    show (Bracket ts1 ts2) = "<" ++ show ts1 ++ "," ++ show ts2 ++ ">"
    show (Symbol s) = s
    
    showList = showCompactList

type Port = Zipper [Token] -> Output (Zipper [Token])

pushAndRefocus :: a -> Zipper a -> Zipper a
pushAndRefocus s = left . push s

popAtCursor :: Zipper [Token] -> (Token, Zipper [Token])
popAtCursor tss = case cursor tss of
    (t:ts) -> (t, replace ts tss)
    []     -> error $ "popAtCursor: malformed incoming context " ++ show tss

pushAtCursor :: Token -> Zipper [Token] -> Zipper [Token]
pushAtCursor t tss = replace (t : cursor tss) tss

app :: Port -> Port -> Port -> (Port, Port, Port)
app princp_out cont_out arg_out = (princp_in, cont_in, arg_in)
  where
    princp_in tss = case popAtCursor tss of
        (White, tss') -> cont_out tss'
        (Black, tss') -> arg_out tss'
        _             -> error $ "app: principal port got malformed incoming context " ++ show tss
    
    cont_in tss = princp_out (pushAtCursor White tss)
    
    arg_in tss = princp_out (pushAtCursor Black tss)

lam :: Port -> Port -> Port -> (Port, Port, Port)
lam princp_out body_out param_out = (princp_in, body_in, param_in)
  where
    princp_in tss = case popAtCursor tss of
        (White, tss') -> body_out tss'
        (Black, tss') -> param_out tss'
        _             -> error $ "lam: principal port got malformed incoming context " ++ show tss
    
    body_in tss = princp_out (pushAtCursor White tss)
    
    param_in tss = princp_out (pushAtCursor Black tss)

share :: Port -> Port -> Port -> (Port, Port, Port)
share princp_out left_out right_out = (princp_in, left_in, right_in)
  where
    princp_in tss = case popAtCursor tss of
        (LeftT, tss')  -> left_out tss'
        (RightT, tss') -> right_out tss'
        _              -> error $ "share: principal port got malformed incoming context " ++ show tss
    
    left_in tss = princp_out (pushAtCursor LeftT tss)
    
    right_in tss = princp_out (pushAtCursor RightT tss)

enterBox :: Port -> Port
enterBox entering ts = entering (right ts)

leaveBox :: Port -> Port
leaveBox leaving ts = leaving (left ts)

croissant :: String -> Port -> Port -> (Port, Port)
croissant s forced_out boxed_out = (forced_in, boxed_in)
  where
    forced_in tss = boxed_out (pushAndRefocus [Symbol s] tss)
    
    boxed_in tss = case cursor tss of
        [Symbol s'] | s == s' -> forced_out (pop tss)
        _                     -> error $ "croissant: boxed port got malformed incoming context " ++ show tss

bracket :: Port -> Port -> (Port, Port)
bracket merged_out waiting_out = (merged_in, waiting_in)
  where
    merged_in tss = waiting_out (replace ([Bracket (cursor tss) (cursor (right tss))]) (pop tss))
    
    waiting_in tss = case cursor tss of
        [Bracket shallow deep] -> merged_out $ pushAndRefocus shallow $ pushAndRefocus deep $ pop tss
        _                      -> error $ "bracket: waiting port got malformed incoming context " ++ show tss

fv :: String -> Port
fv = Output

examples :: IO ()
examples = do
    printUTF8 $ identity $ fromList [[White]]
    printUTF8 $ identity_app $ fromList [[]]

-- (\x.x) @ y
--  Port wired to the input of the lambda
identity :: Port
identity = r1
  where
    inp = fv "Input"
    (r1, b1, p1) = lam inp f2 b2
    (f2, b2) = croissant "x" b1 p1

-- (\x.x) @ y
--  Port wired to the input of the application
identity_app :: Port
identity_app = c1
  where
    inp = fv "Input"
    y = fv "y"
    (r1, c1, _a1) = app r2 inp (enterBox y)
    (r2, b2, p2) = lam r1 f3 b3
    (f3, b3) = croissant "x" b2 p2