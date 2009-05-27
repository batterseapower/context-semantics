module Language.ContextSemantics.CallByNeedLambda where

import Language.ContextSemantics.Expressions
import Language.ContextSemantics.Utilities ()
import Language.ContextSemantics.Output

import Control.Arrow (second)

import Data.List (nub)
import Data.List.Zipper
import Data.Maybe
import Data.Nthable

import Prelude hiding (fst, snd)

--
-- Context semantics
--

data Token = White | Black | LeftT | RightT | Bracket [Token] [Token] | Symbol String

instance Show Token where
    show White = "⚪"
    show Black = "⚫"
    show LeftT = "L"
    show RightT = "R"
    show (Bracket ts1 ts2) = "<" ++ show ts1 ++ "," ++ show ts2 ++ ">"
    show (Symbol s) = s
    
    showList = showCompactList

type Port = Zipper [Token] -> Either String (Output (Zipper [Token]))

popAtCursor :: Zipper [Token] -> Either String (Token, Zipper [Token])
popAtCursor tss = case cursor tss of
    (t:ts) -> return (t, replace ts tss)
    []     -> Left $ "popAtCursor: malformed incoming context " ++ show tss

pushAtCursor :: Token -> Zipper [Token] -> Zipper [Token]
pushAtCursor t tss = replace (t : cursor tss) tss

app :: Port -> Port -> Port -> (Port, Port, Port)
app princp_out cont_out arg_out = (princp_in, cont_in, arg_in)
  where
    princp_in tss = popAtCursor tss >>= \tss' -> case tss' of
        (White, tss'') -> cont_out tss''
        (Black, tss'') -> arg_out tss''
        _              -> Left $ "app: principal port got malformed incoming context " ++ show tss
    
    cont_in tss = princp_out (pushAtCursor White tss)
    
    arg_in tss = princp_out (pushAtCursor Black tss)

lam :: Port -> Port -> Port -> (Port, Port, Port)
lam princp_out body_out param_out = (princp_in, body_in, param_in)
  where
    princp_in tss = popAtCursor tss >>= \tss' -> case tss' of
        (White, tss'') -> body_out tss''
        (Black, tss'') -> param_out tss''
        _              -> Left $ "lam: principal port got malformed incoming context " ++ show tss
    
    body_in tss = princp_out (pushAtCursor White tss)
    
    param_in tss = princp_out (pushAtCursor Black tss)

share :: Port -> Port -> Port -> (Port, Port, Port)
share princp_out left_out right_out = (princp_in, left_in, right_in)
  where
    princp_in tss = popAtCursor tss >>= \tss' -> case tss' of
        (LeftT, tss'')  -> left_out tss''
        (RightT, tss'') -> right_out tss''
        _               -> Left $ "share: principal port got malformed incoming context " ++ show tss
    
    left_in tss = princp_out (pushAtCursor LeftT tss)
    
    right_in tss = princp_out (pushAtCursor RightT tss)

enterBox :: Port -> Port
enterBox entering ts = entering (right ts)

leaveBox :: Port -> Port
leaveBox leaving ts = leaving (left ts)

croissant :: String -> Port -> Port -> (Port, Port)
croissant s forced_out boxed_out = (forced_in, boxed_in)
  where
    forced_in tss = boxed_out (insert [Symbol s] tss)
    
    boxed_in tss = case cursor tss of
        [Symbol s'] | s == s' -> forced_out (delete tss)
        _                     -> Left $ "croissant: boxed port got malformed incoming context " ++ show tss

bracket :: Port -> Port -> (Port, Port)
bracket merged_out waiting_out = (merged_in, waiting_in)
  where
    merged_in tss = waiting_out (insert ([Bracket (cursor tss) (cursor (right tss))]) (delete (delete tss)))
    
    waiting_in tss = case cursor tss of
        [Bracket shallow deep] -> merged_out $ insert shallow $ insert deep $ delete tss
        _                      -> Left $ "bracket: waiting port got malformed incoming context " ++ show tss

fv :: String -> Port
fv = (Right .) . Output

--
-- Translation from traditional CBN lambda calculus
--

exprSemantics :: Expr -> (Port, [(String, Port)])
exprSemantics e = exprSemantics' (fv "Input") [(v, fv v) | v <- freeVars e] e

exprSemantics' :: Port -> [(String, Port)] -> Expr -> (Port, [(String, Port)])
exprSemantics' out_port env (V v) = (forced_port, [(v, boxed_port)])
  where (forced_port, boxed_port) = croissant v out_port (lookupInEnv env v)
exprSemantics' out_port env (e1 :@ e2) = (c, usg)
  where (e1_port, usg1) = exprSemantics' r env1 e1
        -- If you send a signal out of e2 then it must leave the box - hence the modifications
        -- to the environment and the port we supply
        (e2_port, usg2) = exprSemantics' (leaveBox a) (map (second leaveBox) env2') e2
        
        -- Both expressions in the application might refer to the same free variable, and we need
        -- to insert share nodes if that happens
        (env1, env2, usg) = combineUsages env usg1 usg2'
        
        -- If you send a signal to the usages originating from e2 then you implicitly enter the box.
        -- Furthermore, we need to make sure that before you enter the box you go through a bracket
        -- node -- inserting these is the job of bracketUsages
        (env2', usg2') = bracketUsages env2 (map (second enterBox) usg2)
        
        -- Finally, build the app node. Remember that e2 is boxed, so we need to enterBox on its input port
        (r, c, a) = app e1_port out_port (enterBox e2_port)
exprSemantics' out_port env (Lam v e) = (r, filter ((/= v) . fst) usg)
  where (e_port, usg) = exprSemantics' b ((v, p) : env) e
        v_port = (fv $ "Plug for " ++ v) `fromMaybe` lookup v usg
        (r, b, p) = lam out_port e_port v_port

combineUsages :: [(String, Port)] -> [(String, Port)] -> [(String, Port)] -> ([(String, Port)], [(String, Port)], [(String, Port)])
combineUsages env usg1 usg2 = (catMaybes env1_mbs, catMaybes env2_mbs, usg)
  where
    (usg, env1_mbs, env2_mbs) = unzip3 [combineUsage v (lookup v usg1) (lookup v usg2)
                                       | v <- nub $ map fst (usg1 ++ usg2)]
    
    -- If both sides of the usage refer to the same variable, we need to insert a share node and
    -- adjust the usage and environment appropriately to interdict all communication between the
    -- use and definition sites
    combineUsage v mb_p1 mb_p2 = case (mb_p1, mb_p2) of
        (Nothing, Nothing) -> error "combineUsage"
        (Just p1, Nothing) -> ((v, p1), Just (v, p), Nothing)
        (Nothing, Just p2) -> ((v, p2), Nothing, Just (v, p))
        (Just p1, Just p2) -> let (p_in, l_in, r_in) = share p p1 p2
                              in ((v, p_in), Just (v, l_in), Just (v, r_in))
      where p = lookupInEnv env v

bracketUsages :: [(String, Port)] -> [(String, Port)] -> ([(String, Port)], [(String, Port)])
bracketUsages env = unzip . map bracketUsage
  where
    -- For every usage originating from the expression, add something to the environment that
    -- brackets it before we go any further away from the box, adjusting the usage information
    -- to now refer to the bracket
    bracketUsage (v, p) = ((v, m), (v, w))
      where (m, w) = bracket p (lookupInEnv env v)

lookupInEnv :: [(String, Port)] -> String -> Port
lookupInEnv env v = error ("No binding for " ++ v) `fromMaybe` lookup v env

--
-- Examples
--

examples :: IO ()
examples = do
    printUTF8 $ identity $ fromList [[White]]
    printUTF8 $ identity_app $ fromList [[]]
    printUTF8 $ self_app $ fromList [[White]]
    printUTF8 $ self_app $ fromList [[Black, LeftT, Symbol "x"], [Black, Symbol "α"]]
    printUTF8 $ fst dead_var $ fromList [[Black]]
    printUTF8 $ fst dead_var $ fromList [[White]]
    printUTF8 $ snd dead_var $ fromList [[Symbol "x"], [Symbol "α"]]
    printUTF8 $ fst app_to_fv $ fromList [[]]
    printUTF8 $ fst app_to_fv_in_lam $ fromList [[White]]
    printUTF8 $ snd app_to_fv_in_lam $ fromList [[Symbol "x"], [Black, Symbol "α"], [White]]

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

self_app :: Port
self_app = fst $ exprSemantics $ Lam "x" $ V "x" :@ V "x"

dead_var :: (Port, Port)
dead_var = (p, lookupInEnv fvs "x")
  where (p, fvs) = exprSemantics $ Lam "y" $ V "x"

app_to_fv :: (Port, Port, Port)
app_to_fv = (p, lookupInEnv fvs "x", lookupInEnv fvs "y")
  where (p, fvs) = exprSemantics $ V "x" :@ V "y"

app_to_fv_in_lam :: (Port, Port)
app_to_fv_in_lam = (p, lookupInEnv fvs "x")
  where (p, fvs) = exprSemantics $ Lam "y" $ V "x" :@ V "y"