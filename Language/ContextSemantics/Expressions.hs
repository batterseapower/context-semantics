module Language.ContextSemantics.Expressions where

import Data.List

import qualified Language.Haskell.TH as TH


data Expr = V String
          | Expr :@ Expr
          | Lam String Expr

infixl 8 :@

freeVars :: Expr -> [String]
freeVars (V v) = [v]
freeVars (e1 :@ e2) = freeVars e1 ++ freeVars e2
freeVars (Lam v e) = delete v $ freeVars e

expr :: TH.ExpQ -> TH.ExpQ
expr qe = do
    e <- qe
    case e of
        TH.VarE nm              -> [| V $(TH.stringE (TH.nameBase nm)) |]
        TH.AppE e1 e2           -> [| $(expr (return e1)) :@ $(expr (return e2)) |]
        TH.LamE [TH.VarP nm] e1 -> [| Lam $(TH.stringE (TH.nameBase nm)) $(expr (return e1)) |]
        _                       -> fail $ "Sorry, can't handle this bit of Haskell in the expression language: " ++ show e

fvTH :: String -> TH.ExpQ
fvTH s = TH.varE (TH.mkName s)