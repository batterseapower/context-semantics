module Language.ContextSemantics.Utilities where

import qualified Data.IntMap as IM
import Data.Maybe
import qualified Data.Traversable as T

import Debug.Trace


fromSingleton :: [a] -> a
fromSingleton [x] = x
fromSingleton xs  = error $ "fromSingleton: got " ++ show (length xs) ++ " items"

lookupCertainly :: Eq a => a -> [(a, b)] -> b
lookupCertainly = (fromJust .) . lookup

iMlookupCertainly :: Int -> IM.IntMap a -> a
iMlookupCertainly = (fromJust .) . IM.lookup

fmapM :: (T.Traversable t, Monad m) => (a -> m b) -> t a -> m (t b)
fmapM = T.mapM

fmapM_ :: (T.Traversable t, Monad m) => (a -> m b) -> t a -> m ()
fmapM_ f x = fmapM f x >> return ()

bitrace :: String -> b -> b
bitrace s x = trace (">>> " ++ s) (x `seq` trace ("<<< " ++ s) x)

assertJust :: String -> Maybe a -> a
assertJust _ (Just x) = x
assertJust s Nothing  = error $ "assertJust: got Nothing (" ++ s ++ ")"
