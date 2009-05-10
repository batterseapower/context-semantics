module Language.ContextSemantics.Output where


data Output a = Output String a

instance Show a => Show (Output a) where
    show (Output port what) = port ++ ": " ++ show what

showCompactList :: Show a => [a] -> ShowS
showCompactList = foldr (\x -> (shows x .)) id