module HigherOrder where

{-@ LIQUID "--higher-order" @-}

import Prelude hiding (map)


{-@ map :: f:(a -> b) -> xs:[a] -> {v:[b] | len xs == len v } @-}
map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x:map f xs
