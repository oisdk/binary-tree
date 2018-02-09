module Main (main) where

import Criterion.Main
import System.Random
import Data.Tree.Binary.Preorder

int :: IO Int
int = randomIO

showAtSize n = env (replicateA n int) $ \xs -> bench (show n) $ nf drawTree xs

main :: IO ()
main = defaultMain (map showAtSize [10000, 100000])
