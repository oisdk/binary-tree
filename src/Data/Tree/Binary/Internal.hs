module Data.Tree.Binary.Internal where

import Prelude hiding (unlines)

data LevelBuilder = LevelBuilder
  { offset :: {-# UNPACK #-} !Int
  , levels :: [String -> String]
  }

drawBinaryTree ::
     Show a
  => (LevelBuilder -> (a -> LevelBuilder -> LevelBuilder -> LevelBuilder) -> b -> LevelBuilder)
  -> b
  -> String
drawBinaryTree ft = unlines . levels . ft (LevelBuilder 0 []) f
  where
    f el (LevelBuilder llen lb) (LevelBuilder rlen rb) =
      LevelBuilder
        (llen + rlen + xlen)
        (pad llen . (xshw ++) . pad rlen : zipLongest lb rb)
      where
        xshw = show el
        xlen = length xshw
        zipLongest (x:xs) (y:ys) = x . pad xlen . y : zipLongest xs ys
        zipLongest [] ys = map (\y -> pad (llen+xlen) . y) ys
        zipLongest xs [] = map (\x -> x . pad (xlen+rlen)) xs
    pad = flip (foldr (:)) . flip replicate ' '
    unlines [] = ""
    unlines (x:xs) = x (foldr (\e a -> '\n' : e a) "" xs)
