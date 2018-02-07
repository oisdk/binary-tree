module Data.Tree.Binary.Internal where

data StringBuilder = SB { size :: {-# UNPACK #-} !Int, levels :: [String -> String] }

drawBinaryTree :: Show a => (StringBuilder -> (a -> StringBuilder -> StringBuilder -> StringBuilder) -> b -> StringBuilder) -> b -> String
drawBinaryTree ft = unlines' . levels . ft (SB 0 []) f
  where
    f el (SB llen lb) (SB rlen rb) = SB
        ( llen + rlen + xlen)
        ( pad llen . (xshw ++) . pad rlen :
          zipLongest llen rlen join' lb rb)
      where
        xshw = show el
        xlen = length xshw
        join' x y = x . pad xlen . y
    pad = flip (foldr (:)) . flip replicate ' '
    unlines' = foldr (\e a -> e ('\n' : a)) ""
    zipLongest ldef rdef fn = go
      where
        go (x:xs) (y:ys) = fn x y : go xs ys
        go [] ys         = map (fn (pad ldef)) ys
        go xs []         = map (`fn` (pad rdef)) xs
