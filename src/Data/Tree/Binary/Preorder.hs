{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE Safe               #-}

-- | A simple, generic binary tree and some operations.
module Data.Tree.Binary.Preorder
  (
   -- * The tree type
   Tree(..)
  ,
   -- * Construction
   unfoldTree
  ,replicate
  ,replicateA
  ,singleton
  ,empty
  ,fromList
  ,
   -- * Consumption
   foldTree
  ,zygoTree
  ,
   -- * Display
   drawBinaryTree)
  where

import           Control.DeepSeq       (NFData (..))
import           Data.Data             (Data)
import           Data.Functor.Classes
import           Data.Monoid
import           Data.Typeable         (Typeable)
import           GHC.Generics          (Generic, Generic1)

import           Control.Applicative   hiding (empty)
import           Data.Functor.Identity
import           Data.List             (uncons)
import           Data.Maybe            (fromMaybe)
import           Text.Read
import           Text.Read.Lex

import           Prelude               hiding (replicate)

-- | A simple binary tree.
data Tree a
    = Leaf
    | Node a
           (Tree a)
           (Tree a)
    deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable,Typeable
             ,Generic,Generic1,Data)

-- | A binary tree with one element.
singleton :: a -> Tree a
singleton x = Node x Leaf Leaf
{-# INLINE singleton #-}

-- | A binary tree with no elements.
empty :: Tree a
empty = Leaf
{-# INLINE empty #-}

instance NFData a =>
         NFData (Tree a) where
    rnf Leaf         = ()
    rnf (Node x l r) = rnf x `seq` rnf l `seq` rnf r

instance Eq1 Tree where
    liftEq _ Leaf Leaf = True
    liftEq eq (Node x xl xr) (Node y yl yr) =
        eq x y && liftEq eq xl yl && liftEq eq xr yr
    liftEq _ _ _ = False

instance Ord1 Tree where
    liftCompare _ Leaf Leaf = EQ
    liftCompare cmp (Node x xl xr) (Node y yl yr) =
        cmp x y <> liftCompare cmp xl yl <> liftCompare cmp xr yr
    liftCompare _ Leaf _ = LT
    liftCompare _ _ Leaf = GT

instance Show1 Tree where
    liftShowsPrec s _ = go where
      go _ Leaf = showString "Leaf"
      go d (Node x l r)
        = showParen (d >= 11)
        $ showString "Node "
        . s 11 x
        . showChar ' '
        . go 11 l
        . showChar ' '
        . go 11 r

instance Read1 Tree where
    liftReadPrec rp _ = go
      where
        go =
            parens $
            prec 10 (Leaf <$ expect' (Ident "Leaf")) +++
            prec
                10
                (expect' (Ident "Node") *>
                 liftA3 Node (step rp) (step go) (step go))
        expect' = lift . expect

-- | Fold over a tree.
--
-- prop> foldTree Leaf Node xs === xs
foldTree :: b -> (a -> b -> b -> b) -> Tree a -> b
foldTree b f = go where
  go Leaf         = b
  go (Node x l r) = f x (go l) (go r)

-- | A zygomorphism over a tree. Used if you want perform two folds
-- over a tree in one pass.
--
-- As an example, checking if a tree is balanced can be performed like
-- this using explicit recursion:
--
-- @
-- isBalanced :: 'Tree' a -> Bool
-- isBalanced 'Leaf' = True
-- isBalanced ('Node' _ l r)
--   = 'length' l == 'length' r && isBalanced l && isBalanced r
-- @
--
-- However, this algorithm performs several extra passes over the
-- tree. A more efficient version is much harder to read, however:
--
-- @
-- isBalanced :: Tree a -> Bool
-- isBalanced = snd . go where
--   go 'Leaf' = (0 :: Int,True)
--   go ('Node' _ l r) =
--       let (llen,lbal) = go l
--           (rlen,rbal) = go r
--       in (llen + rlen + 1, llen == rlen && lbal && rbal)
-- @
--
-- This same algorithm (the one pass version) can be expressed as a
-- zygomorphism:
--
-- @
-- isBalanced :: 'Tree' a -> Bool
-- isBalanced =
--     'zygoTree'
--         (0 :: Int)
--         (\\_ x y -> 1 + x + y)
--         True
--         go
--   where
--     go _ llen lbal rlen rbal = llen == rlen && lbal && rbal
-- @
zygoTree
    :: p
    -> (a -> p -> p -> p)
    -> b
    -> (a -> p -> b -> p -> b -> b)
    -> Tree a
    -> b
zygoTree p f1 b f = snd . go where
  go Leaf = (p,b)
  go (Node x l r) =
      let (lr1,lr) = go l
          (rr1,rr) = go r
      in (f1 x lr1 rr1, f x lr1 lr rr1 rr)

-- | Unfold a tree from a seed.
unfoldTree :: (b -> Maybe (a, b, b)) -> b -> Tree a
unfoldTree f = go where
  go = maybe Leaf (\(x,l,r) -> Node x (go l) (go r)) . f

-- | @'replicate' n a@ creates a tree of size @n@ filled @a@.
--
-- >>> putStr (drawBinaryTree (replicate 4 ()))
--     ()
--   ()  ()
-- ()
--
-- prop> \(NonNegative n) -> length (replicate n ()) === n
replicate :: Int -> a -> Tree a
replicate n x = runIdentity (replicateA n (Identity x))

-- | @'replicateA' n a@ replicates the action @a@ @n@ times, trying
-- to balance the result as much as possible. The actions are executed
-- in a preorder traversal (same as the 'Foldable' instance.)
--
-- >>> toList (evalState (replicateA 10 (State (\s -> (s, s + 1)))) 1)
-- [1,2,3,4,5,6,7,8,9,10]
replicateA :: Applicative f => Int -> f a -> f (Tree a)
replicateA n x = go n
  where
    go m
      | m <= 0 = pure Leaf
      | even m = Node <$> x <*> r <*> go (d-1)
      | otherwise = Node <$> x <*> r <*> r
      where
        d = m `div` 2
        r = go d
{-# SPECIALIZE replicateA :: Int -> Identity a -> Identity (Tree a) #-}

-- | This instance is necessarily inefficient, to obey the monoid laws.
--
-- >>> putStr (drawBinaryTree (fromList [1..6]))
--    1
--  2   5
-- 3 4 6
--
-- >>> putStr (drawBinaryTree (fromList [1..6] `mappend` singleton 7))
--    1
--  2   5
-- 3 4 6 7
--
-- 'mappend' distributes over 'toList':
--
-- prop> toList (mappend xs (ys :: Tree Int)) === mappend (toList xs) (toList ys)
instance Monoid (Tree a) where
    mappend Leaf y         = y
    mappend (Node x l r) y = Node x l (mappend r y)
    mempty = Leaf

-- | Construct a tree from a list, in an preorder fashion.
--
-- prop> toList (fromList xs) === xs
fromList :: [a] -> Tree a
fromList xs = evalState (replicateA n u) xs
  where
    n = length xs
    u = State (fromMaybe (error "Data.Tree.Binary.fromList: bug!") . uncons)

-- | Pretty-print a tree.
--
-- >>> putStr (drawBinaryTree (fromList [1..7]))
--    1
--  2   5
-- 3 4 6 7
drawBinaryTree :: Show a => Tree a -> String
drawBinaryTree = foldr (. (:) '\n') "" . snd . foldTree (0, []) f
  where
    f el (llen,lb) (rlen,rb) =
        ( llen + rlen + xlen
        , pad llen . (xshw ++) . pad rlen :
          zipLongest (pad llen) (pad rlen) join' lb rb)
      where
        xshw = show el
        xlen = length xshw
        join' x y = x . pad xlen . y
    pad 0 = id
    pad n = (' ' :) . pad (n - 1)

zipLongest :: a -> b -> (a -> b -> c) -> [a] -> [b] -> [c]
zipLongest ldef rdef fn = go
  where
    go (x:xs) (y:ys) = fn x y : go xs ys
    go [] ys         = map (fn ldef) ys
    go xs []         = map (`fn` rdef) xs

newtype State s a = State
    { runState :: s -> (a, s)
    } deriving (Functor)

instance Applicative (State s) where
    pure x = State (\s -> (x, s))
    fs <*> xs =
        State
            (\s ->
                  case runState fs s of
                      (f,s') ->
                          case runState xs s' of
                              (x,s'') -> (f x, s''))

evalState :: State s a -> s -> a
evalState xs s = fst (runState xs s)

-- $setup
-- >>> :set -XDeriveFunctor
-- >>> import Test.QuickCheck
-- >>> import Data.Foldable
-- >>> :{
-- instance Arbitrary a =>
--          Arbitrary (Tree a) where
--     arbitrary = sized go
--       where
--         go 0 = pure Leaf
--         go n
--           | n <= 0 = pure Leaf
--           | otherwise = oneof [pure Leaf, liftA3 Node arbitrary sub sub]
--           where
--             sub = go (n `div` 2)
--     shrink Leaf = []
--     shrink (Node x l r) =
--         Leaf : l : r :
--         [ Node x' l' r'
--         | (x',l',r') <- shrink (x, l, r) ]
-- :}
