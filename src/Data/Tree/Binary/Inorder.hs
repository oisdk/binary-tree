{-# LANGUAGE CPP #-}

{-# LANGUAGE BangPatterns #-}
#if __GLASGOW_HASKELL__
{-# LANGUAGE DeriveDataTypeable #-}
#endif
#if __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE DeriveGeneric #-}
#endif
#if __GLASGOW_HASKELL__ >= 703
{-# LANGUAGE Safe #-}
#endif


-- | 
-- Module      : Data.Tree.Binary.Inorder
-- Description : A simple, generic, inorder binary tree.
-- Copyright   : (c) Donnacha Oisín Kidney, 2018
-- License     : MIT
-- Maintainer  : mail@doisinkidney.com
-- Stability   : experimental
-- Portability : portable
--
-- This module provides a simple inorder binary tree, as is needed
-- in several application. Instances, if sensible, are defined,
-- and generally effort is made to keep the implementation as
-- generic as possible.

module Data.Tree.Binary.Inorder
  ( -- * The tree type
   Tree(..)
   -- * Construction
  , unfoldTree
  , replicate
  , replicateA
  , singleton
  , empty
  , fromList
   -- * Consumption
  , foldTree
   -- * Querying
  , depth
   -- * Display
  , drawTree
  , drawTreeWith
  , printTree
  ) where

import Prelude hiding
  ( replicate
#if MIN_VERSION_base(4,8,0)
  ,Functor(..),Foldable(..),Applicative, (<$>), foldMap, Monoid
#else
  ,foldr,foldl
#endif
  )

import Data.List (length)

import Control.Applicative (Applicative(..), Alternative, liftA2, liftA3)
import qualified Control.Applicative as Alternative (empty, (<|>)) 

import Control.DeepSeq (NFData(rnf))

import Data.Monoid (Monoid(mappend, mempty))
import Data.Functor (Functor(fmap, (<$)))

#if MIN_VERSION_base(4,6,0)
import Data.Foldable (Foldable(foldl, foldr, foldMap, foldl', foldr'))
#else
import Data.Foldable (Foldable(foldl, foldr, foldMap))
#endif

#if MIN_VERSION_base(4,9,0)
import Data.Functor.Classes
import qualified Data.Semigroup as Semigroup
#endif

import Data.Traversable (Traversable(traverse))

import Data.Typeable (Typeable)

#if __GLASGOW_HASKELL__ >= 706
import GHC.Generics (Generic, Generic1)
#elif __GLASGOW_HASKELL__ >= 702
import GHC.Generics (Generic)
#endif

import Text.Read

#if __GLASGOW_HASKELL__
import Data.Data (Data)
#if MIN_VERSION_base(4,10,0)
import Text.Read.Lex (expect)
#endif
#endif

import qualified Data.Tree.Binary.Internal as Internal
import Data.Tree.Binary.Internal (State(..), evalState, Identity(..))

-- | An inorder binary tree.
data Tree a
  = Leaf
  | Node (Tree a)
         a
         (Tree a)
  deriving (Show, Read, Eq, Ord
#if __GLASGOW_HASKELL__ >= 706
  , Typeable, Data, Generic, Generic1
#elif __GLASGOW_HASKEL__ >= 702
  , Typeable, Data, Generic
#elif __GLASGOW_HASKELL__
  , Typeable, Data
#endif
  )

instance Functor Tree where
  fmap _ Leaf = Leaf
  fmap f (Node l x r) = Node (fmap f l) (f x) (fmap f r)
#if __GLASGOW_HASKELL__
  {-# INLINABLE fmap #-}
#endif
  x <$ xs = go xs where
    go Leaf = Leaf
    go (Node l _ r) = Node (go l) x (go r)
  {-# INLINE (<$) #-}

instance Applicative Tree where
  pure x = y where y = Node y x y
  Leaf <*> _ = Leaf
  Node _ _ _ <*> Leaf = Leaf
  Node fl f fr <*> Node xl x xr = Node (fl <*> xl) (f x) (fr <*> xr)
#if __GLASGOW_HASKELL__
  {-# INLINABLE pure #-}
  {-# INLINABLE (<*>) #-}
#endif
#if MIN_VERSION_base(4,10,0)
  liftA2 f = go where
    go Leaf _ = Leaf
    go (Node _ _ _) Leaf = Leaf
    go (Node xl x xr) (Node yl y yr) = Node (go xl yl) (f x y) (go xr yr)
  {-# INLINE liftA2 #-}
#endif
#if MIN_VERSION_base(4,2,0)
  Leaf *> _ = Leaf
  Node _ _ _ *> Leaf = Leaf
  Node xl _ xr *> Node yl y yr = Node (xl *> yl) y (xr *> yr)
  Leaf <* _ = Leaf
  Node _ _ _ <* Leaf = Leaf
  Node xl x xr <* Node yl _ yr = Node (xl <* yl) x (xr <* yr)
#if __GLASGOW_HASKELL__
  {-# INLINABLE (*>) #-}
  {-# INLINABLE (<*) #-}
#endif
#endif

instance Alternative Tree where
  empty = Leaf
  {-# INLINE empty #-}
#if MIN_VERSION_base(4,9,0)
  (<|>) = (Semigroup.<>)
#else
  (<|>) = mappend
#endif
  {-# INLINE (<|>) #-}

instance Foldable Tree where
  foldr _ b Leaf = b
  foldr f b (Node l x r) = foldr f (f x (foldr f b r)) l

  foldl _ b Leaf = b
  foldl f b (Node l x r) = foldl f (f (foldl f b l) x) r

  foldMap _ Leaf = mempty
  foldMap f (Node l x r) = foldMap f l `mappend` f x `mappend` foldMap f r

#if __GLASGOW_HASKELL__
  {-# INLINABLE foldMap #-}
  {-# INLINABLE foldr #-}
  {-# INLINABLE foldl #-}
#endif


#if MIN_VERSION_base(4,6,0)
  foldr' _ !b Leaf = b
  foldr' f !b (Node l x r) = case foldr' f b r of
    !b' -> case f x b' of
      !b'' -> foldr' f b'' l

  foldl' _ !b Leaf = b
  foldl' f !b (Node l x r) = case foldl' f b l of
    !b' -> case f b' x of
      !b'' -> foldl' f b'' r
#if __GLASGOW_HASKELL__
  {-# INLINABLE foldr' #-}
  {-# INLINABLE foldl' #-}
#endif
#endif

instance Traversable Tree where
  traverse _ Leaf = pure Leaf
  traverse f (Node l x r) = liftA3 Node (traverse f l) (f x) (traverse f r)
#if __GLASGOW_HASKELL__
  {-# INLINABLE traverse #-}
#endif

-- | A binary tree with one element.
singleton :: a -> Tree a
singleton x = Node Leaf x Leaf

{-# INLINE singleton #-}
-- | A binary tree with no elements.
empty :: Tree a
empty = Leaf

{-# INLINE empty #-}
instance NFData a => NFData (Tree a) where
  rnf Leaf = ()
  rnf (Node l x r) = rnf l `seq` rnf x `seq` rnf r

#if MIN_VERSION_base(4,9,0)
instance Eq1 Tree where
  liftEq _ Leaf Leaf = True
  liftEq eq (Node xl x xr) (Node yl y yr) =
    liftEq eq xl yl && eq x y && liftEq eq xr yr
  liftEq _ _ _ = False

instance Ord1 Tree where
  liftCompare _ Leaf Leaf = EQ
  liftCompare cmp (Node xl x xr) (Node yl y yr) =
    liftCompare cmp xl yl `mappend` cmp x y `mappend` liftCompare cmp xr yr
  liftCompare _ Leaf _ = LT
  liftCompare _ _ Leaf = GT

instance Show1 Tree where
  liftShowsPrec s _ = go
    where
      go _ Leaf = showString "Leaf"
      go d (Node l x r) =
        showParen (d >= 11) $
        showString "Node " .
        go 11 l . showChar ' ' . s 11 x . showChar ' ' . go 11 r

instance Read1 Tree where
#if MIN_VERSION_base(4,10,0) && __GLASGOW_HASKELL__
  liftReadPrec rp _ = go
    where
      go =
        parens $
        prec 10 (Leaf <$ expect' (Ident "Leaf")) +++
        prec
          10
          (expect' (Ident "Node") *> liftA3 Node (step go) (step rp) (step go))
      expect' = lift . expect
  liftReadListPrec = liftReadListPrecDefault
#else
  liftReadsPrec rp _ = go
    where
      go p st =
        [(Leaf, xs) | ("Leaf", xs) <- lex st] ++
        readParen
          (p > 10)
          (\vs ->
             [ (Node l x r, zs)
             | ("Node", ws) <- lex vs
             , (l, xs) <- go 11 ws
             , (x, ys) <- rp 11 xs
             , (r, zs) <- go 11 ys
             ])
          st
#endif
#endif

-- | Fold over a tree.
--
-- prop> foldTree Leaf Node xs === xs
foldTree :: b -> (b -> a -> b -> b) -> Tree a -> b
foldTree b f = go
  where
    go Leaf = b
    go (Node l x r) = f (go l) x (go r)
{-# INLINE foldTree #-}

-- | The depth of the tree.
-- 
-- >>> depth empty
-- 0
--
-- >>> depth (singleton ())
-- 1
depth :: Tree a -> Int
depth = foldTree 0 (\l _ r -> succ (max l r))

-- | Unfold a tree from a seed.
unfoldTree :: (b -> Maybe (b, a, b)) -> b -> Tree a
unfoldTree f = go
  where
    go = maybe Leaf (\(l, x, r) -> Node (go l) x (go r)) . f

-- | @'replicate' n a@ creates a tree of size @n@ filled @a@.
--
-- >>> putStr (drawTree (replicate 4 ()))
--      ┌()
--   ┌()┘
-- ()┤
--   └()
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
      | even m = liftA3 Node r x (go (d - 1))
      | otherwise = liftA3 Node r x r
      where
        d = m `div` 2
        r = go d

{-# SPECIALISE replicateA :: Int -> Identity a -> Identity (Tree a) #-}
{-# SPECIALISE replicateA :: Int -> State s a -> State s (Tree a) #-}

#if MIN_VERSION_base(4,9,0)
instance Semigroup.Semigroup (Tree a) where
  Leaf <> y = y
  Node x l r <> y = Node x l (r Semigroup.<> y)
#if __GLASGOW_HASKELL__
  {-# INLINABLE (<>) #-}
#endif
#endif

-- | This instance is necessarily inefficient, to obey the monoid laws.
--
-- >>> printTree (fromList [1..6])
--    ┌1
--  ┌2┤
--  │ └3
-- 4┤
--  │ ┌5
--  └6┘
--
-- >>> printTree (fromList [1..6] `mappend` singleton 7)
--    ┌1
--  ┌2┤
--  │ └3
-- 4┤
--  │ ┌5
--  └6┤
--    └7
--
-- 'mappend' distributes over 'toList':
--
-- prop> toList (mappend xs (ys :: Tree Int)) === mappend (toList xs) (toList ys)
instance Monoid (Tree a) where
#if MIN_VERSION_base(4,9,0)
  mappend = (Semigroup.<>)
  {-# INLINE mappend #-}
#else
  mappend Leaf y = y
  mappend (Node l x r) y = Node l x (mappend r y)
#if __GLASGOW_HASKELL__
  {-# INLINABLE mappend #-}
#endif
#endif
  mempty = Leaf

-- | Construct a tree from a list, in an inorder fashion.
--
-- prop> toList (fromList xs) === xs
fromList :: [a] -> Tree a
fromList xs = evalState (replicateA n u) xs
  where
    n = length xs
    u =
      State
        (\ys ->
           case ys of
             [] -> 
#if __GLASGOW_HASKELL__ >= 800
               errorWithoutStackTrace
#else
               error
#endif
               "Data.Tree.Binary.Inorder.fromList: bug!"
             z:zs -> (z, zs))

-- | Convert a tree to a human-readable structural representation.
--
-- >>> putStr (drawTree (fromList [1..7]))
--    ┌1
--  ┌2┤
--  │ └3
-- 4┤
--  │ ┌5
--  └6┤
--    └7
--
drawTree :: Show a => Tree a -> String
drawTree t = drawTreeWith show t ""

-- | Pretty-print a tree with a custom show function.
--
-- >>> putStr (drawTreeWith (const "─") (fromList [1..7]) "")
--    ┌─
--  ┌─┤
--  │ └─
-- ─┤
--  │ ┌─
--  └─┤
--    └─
drawTreeWith :: (a -> String) -> Tree a -> ShowS
drawTreeWith sf = Internal.drawTree sf unc foldTree'
  where
    unc Leaf = Nothing
    unc (Node l x r) = Just (x, l, r)
    foldTree' b f = go where
      go Leaf = b
      go (Node Leaf x Leaf) = f x Nothing Nothing
      go (Node l x Leaf) = f x (Just (go l)) Nothing
      go (Node Leaf x r) = f x Nothing (Just (go r))
      go (Node l x r) = f x (Just (go l)) (Just (go r))
    

-- | Pretty-print a tree.
--
-- >>> printTree (fromList [1..7])
--    ┌1
--  ┌2┤
--  │ └3
-- 4┤
--  │ ┌5
--  └6┤
--    └7
--
printTree :: Show a => Tree a -> IO ()
printTree = putStr . drawTree

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.Foldable (toList)
-- >>> import Prelude (Num(..), putStr)
-- >>> :{
-- instance Arbitrary a =>
--          Arbitrary (Tree a) where
--     arbitrary = sized go
--       where
--         go 0 = pure Leaf
--         go n
--           | n <= 0 = pure Leaf
--           | otherwise = oneof [pure Leaf, liftA3 Node sub arbitrary sub]
--           where
--             sub = go (n `div` 2)
--     shrink Leaf = []
--     shrink (Node l x r) =
--         Leaf : l : r :
--         [ Node l' x' r'
--         | (l',x',r') <- shrink (l, x, r) ]
-- :}
