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
-- Module      : Data.Tree.Binary.Preorder
-- Description : A simple, generic, preorder binary tree.
-- Copyright   : (c) Donnacha Oisín Kidney, 2018
-- License     : MIT
-- Maintainer  : mail@doisinkidney.com
-- Stability   : experimental
-- Portability : portable
--
-- This module provides a simple preorder binary tree, as is needed
-- in several application. Instances, if sensible, are defined,
-- and generally effort is made to keep the implementation as
-- generic as possible.

module Data.Tree.Binary.Preorder
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
  , printTree
  ) where

import Prelude
  ( Eq

  , Bool(..)
  , otherwise
  , (&&)

  , Ord((<=), (>=), max)
  , Ordering(..)

  , Read
  , Show
  , String
  , showString
  , showChar
  , showParen

  , putStrLn
  , IO

  , Maybe
  , maybe

  , length

  , Int
  , Num((-))
  , Enum(succ)
  , Integral(div)
  , even

#if __GLASGOW_HASKELL__ >= 800
  , errorWithoutStackTrace
#else
  , error
#endif
  , seq

  , (.)
  , ($)
  )


import Control.Applicative (Applicative(pure, (*>)), liftA3)

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

import Data.Traversable (Traversable(..))

import Data.Typeable (Typeable)

#if __GLASGOW_HASKELL__ >= 706
import GHC.Generics (Generic, Generic1)
#elif __GLASGOW_HASKELL__ >= 702
import GHC.Generics (Generic)
#endif

import Text.Read

#if __GLASGOW_HASKELL__
import Data.Data (Data)
import qualified Text.Read.Lex as Lex
#endif

import qualified Data.Tree.Binary.Internal as Internal
import Data.Tree.Binary.Internal (State(..), evalState, Identity(..))

-- | A preorder binary tree.
data Tree a
  = Leaf
  | Node a
         (Tree a)
         (Tree a)
  deriving (Show, Read, Eq, Ord
#if __GLASGOW_HASKELL__
  , Typeable, Data
#endif 
#if __GLASGOW_HASKELL__ >= 702
  , Generic, Generic1
#endif
  )

instance Functor Tree where
  fmap _ Leaf = Leaf
  fmap f (Node x l r) = Node (f x) (fmap f l) (fmap f r)

instance Foldable Tree where
  foldr _ b Leaf = b
  foldr f b (Node x l r) = f x (foldr f (foldr f b r) l)

  foldl _ b Leaf = b
  foldl f b (Node x l r) = foldl f (foldl f (f b x) l) r

  foldMap _ Leaf = mempty
  foldMap f (Node x l r) = f x `mappend` foldMap f l `mappend` foldMap f r

#if __GLASGOW_HASKELL__
  {-# INLINABLE foldMap #-}
  {-# INLINABLE foldr #-}
  {-# INLINABLE foldl #-}
#endif


#if MIN_VERSION_base(4,6,0)
  foldr' _ !b Leaf = b
  foldr' f !b (Node x l r) = case foldr' f b r of
    !b' -> case foldr' f b' l of
      !b'' -> f x b''

  foldl' _ !b Leaf = b
  foldl' f !b (Node x l r) = case f b x of
    !b' -> case foldl' f b' l of
      !b'' -> foldl' f b'' r
#if __GLASGOW_HASKELL__
  {-# INLINABLE foldr' #-}
  {-# INLINABLE foldl' #-}
#endif
#endif

instance Traversable Tree where
  traverse _ Leaf = pure Leaf
  traverse f (Node x l r) = liftA3 Node (f x) (traverse f l) (traverse f r)
#if __GLASGOW_HASKELL__
  {-# INLINABLE traverse #-}
#endif

-- | A binary tree with one element.
singleton :: a -> Tree a
singleton x = Node x Leaf Leaf

{-# INLINE singleton #-}
-- | A binary tree with no elements.
empty :: Tree a
empty = Leaf

{-# INLINE empty #-}
instance NFData a => NFData (Tree a) where
  rnf Leaf = ()
  rnf (Node x l r) = rnf x `seq` rnf l `seq` rnf r

#if MIN_VERSION_base(4,9,0)
instance Eq1 Tree where
  liftEq _ Leaf Leaf = True
  liftEq eq (Node x xl xr) (Node y yl yr) =
    eq x y && liftEq eq xl yl && liftEq eq xr yr
  liftEq _ _ _ = False

instance Ord1 Tree where
  liftCompare _ Leaf Leaf = EQ
  liftCompare cmp (Node x xl xr) (Node y yl yr) =
    cmp x y `mappend` liftCompare cmp xl yl `mappend` liftCompare cmp xr yr
  liftCompare _ Leaf _ = LT
  liftCompare _ _ Leaf = GT

instance Show1 Tree where
  liftShowsPrec s _ = go
    where
      go _ Leaf = showString "Leaf"
      go d (Node x l r) =
        showParen (d >= 11) $
        showString "Node " .
        s 11 x . showChar ' ' . go 11 l . showChar ' ' . go 11 r

instance Read1 Tree where
#if MIN_VERSION_base(4,10,0) && __GLASGOW_HASKELL__
  liftReadPrec rp _ = go
    where
      go =
        parens $
        prec 10 (Leaf <$ expect' (Ident "Leaf")) +++
        prec
          10
          (expect' (Ident "Node") *> liftA3 Node (step rp) (step go) (step go))
      expect' = lift . Lex.expect
  liftReadListPrec = liftReadListPrecDefault
#else
  liftReadsPrec rp _ = go
    where
      go p st =
        [(Leaf, xs) | ("Leaf", xs) <- lex st] ++
        readParen
          (p > 10)
          (\vs ->
             [ (Node x l r, zs)
             | ("Node", ws) <- lex vs
             , (x, xs) <- rp 11 ws
             , (l, ys) <- go 11 xs
             , (r, zs) <- go 11 ys
             ])
          st
#endif
#endif

-- | Fold over a tree.
--
-- prop> foldTree Leaf Node xs === xs
foldTree :: b -> (a -> b -> b -> b) -> Tree a -> b
foldTree b f = go
  where
    go Leaf = b
    go (Node x l r) = f x (go l) (go r)

-- | The depth of the tree.
--
-- >>> depth empty
-- 0
--
-- >>> depth (singleton ())
-- 1
depth :: Tree a -> Int
depth = foldTree 0 (\_ l r -> succ (max l r))

-- | Unfold a tree from a seed.
unfoldTree :: (b -> Maybe (a, b, b)) -> b -> Tree a
unfoldTree f = go
  where
    go = maybe Leaf (\(x, l, r) -> Node x (go l) (go r)) . f

-- | @'replicate' n a@ creates a tree of size @n@ filled @a@.
--
-- >>> putStr (drawTree (replicate 4 ()))
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
      | even m = liftA3 Node x r (go (d - 1))
      | otherwise = liftA3 Node x r r
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
--    1
--  2   5
-- 3 4 6
--
-- >>> printTree (fromList [1..6] `mappend` singleton 7)
--    1
--  2   5
-- 3 4 6 7
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
  mappend (Node x l r) y = Node x l (mappend r y)
#if __GLASGOW_HASKELL__
  {-# INLINABLE mappend #-}
#endif
#endif
  mempty = Leaf

-- | Construct a tree from a list, in an preorder fashion.
--
-- prop> toList (fromList xs) === xs
fromList :: [a] -> Tree a
fromList xs = evalState (replicateA n u) xs
  where
    n = Prelude.length xs
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
               "Data.Tree.Binary.Preorder.fromList: bug!"
             z:zs -> (z, zs))

-- | Convert a tree to a human-readable structural representation.
--
-- >>> putStr (drawTree (fromList [1..7]))
--    1
--  2   5
-- 3 4 6 7
drawTree :: Show a => Tree a -> String
drawTree = Internal.drawBinaryTree foldTree

-- | Pretty-print a tree.
--
-- >>> printTree (fromList [1..7])
--    1
--  2   5
-- 3 4 6 7
printTree :: Show a => Tree a -> IO ()
printTree = putStrLn . drawTree

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
--           | otherwise = oneof [pure Leaf, liftA3 Node arbitrary sub sub]
--           where
--             sub = go (n `div` 2)
--     shrink Leaf = []
--     shrink (Node x l r) =
--         Leaf : l : r :
--         [ Node x' l' r'
--         | (x',l',r') <- shrink (x, l, r) ]
-- :}
