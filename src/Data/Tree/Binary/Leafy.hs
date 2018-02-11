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
-- Module      : Data.Tree.Binary.Leafy
-- Description : A simple, generic, leafy binary tree.
-- Copyright   : (c) Donnacha Oisín Kidney, 2018
-- License     : MIT
-- Maintainer  : mail@doisinkidney.com
-- Stability   : experimental
-- Portability : portable
--
-- This module provides a simple leafy binary tree, as is needed
-- in several applications. Instances, if sensible, are defined,
-- and generally effort is made to keep the implementation as
-- generic as possible.

module Data.Tree.Binary.Leafy
  ( -- * The tree type
   Tree(..)
   -- * Construction
  , unfoldTree
  , replicate
  , replicateA
  , singleton
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

import Control.Applicative (Applicative(..), liftA2)

import Control.DeepSeq (NFData(rnf))

import Data.Monoid (Monoid(mappend))
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

import Control.Monad.Fix (MonadFix(..), fix)

import qualified Data.Tree.Binary.Internal as Internal
import Data.Tree.Binary.Internal (Identity(..), State(..), evalState)

#if __GLASGOW_HASKELL__ >= 800
import GHC.Stack (HasCallStack)
#endif

-- | A leafy binary tree.
infixl 5 :*:
data Tree a
  = Leaf a
  | Tree a :*: Tree a
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
  fmap f (Leaf x) = Leaf (f x)
  fmap f (xs :*: ys) = fmap f xs :*: fmap f ys
#if __GLASGOW_HASKELL__
  {-# INLINABLE fmap #-}
#endif
  x <$ xs = go xs where
    go (Leaf _) = Leaf x
    go (ls :*: rs) = go ls :*: go rs
  {-# INLINE (<$) #-}

instance Applicative Tree where
  pure = Leaf
  {-# INLINE pure #-}
  Leaf f <*> xs = fmap f xs
  (fs :*: gs) <*> xs = (fs <*> xs) :*: (gs <*> xs)
#if __GLASGOW_HASKELL__
  {-# INLINABLE (<*>) #-}
#endif
#if MIN_VERSION_base(4,10,0)
  liftA2 f = go where
    go (Leaf x) ys = fmap (f x) ys
    go (xl :*: xr) ys = go xl ys :*: go xr ys
  {-# INLINE liftA2 #-}
#endif
#if MIN_VERSION_base(4,2,0)
  Leaf _ *> ys = ys
  (xl :*: xr) *> ys = (xl *> ys) :*: (xr *> ys)
  Leaf x <* ys = x <$ ys
  (xl :*: xr) <* ys = (xl <* ys) :*: (xr <* ys)
#if __GLASGOW_HASKELL__
  {-# INLINABLE (*>) #-}
  {-# INLINABLE (<*) #-}
#endif
#endif

instance Monad Tree where
  Leaf x >>= f = f x
  (xl :*: xr) >>= f = (xl >>= f) :*: (xr >>= f)
#if __GLASGOW_HASKELL__
  {-# INLINABLE (>>=) #-}
#endif

instance MonadFix Tree where
  mfix f = case fix (f . head') of
    Leaf x -> Leaf x
    xs :*: _ -> cons' (head' xs) (mfix (tail' . f))
    where
      head' (Leaf x) = x
      head' (xs :*: _) = head' xs
      cons' x xs = Leaf x :*: xs
      tail' (Leaf _ :*: ys) = ys
      tail' ((xs :*: ys) :*: zs) = (tail' xs :*: ys) :*: zs
      tail' _ =
#if __GLASGOW_HASKELL__ >= 800
        errorWithoutStackTrace
#else
        error
#endif
        "Data.Tree.Binary.Leafy.mfix: Empty tree"

#if MIN_VERSION_base(4,9,0)
instance Semigroup.Semigroup (Tree a) where
  xs@(Leaf _) <> ys = xs :*: ys
  (xl :*: xr) <> ys = xl :*: (xr Semigroup.<> ys)
#if __GLASGOW_HASKELL__
  {-# INLINABLE (<>) #-}
#endif
#endif

instance Foldable Tree where
  foldr f b (Leaf x) = f x b
  foldr f b (xs :*: ys) = foldr f (foldr f b ys) xs

  foldl f b (Leaf x) = f b x
  foldl f b (xs :*: ys) = foldl f (foldl f b xs) ys

  foldMap f (Leaf x) = f x
  foldMap f (xs :*: ys) = foldMap f xs `mappend` foldMap f ys

#if __GLASGOW_HASKELL__
  {-# INLINABLE foldr #-}
  {-# INLINABLE foldl #-}
  {-# INLINABLE foldMap #-}
#endif

#if MIN_VERSION_base(4,6,0)
  foldr' f !b (Leaf x) = f x b
  foldr' f !b (xs :*: ys) = case foldr' f b ys of
    !b' -> foldr' f b' xs

  foldl' f !b (Leaf x) = f b x
  foldl' f !b (xs :*: ys) = case foldl' f b xs of
    !b' -> foldl' f b' ys
#if __GLASGOW_HASKELL__
  {-# INLINABLE foldr' #-}
  {-# INLINABLE foldl' #-}
#endif
#endif

instance Traversable Tree where
  traverse f (Leaf x) = fmap Leaf (f x)
  traverse f (xs :*: ys) = liftA2 (:*:) (traverse f xs) (traverse f ys)
#if __GLASGOW_HASKELL
  {-# INLINABLE traverse #-}
#endif

-- | A binary tree with one element.
singleton :: a -> Tree a
singleton = Leaf
{-# INLINE singleton #-}

instance NFData a => NFData (Tree a) where
  rnf (Leaf x) = rnf x
  rnf (xs :*: ys) = rnf xs `seq` rnf ys

#if MIN_VERSION_base(4,9,0)
instance Eq1 Tree where
  liftEq eq (Leaf x) (Leaf y) = eq x y
  liftEq eq (xl :*: xr) (yl :*: yr) = liftEq eq xl yl && liftEq eq xr yr
  liftEq _ _ _ = False

instance Ord1 Tree where
  liftCompare cmp (Leaf x) (Leaf y) = cmp x y
  liftCompare cmp (xl :*: xr) (yl :*: yr) =
    liftCompare cmp xl yl `mappend` liftCompare cmp xr yr
  liftCompare _ (Leaf _) (_ :*: _) = LT
  liftCompare _ (_ :*: _) (Leaf _) = GT

instance Show1 Tree where
  liftShowsPrec s _ = go
    where
      go d (Leaf x) = showParen (d >= 11) $ showString "Leaf " . s 11 x
      go d (xs :*: ys) =
        showParen (d > 5) $ go 6 xs . showString " :*: " . go 6 ys

instance Read1 Tree where
#if MIN_VERSION_base(4,10,0) && __GLASGOW_HASKELL__
  liftReadPrec rp _ = go
    where
      go =
        parens $
        prec 10 (expect' (Ident "Leaf") *> fmap Leaf (step rp)) +++
        prec 5 (liftA2 (:*:) (step go) (expect' (Symbol ":*:") *> step go))
      expect' = lift . expect
  liftReadListPrec = liftReadListPrecDefault
#else
  liftReadsPrec rp _ = go
    where
      go p st =
        readParen
          (p > 10)
          (\xs -> [(Leaf x, zs) | ("Leaf", ys) <- lex xs, (x, zs) <- rp 11 ys])
          st ++
        readParen
          (p > 5)
          (\ws ->
             [ (x :*: y, zs)
             | (x, xs) <- go 6 ws
             , (":*:", ys) <- lex xs
             , (y, zs) <- go 6 ys
             ])
          st
#endif
#endif

-- | Fold over a tree.
--
-- prop> foldTree Leaf (:*:) xs === xs
foldTree :: (a -> b) -> (b -> b -> b) -> Tree a -> b
foldTree b f = go
  where
    go (Leaf x) = b x
    go (xs :*: ys) = go xs `f` go ys
{-# INLINE foldTree #-}

-- | The depth of the tree.
--
-- >>> depth (singleton ())
-- 1
depth :: Tree a -> Int
depth = foldTree (const 1) (\x y -> succ (max x y))

-- | Unfold a tree from a seed.
unfoldTree :: (b -> Either a (b, b)) -> b -> Tree a
unfoldTree f = go
  where
    go = either Leaf (\(l,r) -> go l :*: go r) . f

-- | @'replicate' n a@ creates a tree of size @n@ filled with @a@.
--
-- >>> printTree (replicate 4 ())
--  ┌()
-- ┌┤
-- │└()
-- ┤
-- │┌()
-- └┤
--  └()
--
--  prop> \(Positive n) -> length (replicate n ()) === n
replicate :: Int -> a -> Tree a
replicate n x = runIdentity (replicateA n (Identity x))

-- | @'replicateA' n a@ replicates the action @a@ @n@ times, trying
-- to balance the result as much as possible. The actions are executed
-- in the same order as the 'Foldable' instance.
--
-- >>> toList (evalState (replicateA 10 (State (\s -> (s, s + 1)))) 1)
-- [1,2,3,4,5,6,7,8,9,10]
replicateA :: Applicative f => Int -> f a -> f (Tree a)
replicateA n x = go n
  where
    go m
      | m <= 1 = fmap Leaf x
      | even m = liftA2 (:*:) r r
      | otherwise = liftA2 (:*:) r (go (d+1))
      where
        d = m `div` 2
        r = go d
{-# SPECIALISE replicateA :: Int -> Identity a -> Identity (Tree a) #-}
{-# SPECIALISE replicateA :: Int -> State s a -> State s (Tree a) #-}

-- | Construct a tree from a list.
#if __GLASGOW_HASKELL__ >= 800
fromList :: HasCallStack => [a] -> Tree a
#else
fromList :: [a] -> Tree a
#endif
fromList [] = error "Data.Tree.Binary.Leafy.fromList: empty list!"
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
               "Data.Tree.Binary.Leafy.fromList: bug!"
             z:zs -> (z, zs))


-- | Convert a tree to a human-readable structural representation.
--
-- >>> putStr (drawTree (Leaf 1 :*: Leaf 2 :*: Leaf 3))
--  ┌1
-- ┌┤
-- │└2
-- ┤
-- └3
drawTree :: Show a => Tree a -> String
drawTree t = drawTreeWith show t ""

-- | Pretty-print a tree with a custom show function.
drawTreeWith :: (a -> String) -> Tree a -> ShowS
drawTreeWith sf = Internal.drawTree (maybe "" sf) (fmap uncons') . Just
  where
    uncons' (xl :*: xr) = (Nothing, Just xl, Just xr)
    uncons' (Leaf x) = (Just x, Nothing, Nothing)

-- | Pretty-print a tree
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
--         go n
--           | n <= 0 = fmap Leaf arbitrary
--           | otherwise = oneof [fmap Leaf arbitrary, liftA2 (:*:) sub sub]
--           where
--             sub = go (n `div` 2)
--     shrink (Leaf x) = fmap Leaf (shrink x)
--     shrink (l :*: r) =
--         l : r :
--         [ l' :*: r'
--         | (l',r') <- shrink (l, r) ]
-- :}
