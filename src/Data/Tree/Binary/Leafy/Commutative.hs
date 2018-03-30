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

#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE PatternSynonyms #-}
#endif

module Data.Tree.Binary.Leafy.Commutative
  (Tree(Leaf)
#if __GLASGOW_HASKELL__ >= 800
  ,pattern (:&:)
  ,pattern (:*:)
#else
  , (&:)
#endif
  ,unconsTree)
  where

import Prelude hiding
  ( replicate
#if MIN_VERSION_base(4,8,0)
  ,Functor(..),Foldable(..),Applicative, (<$>), foldMap, Monoid
#else
  ,foldr,foldl
#endif
  )

import Control.DeepSeq (NFData(rnf))

#if MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable(foldl, foldr, foldMap, foldl', foldr', null))
#elif MIN_VERSION_base(4,6,0)
import Data.Foldable (Foldable(foldl, foldr, foldMap, foldl', foldr'))
#else
import Data.Foldable (Foldable(foldl, foldr, foldMap))
#endif

#if __GLASGOW_HASKELL__
import Data.Data (Data)
#endif

import Data.Typeable (Typeable)

#if __GLASGOW_HASKELL__ >= 706
import GHC.Generics (Generic, Generic1)
#elif __GLASGOW_HASKELL__ >= 702
import GHC.Generics (Generic)
#endif

#if MIN_VERSION_base(4,9,0)
import Data.Functor.Classes
import qualified Data.Semigroup as Semigroup
#endif

-- | A leafy binary tree, where the only exported constructors are
-- commutative.
data Tree a
    = Leaf a
    | Branch (Tree a)
             (Tree a)
    deriving (Eq,Ord
#if __GLASGOW_HASKELL__ >= 706
  , Typeable, Data, Generic, Generic1
#elif __GLASGOW_HASKEL__ >= 702
  , Typeable, Data, Generic
#elif __GLASGOW_HASKELL__
  , Typeable, Data
#endif
  )

#if __GLASGOW_HASKELL__ >= 800
infixl 5 :&:
pattern (:&:) :: Ord a => Tree a -> Tree a -> Tree a
pattern xs :&: ys <- Branch xs ys
  where xs :&: ys
          | xs <= ys = Branch xs ys
          | otherwise = Branch ys xs
{-# COMPLETE Leaf, (:&:) #-}

infixl 5 :*:
pattern (:*:) :: Tree a -> Tree a -> Tree a
pattern xs :*: ys <- Branch xs ys
{-# COMPLETE Leaf, (:*:) #-}
#endif

infixl 5 &:
(&:) :: Ord a => Tree a -> Tree a -> Tree a
xs &: ys | xs <= ys = Branch xs ys
         | otherwise = Branch ys xs

#if MIN_VERSION_base(4,9,0)
instance Ord a => Semigroup.Semigroup (Tree a) where
  xs@(Leaf _) <> ys = xs &: ys
  (Branch xl xr) <> ys = xl &: (xr Semigroup.<> ys)
#if __GLASGOW_HASKELL__
  {-# INLINABLE (<>) #-}
#endif
#endif

unconsTree :: Tree a -> Either a (Tree a, Tree a)
unconsTree (Leaf x) = Left x
unconsTree (Branch xs ys) = Right (xs,ys)

instance Show a =>
         Show (Tree a) where
#if MIN_VERSION_base(4,9,0)
    showsPrec = showsPrec1
#else
    showsPrec d (Leaf x) =
        showParen (d >= 11) $ showString "Leaf " . showsPrec 11 x
    showsPrec d (Branch xs ys) =
        showParen (d > 5) $ showsPrec 6 xs . showString " :&: " . showsPrec 6 ys
#endif

instance Foldable Tree where
  foldr f b (Leaf x) = f x b
  foldr f b (Branch xs ys) = foldr f (foldr f b ys) xs

  foldl f b (Leaf x) = f b x
  foldl f b (Branch xs ys) = foldl f (foldl f b xs) ys

  foldMap f (Leaf x) = f x
  foldMap f (Branch xs ys) = foldMap f xs `mappend` foldMap f ys

#if __GLASGOW_HASKELL__
  {-# INLINABLE foldr #-}
  {-# INLINABLE foldl #-}
  {-# INLINABLE foldMap #-}
#endif

#if MIN_VERSION_base(4,6,0)
  foldr' f !b (Leaf x) = f x b
  foldr' f !b (Branch xs ys) = case foldr' f b ys of
    !b' -> foldr' f b' xs

  foldl' f !b (Leaf x) = f b x
  foldl' f !b (Branch xs ys) = case foldl' f b xs of
    !b' -> foldl' f b' ys
#if __GLASGOW_HASKELL__
  {-# INLINABLE foldr' #-}
  {-# INLINABLE foldl' #-}
#endif
#endif

#if MIN_VERSION_base(4,8,0)
  null _ = False
  {-# INLINE null #-}
#endif

instance NFData a => NFData (Tree a) where
  rnf (Leaf x) = rnf x
  rnf (Branch xs ys) = rnf xs `seq` rnf ys

#if MIN_VERSION_base(4,9,0)
instance Eq1 Tree where
  liftEq eq (Leaf x) (Leaf y) = eq x y
  liftEq eq (Branch xl xr) (Branch yl yr) = liftEq eq xl yl && liftEq eq xr yr
  liftEq _ _ _ = False

instance Ord1 Tree where
  liftCompare cmp (Leaf x) (Leaf y) = cmp x y
  liftCompare cmp (Branch xl xr) (Branch yl yr) =
    liftCompare cmp xl yl `mappend` liftCompare cmp xr yr
  liftCompare _ (Leaf _) (Branch _ _) = LT
  liftCompare _ (Branch _  _) (Leaf _) = GT

instance Show1 Tree where
    liftShowsPrec s _ = go
      where
        go d (Leaf x) = showParen (d >= 11) $ showString "Leaf " . s 11 x
        go d (Branch xs ys) =
            showParen (d > 5) $ go 6 xs . showString " :&: " . go 6 ys
#endif

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.Foldable (toList, length)
-- >>> import Prelude (Num(..), putStr)
-- >>> import Data.Tree.Binary.Internal (evalState, State(..))
-- >>> import Data.Functor (fmap)
-- >>> import Control.Applicative (liftA2)
-- >>> :{
-- instance (Arbitrary a, Ord a) =>
--          Arbitrary (Tree a) where
--     arbitrary = sized go
--       where
--         go n
--           | n <= 0 = fmap Leaf arbitrary
--           | otherwise = oneof [fmap Leaf arbitrary, liftA2 (&:) sub sub]
--           where
--             sub = go (n `div` 2)
--     shrink (Leaf x) = fmap Leaf (shrink x)
--     shrink (l :&: r) =
--         l : r :
--         [ l' :&: r'
--         | (l',r') <- shrink (l, r) ]
-- :}
