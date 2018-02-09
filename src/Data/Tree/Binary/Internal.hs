{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 703
{-# LANGUAGE Safe #-}
#endif

-- |
-- Module      : Data.Tree.Binary.Internal
-- Description : Common utility functions for the binary-tree package.
-- Copyright   : (c) Donnacha Oisín Kidney 2018
-- License     : MIT
-- Maintainer  : mail@doisinkidney.com
-- Portability : portable
--
-- = WARNING
-- 
-- This module is considered __internal__.
-- 
-- The Package Versioning Policy __does not apply__.
-- 
-- This contents of this module may change __in any way whatsoever__
-- and __without any warning__ between minor versions of this package.
-- 
-- Authors importing this module are expected to track development
-- closely.
-- 
-- = Description
--
-- This module exports some utility functions common to both tree modules.
module Data.Tree.Binary.Internal
  ( drawTree
  , Identity(..)
  , State(..)
  , evalState
  ) where

import Prelude hiding (
#if MIN_VERSION_base(4,8,0)
  Functor(..),Applicative, (<$>), foldMap, Monoid
#endif
  )

#if MIN_VERSION_base(4,8,0)
import Data.Functor.Identity (Identity(..))
#endif

import Data.Functor (Functor(fmap))
import Control.Applicative (Applicative((<*>), pure))

--------------------------------------------------------------------------------
-- Drawing Trees
--------------------------------------------------------------------------------
data Padding =
  Padding {-# UNPACK #-}!Int
          Prefix

data Prefix
  = Nil
  | Prefix String
           Padding

data LevelBuilder = LevelBuilder
  { _offset :: {-# UNPACK #-}!Int
  , levels :: [Padding -> Padding]
  }

-- | Given a folding function for a binary tree, draw the tree in a structured,
-- human-readable way.
drawTree ::
     Show a
  => (LevelBuilder -> (a -> LevelBuilder -> LevelBuilder -> LevelBuilder) -> b -> LevelBuilder)
  -> b
  -> String
drawTree ft = runLevels . levels . ft (LevelBuilder 0 []) f
  where
    f xv (LevelBuilder llen lb) (LevelBuilder rlen rb) =
      LevelBuilder
        (llen + rlen + xlen)
        ((Padding llen . Prefix xshw . cons rlen) : zipLongest lb rb)
      where
        xshw = show xv
        xlen = length xshw
        zipLongest (x:xs) (y:ys) = (x . cons xlen . y) : zipLongest xs ys
        zipLongest [] ys = map (cons (llen + xlen) .) ys
        zipLongest xs [] = map (. cons (rlen + xlen)) xs

cons :: Int -> Padding -> Padding
cons i (Padding j xs) = Padding (i + j) xs

nil :: Padding
nil = Padding 0 Nil

runLevels :: [Padding -> Padding] -> String
runLevels [] = ""
runLevels (x:xs) =
  runLevel (x nil) (foldr (\e a -> '\n' : runLevel (e nil) a) "" xs)

runLevel :: Padding -> String -> String
runLevel (Padding n xs) = pad n . f xs
  where
    pad 0 = id
    pad m = (' ' :) . pad (m - 1)
    f Nil = id
    f (Prefix s ys) = (s ++) . runLevel ys

--------------------------------------------------------------------------------
-- State
--------------------------------------------------------------------------------

-- | A clone of Control.Monad.State.Strict, reimplemented here to avoid the
-- dependency.
newtype State s a = State
  { runState :: s -> (a, s)
  }

instance Functor (State s) where
  fmap f xs =
    State
      (\s ->
         case runState xs s of
           (x, s') -> (f x, s'))
  {-# INLINE fmap #-}

instance Applicative (State s) where
  pure x = State (\s -> (x, s))
  {-# INLINE pure #-}
  fs <*> xs =
    State
      (\s ->
         case runState fs s of
           (f, s') ->
             case runState xs s' of
               (x, s'') -> (f x, s''))
  {-# INLINE (<*>) #-}

-- | Evaluate a stateful action.
evalState :: State s a -> s -> a
evalState xs s = fst (runState xs s)
{-# INLINE evalState #-}

--------------------------------------------------------------------------------
-- Identity
--------------------------------------------------------------------------------
#if !MIN_VERSION_base(4,8,0)
-- | A clone of Data.Functor.Identity, reimplemented here when it's not yet
-- included in base.
newtype Identity a = Identity {runIdentity :: a}

instance Functor Identity where
  fmap f (Identity x) = Identity (f x)

instance Applicative Identity where
  pure = Identity
  Identity f <*> Identity x = Identity (f x)
#endif
