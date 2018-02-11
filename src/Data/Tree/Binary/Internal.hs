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

#if MIN_VERSION_base(4,7,0)
import Data.Bool (bool)
#else
bool :: a -> a -> Bool -> a
bool f _ False = f
bool _ t True  = t
#endif

--------------------------------------------------------------------------------
-- Drawing Trees
--------------------------------------------------------------------------------

-- | Given an uncons function for a binary tree, draw the tree in a structured,
-- human-readable way.
drawTree :: (a -> String) -> (t -> Maybe (a, t, t)) -> t -> ShowS
drawTree sf project = maybe nd root . project
  where
    go (x, l, r) = node x (fmap go (project l)) (fmap go (project r))

    -- Root special case (no incoming direction)
    root (x, l, r) =
      maybe id (\t -> go t True id xlen) ls .
      showString xshw .
      endc ls rs .
      nl . maybe id (\t -> go t False id xlen) rs
      where
        xshw = sf x
        xlen = length xshw
        ls = project l
        rs = project r

    -- Item -> 
    -- Left result -> 
    -- Right result -> 
    -- Incoming dir -> 
    -- Padding -> 
    -- Offset -> 
    -- Result
    node x ls rs up k i =
      maybe id (branch True) ls .
      k .  pad i . bool bl tl up . showString xshw . endc ls rs . nl . 
      maybe id (branch False) rs
      where
        xshw = sf x
        xlen = length xshw
        branch d fn
          | d == up = fn d (k . pad i) (xlen + 1)
          | otherwise = fn d (k . pad i . vm) xlen

    endc Nothing Nothing = id
    endc (Just _) Nothing = br
    endc Nothing (Just _) = tr
    endc (Just _) (Just _) = rt
    
    pad 0 = id
    pad n = sp . pad (n - 1)

    -- Characters
    nl = showChar '\n'
    bl = showChar '└'
    br = showChar '┘'
    tl = showChar '┌'
    tr = showChar '┐'
    vm = showChar '│'
    rt = showChar '┤'
    sp = showChar ' '
    nd = showChar '╼'

{-# INLINE drawTree #-}

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
