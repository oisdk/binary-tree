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

bool :: a -> a -> Bool -> a
bool f _ False = f
bool _ t True  = t
{-# INLINE bool #-}

--------------------------------------------------------------------------------
-- Drawing Trees
--------------------------------------------------------------------------------

data Drawing
  = Nil
  | NewLine     !Drawing
  | BottomLeft  !Drawing
  | BottomRight !Drawing
  | TopLeft     !Drawing
  | TopRight    !Drawing
  | Vert        !Drawing
  | Split       !Drawing
  | Item !String Drawing
  | Padding {-# UNPACK #-} !Int !Drawing

runDrawing :: Drawing -> ShowS
runDrawing Nil = showChar '╼'
runDrawing ys = go ys
  where
    go Nil st = st
    go (NewLine     xs) st = '\n' : go xs st
    go (BottomLeft  xs) st = '└' : go xs st
    go (BottomRight xs) st = '┘' : go xs st
    go (TopLeft     xs) st = '┌' : go xs st
    go (TopRight    xs) st = '┐' : go xs st
    go (Vert        xs) st = '│' : go xs st
    go (Split       xs) st = '┤' : go xs st
    go (Item x      xs) st = x ++ go xs st
    go (Padding i   xs) st = pad i (go xs st)
    pad 0 = id
    pad n = showChar ' ' . pad (n-1)

-- | Given an uncons function for a binary tree, draw the tree in a structured,
-- human-readable way.
drawTree :: (a -> String) -> (t -> Maybe (a, t, t)) -> t -> ShowS
drawTree sf project = runDrawing . maybe Nil root . project
  where
    go (x, l, r) = node x (project l) (project r)

    -- Root special case (no incoming direction)
    root (x, l, r) =
      maybeAp (\t -> go t True id xlen) ls $
      Item xshw $
      endc ls rs $
      NewLine $ maybeAp (\t -> go t False id xlen) rs $ Nil
      where
        xshw = sf x
        xlen = length xshw
        ls = project l
        rs = project r

    node x ls rs up k i b =
      maybeAp (branch True) ls $
      k $
      pad i $
      bool BottomLeft TopLeft up $
      Item xshw $ endc ls rs $ NewLine $ maybeAp (branch False) rs b
      where
        xshw = sf x
        xlen = length xshw
        branch d fn
          | d == up = go fn d (k . pad i) (xlen + 1)
          | otherwise = go fn d (k . pad i . Vert) xlen
        {-# INLINE branch #-}
    {-# INLINE node #-}

    endc Nothing  Nothing  b = b
    endc (Just _) Nothing  b = BottomRight b
    endc Nothing  (Just _) b = TopRight b
    endc (Just _) (Just _) b = Split b
    {-# INLINE endc #-}
    
    pad i (Padding j xs) = Padding (i+j) xs
    pad i xs = Padding i xs
    {-# INLINE pad #-}

    maybeAp _ Nothing y = y
    maybeAp f (Just x) y = f x y
    {-# INLINE maybeAp #-}

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
