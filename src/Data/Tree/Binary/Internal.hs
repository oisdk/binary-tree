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
-- Base Functor For Recursion Scheme
--------------------------------------------------------------------------------

newtype TreeF a r = TreeF { runTreeF :: Maybe (a, r, r) }

instance Functor (TreeF a) where
  fmap f (TreeF Nothing) = TreeF Nothing
  fmap f (TreeF (Just (x,l,r))) = TreeF (Just (x, f l, f r))

--------------------------------------------------------------------------------
-- Drawing Trees
--------------------------------------------------------------------------------

-- | Given a folding function for a binary tree, draw the tree in a structured,
-- human-readable way.
drawTree ::
     (a -> String)
  -> (t -> Maybe (a, t, t))
  -> t
  -> ShowS
drawTree sf project = firstLevel . project
  where
    ft = maybe b ftc . project
    ftc (x,l,r) = f x (fmap ftc (project l)) (fmap ftc (project r))
    firstLevel Nothing = showChar '╼'
    firstLevel (Just (x, l', r')) = ls . showString xshw . crn . showChar '\n' . rs where
      xshw = sf x
      xlen = length xshw
      ls' = project l'
      rs' = project r'
      ls = maybe id (\t -> ftc t True  id xlen) ls'
      rs = maybe id (\t -> ftc t False id xlen) rs'
      crn = case (ls',rs') of 
        (Nothing,Nothing) -> id
        (Just _ ,Nothing) -> showChar '┘'
        (Nothing,Just _ ) -> showChar '┐'
        (Just _ ,Just _ ) -> showChar '┤'
    b _ k _ = k . showChar '\n'
    branch k i j d u =
      maybe
        id
        (\fn ->
           if d == u
             then fn d (k . pad i) j
             else fn d (k . pad i . showChar '│') (j - 1))
    f x ls' rs' up k i = ls . k . pad i . corn . xshs . showChar '\n' . rs
      where
        corn
          | up = showChar '┌'
          | otherwise = showChar '└'
        xshw = sf x
        xlen = length xshw
        endc Nothing Nothing = (xlen, id)
        endc (Just _) Nothing = (xlen + 1 , showChar '┘')
        endc Nothing (Just _) = (xlen + 1 , showChar '┐')
        endc (Just _) (Just _) = (xlen + 1, showChar '┤')
        (j, eshs) = endc ls' rs'
        xshs = showString xshw . eshs
        ls = branch k i j True up ls'
        rs = branch k i j False up rs'
    pad 0 = id
    pad n = showChar ' ' . pad (n - 1)

{-# INLINE drawTree #-}

type Base = (Bool -> ShowS -> Int -> ShowS) 

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
