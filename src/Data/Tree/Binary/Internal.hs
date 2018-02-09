{-# LANGUAGE CPP #-}

module Data.Tree.Binary.Internal
  ( drawBinaryTree
  , Identity(..)
  , State(..)
  , evalState
  ) where

import Prelude hiding (
  unlines
#if MIN_VERSION_base(4,8,0)
  ,Functor(..),Foldable(..),Applicative, (<$>), foldMap, Monoid
#endif
  )

#if MIN_VERSION_base(4,8,0)
import Data.Functor.Identity (Identity(..))
import Data.Functor (Functor(fmap))
#endif

import Control.Applicative (Applicative((<*>), pure))
import Data.Monoid (Monoid(mappend, mempty))

data LevelBuilder = LevelBuilder
  { _offset :: {-# UNPACK #-} !Int
  , levels :: [Level]
  }

data Level
  = Nil
  | Padding {-# UNPACK #-} !Int Level
  | Prefix (String -> String) Level

runLevel :: Level -> String -> String
runLevel Nil st = st
runLevel (Padding p xs) st = replicate p ' ' ++ runLevel xs st
runLevel (Prefix p xs) st = p (runLevel xs st)

instance Monoid Level where
  mempty = Nil
  mappend (Padding x Nil) (Padding y ys) = Padding (x + y) ys
  mappend (Prefix x Nil) (Prefix y ys) = Prefix (x . y) ys
  mappend (Padding x xs) ys = Padding x (mappend xs ys)
  mappend (Prefix x xs) ys = Prefix x (mappend xs ys)
  mappend Nil ys = ys

padding :: Int -> Level -> Level
padding 0 ys = ys
padding n (Padding y ys) = Padding (n+y) ys
padding n ys = Padding n ys

drawBinaryTree ::
     Show a
  => (LevelBuilder -> (a -> LevelBuilder -> LevelBuilder -> LevelBuilder) -> b -> LevelBuilder)
  -> b
  -> String
drawBinaryTree ft = unlines . levels . ft (LevelBuilder 0 []) f
  where
    f el (LevelBuilder llen lb) (LevelBuilder rlen rb) =
      LevelBuilder
        (llen + rlen + xlen)
        (padding llen (Prefix xshw (padding rlen Nil)) : zipLongest lb rb)
      where
        xshw = shows el
        xlen = length (xshw "")
        zipLongest (x:xs) (y:ys) = comb3 x xlen y : zipLongest xs ys
        zipLongest [] ys = lfn ys
        zipLongest xs [] = rfn xs
        rfn
          | xr == 0 = id
          | otherwise = map go
          where
            xr = xlen + rlen
            go (Padding x Nil) = Padding (x + xr) Nil
            go (Padding x xs) = Padding x (go xs)
            go (Prefix x xs) = Prefix x (go xs)
            go Nil = Padding xr Nil
        lfn
          | xl == 0 = id
          | otherwise = map go
          where
            xl = llen + xlen
            go (Padding x xs) = Padding (xl + x) xs
            go xs = Padding xl xs
        comb3 xs 0 ys = mappend xs ys
        comb3 Nil l ys = padding l ys
        comb3 (Padding x Nil) l ys = padding (x + l) ys
        comb3 (Padding x xs) l ys = Padding x (comb3 xs l ys)
        comb3 (Prefix x xs) l ys = Prefix x (comb3 xs l ys)
    unlines [] = ""
    unlines (x:xs) = runLevel x (foldr (\e a -> '\n' : runLevel e a) "" xs)

newtype State s a = State
  { runState :: s -> (a, s)
  }

instance Functor (State s) where
  fmap f xs =
    State
      (\s ->
         case runState xs s of
           (x, s') -> (f x, s'))

instance Applicative (State s) where
  pure x = State (\s -> (x, s))
  fs <*> xs =
    State
      (\s ->
         case runState fs s of
           (f, s') ->
             case runState xs s' of
               (x, s'') -> (f x, s''))

evalState :: State s a -> s -> a
evalState xs s = fst (runState xs s)

#if !MIN_VERSION_base(4,8,0)
newtype Identity a = Identity {runIdentity :: a}

instance Functor Identity where
  fmap f (Identity x) = Identity (f x)

instance Applicative Identity where
  pure = Identity
  Identity f <*> Identity x = Identity (f x)
#endif
