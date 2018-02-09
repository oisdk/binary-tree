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
  ,Functor(..),Applicative, (<$>), foldMap, Monoid
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

drawBinaryTree ::
     Show a
  => (LevelBuilder -> (a -> LevelBuilder -> LevelBuilder -> LevelBuilder) -> b -> LevelBuilder)
  -> b
  -> String
drawBinaryTree ft = runLevels . levels . ft (LevelBuilder 0 []) f
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

evalState :: State s a -> s -> a
evalState xs s = fst (runState xs s)
{-# INLINE evalState #-}

--------------------------------------------------------------------------------
-- Identity
--------------------------------------------------------------------------------
#if !MIN_VERSION_base(4,8,0)
newtype Identity a = Identity {runIdentity :: a}

instance Functor Identity where
  fmap f (Identity x) = Identity (f x)

instance Applicative Identity where
  pure = Identity
  Identity f <*> Identity x = Identity (f x)
#endif
