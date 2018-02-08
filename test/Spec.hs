import Test.DocTest
import Test.QuickCheck
import Test.QuickCheck.Poly
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Test.QuickCheck.Function
import Test.ChasingBottoms

import qualified Data.Tree.Binary.Preorder as Preorder
import qualified Data.Tree.Binary.Inorder as Inorder
import Data.Tree.Binary.Internal

import Control.Applicative
import Data.Foldable
import Data.Traversable

import Data.Functor.Classes

import Text.Read

--------------------------------------------------------------------------------
-- Lifted Properties
--------------------------------------------------------------------------------
eq1Prop ::
     (Eq (f OrdA), Eq1 f, Show (f OrdA), Arbitrary (f OrdA))
  => f OrdA
  -> Property
eq1Prop p =
  forAllShrink arbitrary shrink $ \xs ->
    forAllShrink (oneof [pure xs, arbitrary]) shrink $ \ys ->
      (Lifted xs == Lifted ys) === ((xs `asTypeOf` p) == ys)

ord1Prop ::
     (Ord (f OrdA), Ord1 f, Show (f OrdA), Arbitrary (f OrdA))
  => f OrdA
  -> Property
ord1Prop p =
  forAllShrink arbitrary shrink $ \xs ->
    forAllShrink (oneof [pure xs, arbitrary]) shrink $ \ys ->
      (Lifted xs `compare` Lifted ys) === ((xs `asTypeOf` p) `compare` ys)

foldlProp ::
     (Foldable f)
  => f ()
  -> f A
  -> Fun (B, A) B
  -> B
  -> Property
foldlProp _ xs f b =
  foldl (applyFun2 f) b (toList xs) === foldl (applyFun2 f) b xs

foldrProp' ::
     (Foldable f)
  => f ()
  -> f A
  -> Fun (A, B) B
  -> B
  -> Property
foldrProp' _ xs f b = foldr' (applyFun2 f) b xs === foldr (applyFun2 f) b xs

foldlProp' ::
     (Foldable f)
  => f ()
  -> f A
  -> Fun (B, A) B
  -> B
  -> Property
foldlProp' _ xs f b =
  foldl' (applyFun2 f) b xs === foldl (applyFun2 f) b xs

foldMapProp :: Foldable f => f () -> f A -> Fun A [B] -> Property
foldMapProp _ xs f =
  foldMap (applyFun f) (toList xs) === foldMap (applyFun f) xs

indexed :: Traversable f => f a -> (Int, f Int)
indexed = mapAccumL (\a _ -> (a+1, a)) 0

foldrStrictProp :: (Show (f Int), Traversable f) => f () -> f () -> Property
foldrStrictProp _ xs' =
  conjoin
    [ counterexample (unlines [show xs, show ys, show i]) $
    isBottom (foldr' c b xs) === isBottom (foldr' c b ys)
    | b
    -- error "too strict",
         <-
        [0]
    , (i, c) <- zip [-1 ..] fns
    ]
  where
    (n, xs) = indexed xs'
    ys = [0 .. n - 1]
    fns =
      const :
      [ \y b ->
        if x == y
          then error "too strict"
          else y
      | x <- ys
      ]

foldlStrictProp :: (Show (f Int), Traversable f) => f () -> f () -> Property
foldlStrictProp _ xs' =
  conjoin
    [ counterexample (unlines [show xs, show ys, show i]) $
    isBottom (foldl' c b xs) == isBottom (foldl' c b ys)
    | b <- [error "too strict", 0]
    , (i, c) <- zip [-1 ..] fns
    ]
  where
    (n, xs) = indexed xs'
    ys = [0 .. n - 1]
    fns =
      const id :
      [ \b y ->
        if x == y
          then error "too strict"
          else y
      | x <- ys
      ]

main :: IO ()
main = do
  quickBatch (monoid (Preorder.Leaf :: Preorder.Tree A))
  quickCheck (inverseL toList (Preorder.fromList :: [Int] -> Preorder.Tree Int))
  quickBatch (ord (\x -> oneof [pure x, arbitrary :: Gen (Lifted Preorder.Tree OrdA)]))
  quickCheck (eq1Prop Preorder.Leaf)
  quickCheck (ord1Prop Preorder.Leaf)
  quickBatch (monoid (Inorder.Leaf :: Inorder.Tree A))
  quickCheck (inverseL toList (Inorder.fromList :: [Int] -> Inorder.Tree Int))
  quickBatch (ord (\x -> oneof [pure x, arbitrary :: Gen (Lifted Inorder.Tree OrdA)]))
  quickCheck (eq1Prop Inorder.Leaf)
  quickCheck (ord1Prop Preorder.Leaf)
  quickCheck (foldlProp Inorder.Leaf)
  quickCheck (foldlProp Preorder.Leaf)
  quickCheck (foldrProp' Preorder.Leaf)
  quickCheck (foldrProp' Inorder.Leaf)
  quickCheck (foldMapProp Preorder.Leaf)
  quickCheck (foldMapProp Inorder.Leaf)
  quickCheck (foldrStrictProp Preorder.Leaf)
  quickCheck (foldrStrictProp Inorder.Leaf)
  quickCheck (foldlStrictProp Preorder.Leaf)
  quickCheck (foldlStrictProp Inorder.Leaf)
  doctest ["-isrc", "src/"]

--------------------------------------------------------------------------------------------------
-- Arbitrary Instances
--------------------------------------------------------------------------------------------------
instance Arbitrary a => Arbitrary (Preorder.Tree a) where
  arbitrary = sized go
    where
      go 0 = pure Preorder.Leaf
      go n
        | n <= 0 = pure Preorder.Leaf
        | otherwise =
          oneof [pure Preorder.Leaf, liftA3 Preorder.Node arbitrary sub sub]
        where
          sub = go (n `div` 2)
  shrink Preorder.Leaf = []
  shrink (Preorder.Node x l r) =
    Preorder.Leaf :
    l : r : [Preorder.Node x' l' r' | (x', l', r') <- shrink (x, l, r)]

instance Arbitrary a => Arbitrary (Inorder.Tree a) where
  arbitrary = sized go
    where
      go 0 = pure Inorder.Leaf
      go n
        | n <= 0 = pure Inorder.Leaf
        | otherwise =
          oneof [pure Inorder.Leaf, liftA3 Inorder.Node sub arbitrary sub]
        where
          sub = go (n `div` 2)
  shrink Inorder.Leaf = []
  shrink (Inorder.Node l x r) =
    Inorder.Leaf :
    l : r : [Inorder.Node l' x' r' | (l', x', r') <- shrink (l, x, r)]

--------------------------------------------------------------------------------
-- EqProp Instances
--------------------------------------------------------------------------------
instance (Show a, Eq a) => EqProp (Preorder.Tree a) where
  x =-= y =
    whenFail
      (putStrLn (Preorder.drawTree x ++ "\n/=\n" ++ Preorder.drawTree y))
      (x == y)

instance (Show a, Eq a) => EqProp (Inorder.Tree a) where
  x =-= y =
    whenFail
      (putStrLn (Inorder.drawTree x ++ "\n/=\n" ++ Inorder.drawTree y))
      (x == y)

--------------------------------------------------------------------------------
-- Lifted
--------------------------------------------------------------------------------
newtype Lifted f a = Lifted { runLifted :: f a }

instance (Eq1 f, Eq a) => Eq (Lifted f a) where
  Lifted xs == Lifted ys = eq1 xs ys

instance (Ord1 f, Ord a) => Ord (Lifted f a) where
  compare (Lifted xs) (Lifted ys) = compare1 xs ys

instance (Show1 f, Show a) => Show (Lifted f a) where
  showsPrec n (Lifted xs) = showsPrec1 n xs
  showList xs = liftShowList showsPrec showList [ x | Lifted x <- xs ]

instance (Read1 f, Read a) => Read (Lifted f a) where
  readsPrec n xs = [ (Lifted x,ys) | (x, ys) <- readsPrec1 n xs ]
  readPrec = fmap Lifted readPrec1

instance EqProp (f a) => EqProp (Lifted f a) where
  Lifted x =-= Lifted y = x =-= y

instance Arbitrary (f a) => Arbitrary (Lifted f a) where
  arbitrary = fmap Lifted arbitrary
  shrink (Lifted xs) = fmap Lifted (shrink xs)
