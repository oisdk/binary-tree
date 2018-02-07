import Test.DocTest
import Test.QuickCheck
import Test.QuickCheck.Poly
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes

import qualified Data.Tree.Binary.Preorder as Preorder
import qualified Data.Tree.Binary.Inorder as Inorder

import Control.Applicative
import Data.Foldable

import Data.Functor.Classes

import Text.Read

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

instance (Show a, Eq a) => EqProp (Preorder.Tree a) where
  x =-= y =
    whenFail
      (putStrLn (Preorder.drawTree x ++ "\n/=\n" ++ Preorder.drawTree y))
      (x == y)

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

instance (Show a, Eq a) => EqProp (Inorder.Tree a) where
  x =-= y =
    whenFail
      (putStrLn (Inorder.drawTree x ++ "\n/=\n" ++ Inorder.drawTree y))
      (x == y)

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

eq1Prop ::
     (Eq (f a), Eq1 f, Show (f a), Eq a)
  => Gen (f a)
  -> (f a -> [f a])
  -> Property
eq1Prop arb shrnk =
  forAllShrink arb shrnk $ \xs ->
    forAllShrink (oneof [pure xs, arb]) shrnk $ \ys ->
      liftEq (==) xs ys === (xs == ys)

ord1Prop ::
     (Ord (f a), Ord1 f, Show (f a), Ord a)
  => Gen (f a)
  -> (f a -> [f a])
  -> Property
ord1Prop arb shrnk =
  forAllShrink arb shrnk $ \xs ->
    forAllShrink (oneof [pure xs, arb]) shrnk $ \ys ->
      liftCompare compare xs ys === (compare xs ys)

main :: IO ()
main = do
  quickBatch (monoid (Preorder.Leaf :: Preorder.Tree A))
  quickCheck (inverseL toList (Preorder.fromList :: [Int] -> Preorder.Tree Int))
  quickBatch (ord (\x -> oneof [pure x, arbitrary :: Gen (Lifted Preorder.Tree OrdA)]))
  quickCheck (eq1Prop (arbitrary :: Gen (Preorder.Tree A)) shrink)
  quickCheck (ord1Prop (arbitrary :: Gen (Preorder.Tree OrdA)) shrink)
  quickBatch (monoid (Inorder.Leaf :: Inorder.Tree A))
  quickCheck (inverseL toList (Inorder.fromList :: [Int] -> Inorder.Tree Int))
  quickBatch (ord (\x -> oneof [pure x, arbitrary :: Gen (Lifted Inorder.Tree OrdA)]))
  quickCheck (eq1Prop (arbitrary :: Gen (Inorder.Tree A)) shrink)
  quickCheck (ord1Prop (arbitrary :: Gen (Inorder.Tree OrdA)) shrink)
  doctest ["-isrc", "src/"]
