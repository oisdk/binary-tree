{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Test.QuickCheck
import Test.QuickCheck.Poly
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Test.ChasingBottoms
import Test.Framework as Framework
import Test.Framework.Providers.QuickCheck2

import qualified Data.Tree.Binary.Preorder as Preorder
import qualified Data.Tree.Binary.Leafy as Leafy
import qualified Data.Tree.Binary.Inorder as Inorder

import Control.Applicative
import Data.Foldable
import Data.Traversable

#if MIN_VERSION_base(4,9,0)
import Data.Functor.Classes
#endif

import Prelude hiding
  ( replicate
#if MIN_VERSION_base(4,8,0)
  ,Functor(..),Foldable(..),Applicative, (<$>), foldMap, Monoid
#else
  ,foldr,foldl
#endif
  )

import Data.Functor (Functor(fmap))

#if MIN_VERSION_base(4,6,0)
import Data.Foldable (Foldable(foldl, foldr, foldMap, foldl', foldr'))
#else
import Data.Foldable (Foldable(foldl, foldr, foldMap))
#endif

#if MIN_VERSION_base(4,9,0)
import qualified Data.Semigroup as Semigroup
#endif

import Text.Read

--------------------------------------------------------------------------------
-- Lifted Properties
--------------------------------------------------------------------------------
#if MIN_VERSION_base(4,9,0)
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

showProp :: (Show1 f, Show (f A)) => f () -> f A -> Property
showProp _ xs = show xs === show (Lifted xs)

readProp ::
     (Read1 f, Show (f (f Int)), Read (f Int), EqProp (f (f Int)), Arbitrary (f (f Int)))
  => f (f Int)
  -> Property
readProp p = inverseL reader show
  where
    reader str = runLifted (read str) `asTypeOf` p

liftedProperties
    :: (Ord (f OrdA)
       ,Ord1 f
       ,Show (f OrdA)
       ,Arbitrary (f OrdA)
       ,Show1 f
       ,Arbitrary (f A)
       ,Show (f A)
       ,Read1 f
       ,Show (f (f Int))
       ,Read (f Int)
       ,EqProp (f (f Int))
       ,Arbitrary (f (f Int))
       ,EqProp (f OrdA))
    => (OrdA -> f OrdA) -> Framework.Test
liftedProperties t =
    testGroup
        "Lifted Classes"
        [ testBatch (ord (\x -> oneof [pure x, arbitrary `asTypeOf` conv3 t]))
        , testProperty "eq1" (eq1Prop (t undefined))
        , testProperty "ord1 consistency" (ord1Prop (t undefined))
        , testProperty "show1" (showProp (conv t))
        , testProperty "read1" (readProp (conv2 t))]
  where
    conv :: (OrdA -> f OrdA) -> f ()
    conv = undefined
    conv2 :: (OrdA -> f OrdA) -> f (f Int)
    conv2 = undefined
    conv3 :: (OrdA -> f OrdA) -> Gen (Lifted f OrdA)
    conv3 = undefined
#endif

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

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
        [0 :: Int]
    , (i, c) <- zip [(-1 :: Int) ..] fns
    ]
  where
    (n, xs) = indexed xs'
    ys = [0 .. n - 1]
    fns =
      const :
      [ \y _ ->
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
    , (i, c) <- zip [(-1 :: Int) ..] fns
    ]
  where
    (n, xs) = indexed xs'
    ys = [(0 :: Int) .. n - 1]
    fns =
      const id :
      [ \_ y ->
        if x == y
          then error "too strict"
          else y
      | x <- ys
      ]

foldProperties
    :: (Arbitrary (f A)
       ,Show (f A)
       ,Show (f Int)
       ,Arbitrary (f ())
       ,Show (f ())
       ,Traversable f)
    => f () -> Framework.Test
foldProperties p =
    testGroup
        "Folds"
        [ testProperty "foldl" (foldlProp p)
        , testProperty "foldr'" (foldrProp' p)
        , testProperty "foldl'" (foldlProp' p)
        , testProperty "foldMap" (foldMapProp p)
        , testProperty "foldrStrict" (foldrStrictProp p)
#if MIN_VERSION_base(4,8,0) || !MIN_VERSION_base(4,6,0)
        , testProperty "foldlStrict" (foldlStrictProp p)
#endif
        ]



--------------------------------------------------------------------------------
-- Display
--------------------------------------------------------------------------------

endsInNewlineProp :: (a -> String) -> a -> Property
endsInNewlineProp f x =
    maybe (counterexample "shouldn't be empty" False) ('\n' ===) (last' (f x))
  where
    last' =
        foldl'
            (\_ e ->
                  Just e)
            Nothing

--------------------------------------------------------------------------------
-- Helper for Checker format
--------------------------------------------------------------------------------

testBatch :: TestBatch -> Framework.Test
testBatch (name, tests) = testGroup name (map (uncurry testProperty) tests)

main :: IO ()
main =
  defaultMain
    [ testGroup
        "Preorder"
        [ testBatch (monoid (Preorder.Leaf :: Preorder.Tree A))
        , testProperty "toList . fromList" (inverseL toList (Preorder.fromList :: [Int] -> Preorder.Tree Int))
#if MIN_VERSION_base(4,9,0)
        , liftedProperties (const Preorder.Leaf)
#endif
        , foldProperties Preorder.Leaf
        , testBatch (functor (undefined :: Preorder.Tree (A, B, C)))
        , testBatch
            ( "applicative"
            , [ (name, test)
              | (name, test) <- snd $ applicative (undefined :: Preorder.Tree (A, B, C))
              , name /= "homomorphism"
              ])
        , testBatch (traversable (undefined :: Preorder.Tree (A, B, [Int])))
        , testBatch (alternative (undefined :: Preorder.Tree A))
        , testProperty "drawTree ends in newline" (endsInNewlineProp (Preorder.drawTree :: Preorder.Tree A -> String))
        ]
    , testGroup
        "Inorder"
        [ testBatch (monoid (Inorder.Leaf :: Inorder.Tree A))
        , testProperty "toList . fromList" (inverseL toList (Inorder.fromList :: [Int] -> Inorder.Tree Int))
#if MIN_VERSION_base(4,9,0)
        , liftedProperties (const Inorder.Leaf)
#endif
        , foldProperties Inorder.Leaf
        , testBatch
            ( "applicative"
            , [ (name, test)
              | (name, test) <- snd $ applicative (undefined :: Inorder.Tree (A, B, C))
              , name /= "homomorphism"
              ])
        , testBatch (functor (undefined :: Inorder.Tree (A, B, C)))
        , testBatch (traversable (undefined :: Inorder.Tree (A, B, [Int])))
        , testBatch (alternative (undefined :: Inorder.Tree A))
        , testProperty "drawTree ends in newline" (endsInNewlineProp (Inorder.drawTree :: Inorder.Tree A -> String))
        ]
    , testGroup
        "Leafy"
        [
#if MIN_VERSION_base(4,9,0)
        testProperty "semigroup" (isAssoc ((Semigroup.<>) :: Leafy.Tree Int -> Leafy.Tree Int -> Leafy.Tree Int) ) ,
#endif
         testProperty "toList . fromList" (inverseL (NonEmpty . toList) (Leafy.fromList . getNonEmpty :: NonEmptyList Int -> Leafy.Tree Int))
#if MIN_VERSION_base(4,9,0)
        , liftedProperties Leafy.Leaf
#endif
        , foldProperties (Leafy.Leaf undefined)
        , testBatch (functor (undefined :: Leafy.Tree (A, B, C)))
        , testBatch (applicative (undefined :: Leafy.Tree (A, B, C)))
        , testBatch (monad (undefined :: Leafy.Tree (A, B, C)))
        , testBatch (monadFunctor (undefined :: Leafy.Tree (A, B)))
        , testBatch (monadApplicative (undefined :: Leafy.Tree (A, B)))
        , testBatch (traversable (undefined :: Leafy.Tree (A, B, [Int])))
        , testProperty "drawTree ends in newline" (endsInNewlineProp (Leafy.drawTree :: Leafy.Tree A -> String))
        ]
    ]

--------------------------------------------------------------------------------
-- Arbitrary Instances
--------------------------------------------------------------------------------
instance Arbitrary a => Arbitrary (Preorder.Tree a) where
  arbitrary = sized go
    where
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

instance Arbitrary a => Arbitrary (Leafy.Tree a) where
  arbitrary = sized go
    where
      go n
        | n <= 0 = fmap Leafy.Leaf arbitrary
        | otherwise =
          oneof [fmap Leafy.Leaf arbitrary, liftA2 (Leafy.:*:) sub sub]
        where
          sub = go (n `div` 2)
  shrink (Leafy.Leaf x) = fmap Leafy.Leaf (shrink x)
  shrink (l Leafy.:*: r) =
    l : r : [l' Leafy.:*: r' | (l', r') <- shrink (l, r)]

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

instance (Show a, Eq a) => EqProp (Leafy.Tree a) where
  x =-= y =
    whenFail
      (putStrLn (Leafy.drawTree x ++ "\n/=\n" ++ Leafy.drawTree y))
      (x == y)

instance (Eq a, Show a) => EqProp (NonEmptyList a) where
  (=-=) = (===)
--------------------------------------------------------------------------------
-- Lifted
--------------------------------------------------------------------------------

#if MIN_VERSION_base(4,9,0)
newtype Lifted f a = Lifted { runLifted :: f a }

instance (Eq1 f, Eq a) => Eq (Lifted f a) where
  Lifted xs == Lifted ys = eq1 xs ys

instance (Ord1 f, Ord a) => Ord (Lifted f a) where
  compare (Lifted xs) (Lifted ys) = compare1 xs ys

instance (Show1 f, Show a) => Show (Lifted f a) where
  showsPrec n (Lifted xs) = showsPrec1 n xs
  showList xs = liftShowList showsPrec showList [ x | Lifted x <- xs ]

instance (Read1 f, Read a) => Read (Lifted f a) where
#if MIN_VERSION_base(4,10,0)
  readPrec = fmap Lifted readPrec1
#else
  readsPrec n xs = [ (Lifted x,ys) | (x, ys) <- readsPrec1 n xs ]
#endif

instance EqProp (f a) => EqProp (Lifted f a) where
  Lifted x =-= Lifted y = x =-= y

instance Arbitrary (f a) => Arbitrary (Lifted f a) where
  arbitrary = fmap Lifted arbitrary
  shrink (Lifted xs) = fmap Lifted (shrink xs)
#endif
