[![Hackage](https://img.shields.io/hackage/v/binary-tree.svg)](http://hackage.haskell.org/package/binary-tree) [![Build Status](https://travis-ci.org/oisdk/binary-tree.svg?branch=master)](https://travis-ci.org/oisdk/binary-tree)

# binary-tree

This package provides three different binary tree types, in a very generic and portable form. They are:

Preorder:

```haskell
data Tree a = Leaf | Node a (Tree a) (Tree a)
```

Inorder:

```haskell
data Tree a = Leaf | Node (Tree a) a (Tree a)
```

Leafy:

```haskell
data Tree a = Leaf a | Tree a :*: Tree a
```

Effort is made to ensure the types provided are portable and generic: CI tests go back to GHC 7.2, and in cases where more than one sensible instance exists none are provided.

Tricky instances include:

* Lifted Read and Show classes (Read1, Show1, etc).
* MonadFix for the leafy tree and Applicative for the others.
* Semigroup and Monoid instances.
* Handwritten foldable instances

Beyond the instances, a general drawing algorithm is provided, to produce diagrams like so:

```haskell
   ┌1
 ┌2┤
 │ └3
4┤
 │ ┌5
 └6┤
   └7
   
              ┌[1,2,3]
         ┌2<=3┤
         │    └[1,3,2]
    ┌1<=3┤
    │    └[3,1,2]
1<=2┤
    │    ┌[2,1,3]
    └1<=3┤
         │    ┌[2,3,1]
         └2<=3┤
              └[3,2,1]
```

The library is tested using quickcheck and doctest.
