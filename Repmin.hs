{- experiment with Zippers and typeclass constraints
for a lightweight AG approach in Haskell.
TODO memoization to avoid recomputing the inherited attributes.
-}

{-# LANGUAGE
  FlexibleInstances
 , UndecidableInstances -- Show instance
 , FlexibleContexts
 , StandaloneDeriving
 , ViewPatterns
 , DeriveFunctor
 , NoMonomorphismRestriction
 #-}

-- * Module
module Repmin where

res2 g f x y = g (f x y)
cst2 c x y = c

-- * Tree

-- Base functor of the tree type
data TreeF t = Node t t | Leaf Int deriving Show
data Fix f = In (f (Fix f))

deriving instance (Show (f (Fix f))) => Show (Fix f)

type T = Fix TreeF
leaf = In . Leaf
node x y = In (Node x y)

class Tree t where
  tree :: t -> TreeF t

instance Tree T where
  tree (In x) = x

-- Derivative of Tree parameterised by the tree type
data TreeD t = LeftChild t | RightChild t
  deriving (Show, Functor)

type TreeCtx t = [TreeD t]

-- zipper for tree
type TreeZ = (TreeCtx T, T)
instance Tree TreeZ where
  tree (c, t) = case tree t of
    Node x y ->
      Node (LeftChild   y : c, x)
           (RightChild  x : c, y)
    Leaf n -> Leaf n

data Ctx a b = Top | a :> b

class Tree t => TreeC t where
  ctx :: t -> Ctx t (TreeD t)

instance TreeC TreeZ where
  ctx ([],t) = Top
  ctx (d:c,t) = up c t d :> sibling c t d

-- we must add the context to "r" and "l"
sibling c t (LeftChild r)  = LeftChild (RightChild t : c, r)
sibling c t (RightChild l) = RightChild (LeftChild t : c, l)

-- we build the parent zipper
up c t (LeftChild r) = (c, In (Node t r))
up c t (RightChild l) = (c, In (Node l t))

-- Turn a tree into a zipper focused on the root
top :: T -> TreeZ
top t = ([],t)

-- ** example
extree :: T
extree =
     (l 2 * ((l 3 * l 2) * l 5))
   * ((l 2 * l 4) * l 7)
  where
     l = leaf
     (*) = node

-- * Repmin
minT :: (Tree t) => t -> Int
minT (tree -> Leaf n) = n
minT (tree -> Node x y) = min (minT x) (minT y)

-- the global mininum, an inherited attribute is propagated
-- down the tree, as a function of the context.
gmin :: TreeC t => t -> Int
gmin t = case ctx t of
  Top -> minT t
  p :> _ -> gmin p -- copy rule

repmin :: (TreeC t) => t -> T
repmin t = case tree t of
  Leaf n -> leaf (gmin t)
  Node x y -> node (repmin x) (repmin y)

-- ** Abstractions

{- Each of the functions above can be generalised into a
  useful combinator.
-}

{- Paramorphism are especially useful since they can
depend on inherited attributes.
-}

para :: Tree t => (t -> Int -> a) -> (t -> a -> a -> a) -> t -> a
para l n = go
 where
   go t = case tree t of
     Leaf n -> l t n
     Node x y -> n t (go x) (go y)

fold l n = para (const l) (const n)

-- Generalised map that depends on the tree to compute the leaf value.
mapT :: Tree t => (t -> Int -> Int) -> t -> T
mapT f = para (leaf `res2` f) (const node)

propagate :: TreeC t => (t -> a) -> (t -> a) -> t -> a
propagate top parent t = case ctx t of
  Top -> top t
  p :> _ -> parent p
  
-- Define an inherited attribute which is simply copied down
-- the tree and initialiased at the root.
copy :: TreeC t => (t -> a) -> t -> a
copy f = propagate (copy f) f

repmin2 = mapT (\t _ -> gmin t)
 where
   gmin = copy minT
   minT = fold id min

-- * rendering
render t = case tree t of
  Leaf n -> show n ++ rest t
  Node x y -> "(" ++ render x 
rest t = case ctx t of
  Top -> ""
  p :> LeftChild r  -> " * " ++ render r
  p :> RightChild l -> ")" ++ rest p

test f = render . top . f . top $ extree

-- * In order labelling
-- Chaining attributes icount and count
count t = case tree t of
  Leaf _ -> 1 + icount t
  Node x y -> count y

icount t = case ctx t of
  Top -> 0
  p :> LeftChild r -> icount p
  p :> RightChild l -> count l
  
label t = case tree t of
  Leaf _ -> leaf $ icount t
  Node l r -> node (label l) (label r)

-- ** Abstracting over the chain pattern
-- we must give the base case for leaves and top.

chain :: (TreeC t) =>
  (t -> a) -> (t -> Int -> a -> a) -> (t -> a, t -> a)
chain top leaf = (up, down)
  where
    up t = case tree t of
      Leaf n -> leaf t n (down t)
      Node x y -> up y
    down (ctx -> p :> RightChild l) = up l
    down t = propagate top down t -- default to the copy rule

ichain = snd `res2` chain
schain = fst `res2` chain

label2 = mapT $ const . ichain (const 0) (cst2 (1+))

-- * De Moor's repmin
{-  Computes a tree structurally equivalent where the leaves
    contain the number of occurence of the smallest value on
    their left in the inorder traversal.
-}

demoor = mapT $ const . count
  where
    count = ichain (const 0) update
    update t n c = if n == gmin t then 1 + c else c
