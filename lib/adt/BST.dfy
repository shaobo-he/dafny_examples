include "BinaryTree.dfy"

import opened BinaryTree

predicate GEAll(x: int, xs: multiset<int>)   // x is >= every element (bounds a left subtree)
{
  forall v :: v in xs ==> x >= v
}

predicate LEAll(x: int, xs: multiset<int>)   // x is <= every element (bounds a right subtree)
{
  forall v :: v in xs ==> x <= v
}

lemma GEAllEmpty(x: int, xs: multiset<int>)
  ensures |xs| == 0 ==> GEAll(x, xs)
{
}

// A binary search tree: every left-subtree value is <= x <= every right-subtree
// value, recursively.
predicate BinarySearchTree?(t: Tree<int>)
{
  match t
  case Nil => true
  case Node(x, l, r) =>
    GEAll(x, ToMS(l)) && LEAll(x, ToMS(r)) && BinarySearchTree?(l) && BinarySearchTree?(r)
}
