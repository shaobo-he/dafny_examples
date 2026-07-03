include "BinaryTree.dfy"

import opened BinaryTree
import opened Seq

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

lemma InorderMultiset(t: Tree<int>)
  ensures multiset(InorderFlatten(t)) == ToMS(t)
{
  match t
  case Nil =>
  case Node(_, l, r) =>
    InorderMultiset(l);
    InorderMultiset(r);
}

lemma InorderMemberToMS(t: Tree<int>, x: int)
  ensures x in InorderFlatten(t) <==> x in ToMS(t)
{
  InorderMultiset(t);
}

lemma BSTLeftValuesLeRoot(x: int, l: Tree<int>, r: Tree<int>)
  requires BinarySearchTree?(Node(x, l, r))
  ensures forall v :: v in InorderFlatten(l) ==> v <= x
{
  InorderMultiset(l);
  forall v | v in InorderFlatten(l)
    ensures v <= x
  {
    assert v in ToMS(l);
  }
}

lemma BSTRightValuesGeRoot(x: int, l: Tree<int>, r: Tree<int>)
  requires BinarySearchTree?(Node(x, l, r))
  ensures forall v :: v in InorderFlatten(r) ==> x <= v
{
  InorderMultiset(r);
  forall v | v in InorderFlatten(r)
    ensures x <= v
  {
    assert v in ToMS(r);
  }
}

lemma BSTInorderSorted(t: Tree<int>)
  requires BinarySearchTree?(t)
  ensures Sorted(InorderFlatten(t))
{
  match t
  case Nil =>
  case Node(x, l, r) =>
    BSTInorderSorted(l);
    BSTInorderSorted(r);
    InorderMultiset(l);
    InorderMultiset(r);
    var lf := InorderFlatten(l);
    var rf := InorderFlatten(r);
    assert InorderFlatten(t) == lf + [x] + rf;
    forall i, j | 0 <= i < j < |InorderFlatten(t)|
      ensures InorderFlatten(t)[i] <= InorderFlatten(t)[j]
    {
      if j < |lf| {
        assert lf[i] <= lf[j];
      } else if i < |lf| {
        assert lf[i] in lf;
        assert lf[i] in ToMS(l);
        if j == |lf| {
        } else {
          var rj := j - |lf| - 1;
          assert 0 <= rj < |rf|;
          assert InorderFlatten(t)[j] == rf[rj];
          assert rf[rj] in rf;
          assert rf[rj] in ToMS(r);
        }
      } else if i == |lf| {
        if j > |lf| {
          var rj := j - |lf| - 1;
          assert 0 <= rj < |rf|;
          assert InorderFlatten(t)[j] == rf[rj];
          assert rf[rj] in rf;
          assert rf[rj] in ToMS(r);
        }
      } else {
        var ri := i - |lf| - 1;
        var rj := j - |lf| - 1;
        assert 0 <= ri < rj < |rf|;
        assert rf[ri] <= rf[rj];
      }
    }
}

lemma BSTSearchLeftPrune(q: int, x: int, l: Tree<int>, r: Tree<int>)
  requires BinarySearchTree?(Node(x, l, r))
  requires q < x
  ensures q in ToMS(Node(x, l, r)) <==> q in ToMS(l)
{
  if q in ToMS(Node(x, l, r)) && q !in ToMS(l) {
    if q == x {
      assert false;
    } else {
      assert q in ToMS(r);
      assert x <= q;
      assert false;
    }
  }
}

lemma BSTSearchRightPrune(q: int, x: int, l: Tree<int>, r: Tree<int>)
  requires BinarySearchTree?(Node(x, l, r))
  requires x < q
  ensures q in ToMS(Node(x, l, r)) <==> q in ToMS(r)
{
  if q in ToMS(Node(x, l, r)) && q !in ToMS(r) {
    if q == x {
      assert false;
    } else {
      assert q in ToMS(l);
      assert q <= x;
      assert false;
    }
  }
}