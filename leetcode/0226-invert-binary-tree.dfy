// Author: Shaobo He
include "../lib/adt/BinaryTree.dfy"

import opened BinaryTree
import opened Seq

function Mirror<T>(t: Tree<T>) : (r: Tree<T>)
  ensures Size(r) == Size(t)
{
  match t
  case Nil => Nil
  case Node(x, l, r) => Node(x, Mirror(r), Mirror(l))
}

// A corroborating property of inversion: mirroring a tree reverses its in-order
// traversal. Unlike Size/MirrorEq/MirrorPerm below, this is NOT satisfied by
// the identity (no-swap) function. The structural characterization is the
// recursive Mirror definition itself.
lemma MirrorInorderReverse<T>(t: Tree<T>)
  ensures InorderFlatten(Mirror(t)) == Reverse(InorderFlatten(t))
{
  match t
  case Nil =>
  case Node(x, l, r) =>
    MirrorInorderReverse(l);
    MirrorInorderReverse(r);
    ReverseConcat(InorderFlatten(l) + [x], InorderFlatten(r));
    ReverseConcat(InorderFlatten(l), [x]);
}

// The involution Equal?(Mirror(Mirror(t)), t) cannot be stated as a
// postcondition of Mirror itself: the spec's nested Mirror(r) call carries a
// termination obligation that Dafny cannot discharge, because the result is
// structurally the same size as the input.
lemma MirrorEq<T>(t: Tree<T>)
  ensures Equal?(t, Mirror(Mirror(t)))
{
}

lemma MirrorPerm<T>(t: Tree<T>)
  ensures forall x :: CountBT(x, t) == CountBT(x, Mirror(t))
{
}