// Author: Shaobo He
include "../lib/adt/BinaryTree.dfy"

import opened BinaryTree

function Mirror<T>(t: Tree<T>) : (r: Tree<T>)
  ensures Size(r) == Size(t)
{
  match t
  case Nil => Nil
  case Node(x, l, r) => Node(x, Mirror(r), Mirror(l))
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