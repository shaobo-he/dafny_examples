include "../Seq.dfy"
include "Subseq.dfy"

import opened Seq

function {:opaque} Undup<T(==)>(xs: seq<T>): seq<T> {
  if |xs| == 0 then xs
  else if Last(xs) in RemoveLast(xs) then Undup(RemoveLast(xs))
  else Undup(RemoveLast(xs)) + [Last(xs)]
}

lemma MemUndup<T>(xs: seq<T>)
  ensures forall x :: x in Undup(xs) <==> x in xs
{
  reveal Undup();
}

lemma DistinctUndup<T>(xs: seq<T>)
  ensures Distinct(Undup(xs))
{
  reveal Undup();
  if |xs| != 0 && Last(xs) !in RemoveLast(xs) {
    MemUndup(RemoveLast(xs));
  }
}

lemma UndupLengthBound<T>(xs: seq<T>)
  ensures |Undup(xs)| <= |xs|
{
  reveal Undup();
  if |xs| != 0 {
    UndupLengthBound(RemoveLast(xs));
  }
}

lemma UndupDistinctIdentity<T>(xs: seq<T>)
  requires Distinct(xs)
  ensures Undup(xs) == xs
{
  reveal Undup();
  if |xs| != 0 {
    DistinctEqRecLast(xs);
    assert Last(xs) !in RemoveLast(xs);
    DistinctSubseq(xs, 0, |xs| - 1);
    UndupDistinctIdentity(RemoveLast(xs));
    ConcatRemoveLastLast(xs);
  }
}

lemma SubseqUndup<T>(xs: seq<T>)
  ensures Subseq(Undup(xs), xs)
{
  reveal Undup();
  if |xs| == 0 {
    assert Undup(xs) == xs;
    SubseqRefl(xs);
  } else {
    SubseqUndup(RemoveLast(xs));
    if Last(xs) in RemoveLast(xs) {
      SubseqRemoveLast(xs);
      SubseqTrans(Undup(RemoveLast(xs)), RemoveLast(xs), xs);
    } else {
      SubseqAppendSame(Undup(RemoveLast(xs)), RemoveLast(xs), Last(xs));
      ConcatRemoveLastLast(xs);
    }
  }
}
