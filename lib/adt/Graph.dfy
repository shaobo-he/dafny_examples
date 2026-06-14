// Author: Shaobo He
// Topological sort via Kahn's algorithm, i.e. BFS over the frontier of
// vertices whose predecessors have all been emitted. (LeetCode 210,
// "Course Schedule II", is the same algorithm.)
//
// Vertices are 0..V-1. An edge (a, b) means a must appear before b.
//
// Kahn proves, with no acyclicity assumption:
//   * the output is distinct and contains only valid vertices,
//   * SOUNDNESS: for every edge whose head is emitted, its tail is emitted
//     earlier, and
//   * STALL: every un-emitted vertex still has an un-emitted predecessor
//     (so progress only stops on a cyclic remainder).
// CompleteIfAcyclic turns STALL + an acyclicity witness (a strictly
// increasing rank along edges) into completeness, and TopoSort packages
// the two into a full topological-sort guarantee.

module Graph {

  predicate ValidGraph(V: nat, E: set<(nat, nat)>) {
    forall e :: e in E ==> e.0 < V && e.1 < V
  }

  function ToSet(s: seq<nat>): set<nat> {
    set i | 0 <= i < |s| :: s[i]
  }

  // The vertex set {0, ..., n-1}, built recursively to avoid a
  // trigger-less set comprehension.
  function UpTo(n: nat): set<nat>
    ensures forall x: nat :: x in UpTo(n) <==> x < n
  {
    if n == 0 then {} else UpTo(n - 1) + {n - 1}
  }

  lemma ToSetMembership(s: seq<nat>, x: nat)
    ensures x in ToSet(s) <==> x in s
  {
  }

  lemma ToSetAppend(s: seq<nat>, x: nat)
    ensures ToSet(s + [x]) == ToSet(s) + {x}
  {
    forall y: nat
      ensures y in ToSet(s + [x]) <==> y in ToSet(s) + {x}
    {
      ToSetMembership(s + [x], y);
      ToSetMembership(s, y);
    }
  }

  predicate Distinct(s: seq<nat>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  }

  predicate AllPredsDone(E: set<(nat, nat)>, v: nat, done: set<nat>) {
    forall e :: e in E && e.1 == v ==> e.0 in done
  }

  // First index of x in s.
  function Pos(s: seq<nat>, x: nat): nat
    requires x in s
  {
    if s[0] == x then 0 else 1 + Pos(s[1..], x)
  }

  lemma PosCorrect(s: seq<nat>, x: nat)
    requires x in s
    ensures Pos(s, x) < |s| && s[Pos(s, x)] == x
  {
    if s[0] != x {
      PosCorrect(s[1..], x);
    }
  }

  lemma PosAppendOld(s: seq<nat>, y: nat, x: nat)
    requires x in s
    ensures x in s + [y] && Pos(s + [y], x) == Pos(s, x)
  {
    if s[0] != x {
      PosAppendOld(s[1..], y, x);
      assert (s + [y])[1..] == s[1..] + [y];
    }
  }

  lemma PosAppendNew(s: seq<nat>, x: nat)
    requires x !in s
    ensures x in s + [x] && Pos(s + [x], x) == |s|
  {
    if |s| > 0 {
      PosAppendNew(s[1..], x);
      assert (s + [x])[1..] == s[1..] + [x];
    }
  }

  method Kahn(V: nat, E: set<(nat, nat)>) returns (order: seq<nat>)
    requires ValidGraph(V, E)
    ensures Distinct(order)
    ensures forall x :: x in order ==> x < V
    ensures forall e :: e in E && e.1 in ToSet(order) ==>
                          e.0 in ToSet(order) && Pos(order, e.0) < Pos(order, e.1)
    ensures forall v: nat :: v < V && v !in ToSet(order) ==>
                               exists e :: e in E && e.1 == v && e.0 !in ToSet(order)
  {
    order := [];
    var done: set<nat> := {};
    var queue: set<nat> := set v: nat | v < V && AllPredsDone(E, v, {});
    ghost var allV: set<nat> := UpTo(V);

    while queue != {}
      invariant done == ToSet(order)
      invariant done <= allV
      invariant Distinct(order)
      invariant forall x :: x in order ==> x < V
      invariant forall w :: w in queue ==> w < V && AllPredsDone(E, w, done) && w !in done
      invariant forall e :: e in E && e.1 in done ==>
                              e.0 in done && Pos(order, e.0) < Pos(order, e.1)
      invariant forall v: nat :: v < V && AllPredsDone(E, v, done) && v !in done ==> v in queue
      decreases allV - done
    {
      var u :| u in queue;
      ghost var olddone := done;
      ghost var oldorder := order;
      var oldqueue := queue;

      ToSetMembership(oldorder, u);
      assert u !in oldorder;

      order := order + [u];
      done := done + {u};
      ToSetAppend(oldorder, u);
      var newReady := set v: nat | v < V && (u, v) in E
                                   && AllPredsDone(E, v, done) && v !in done;
      queue := (oldqueue - {u}) + newReady;

      // Soundness is maintained.
      forall e | e in E && e.1 in done
        ensures e.0 in done && Pos(order, e.0) < Pos(order, e.1)
      {
        if e.1 in olddone {
          // e.0 in olddone by the old soundness invariant; positions unchanged.
          ToSetMembership(oldorder, e.0);
          ToSetMembership(oldorder, e.1);
          PosAppendOld(oldorder, u, e.0);
          PosAppendOld(oldorder, u, e.1);
        } else {
          // e.1 == u, so e.0 is a predecessor of u and already emitted.
          assert e.1 == u;
          assert e.0 in olddone;
          ToSetMembership(oldorder, e.0);
          PosCorrect(oldorder, e.0);
          PosAppendOld(oldorder, u, e.0);
          PosAppendNew(oldorder, u);
        }
      }

      // The frontier still contains every ready, un-emitted vertex.
      forall v: nat | v < V && AllPredsDone(E, v, done) && v !in done
        ensures v in queue
      {
        if AllPredsDone(E, v, olddone) {
          assert v in oldqueue;
          assert v != u;
        } else {
          assert exists e :: e in E && e.1 == v && e.0 !in olddone;
          var e :| e in E && e.1 == v && e.0 !in olddone;
          assert e.0 in done;
          assert e.0 == u;
          assert v in newReady;
        }
      }
    }

    // queue is empty: derive STALL from the frontier invariant.
    forall v: nat | v < V && v !in ToSet(order)
      ensures exists e :: e in E && e.1 == v && e.0 !in ToSet(order)
    {
      assert v !in done;
      assert !AllPredsDone(E, v, done);
      var e :| e in E && e.1 == v && e.0 !in done;
    }
  }

  // A non-empty finite vertex set has an element of minimal rank.
  lemma MinByRank(S: set<nat>, rank: seq<nat>)
    requires S != {}
    requires forall v :: v in S ==> v < |rank|
    ensures exists m :: m in S && forall w :: w in S ==> rank[m] <= rank[w]
    decreases S
  {
    var x :| x in S;
    if S != {x} {
      var S' := S - {x};
      assert x in S && S' < S;
      MinByRank(S', rank);
      var m' :| m' in S' && forall w :: w in S' ==> rank[m'] <= rank[w];
      if rank[x] > rank[m'] {
        assert forall w :: w in S ==> rank[m'] <= rank[w];
      }
    }
  }

  // STALL plus a strictly-increasing rank along edges (an acyclicity
  // witness) forces every vertex to be emitted.
  lemma CompleteIfAcyclic(V: nat, E: set<(nat, nat)>, done: set<nat>, rank: seq<nat>)
    requires |rank| == V
    requires forall e :: e in E ==> e.0 < V && e.1 < V && rank[e.0] < rank[e.1]
    requires forall v: nat :: v < V && v !in done ==>
                                exists e :: e in E && e.1 == v && e.0 !in done
    ensures forall v: nat :: v < V ==> v in done
  {
    var S := set v: nat | v < V && v !in done;
    if S != {} {
      MinByRank(S, rank);
      var m :| m in S && forall w :: w in S ==> rank[m] <= rank[w];
      var e :| e in E && e.1 == m && e.0 !in done;
      assert e.0 in S;
      assert rank[e.0] < rank[m] && rank[m] <= rank[e.0];
      assert false;
    }
    forall v: nat | v < V
      ensures v in done
    {
      assert v !in S;
    }
  }

  // Full topological sort, given a rank function witnessing acyclicity.
  method TopoSort(V: nat, E: set<(nat, nat)>, ghost rank: seq<nat>)
    returns (order: seq<nat>)
    requires ValidGraph(V, E)
    requires |rank| == V
    requires forall e :: e in E ==> rank[e.0] < rank[e.1]
    ensures Distinct(order)
    ensures forall v: nat :: v < V <==> v in ToSet(order)
    ensures forall e :: e in E ==>
                          e.0 in ToSet(order) && e.1 in ToSet(order)
                          && Pos(order, e.0) < Pos(order, e.1)
  {
    order := Kahn(V, E);
    CompleteIfAcyclic(V, E, ToSet(order), rank);
    forall v: nat
      ensures v < V <==> v in ToSet(order)
    {
      ToSetMembership(order, v);
    }
  }
}
