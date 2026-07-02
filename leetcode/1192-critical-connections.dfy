// Author: Shaobo He
// LeetCode 1192: Critical Connections in a Network -- EXACT correctness.
//
// A "critical connection" (bridge) is an edge whose removal disconnects the
// network. Removing an edge {a,b} can only ever separate a from b, so the
// denotational definition is exactly:
//
//   Bridge(E, a, b)  <==>  {a,b} in E  and  a is NOT reachable from b in E-{a,b}
//
// This file proves CriticalConnections returns EXACTLY that set of edges -- both
// directions of the set equality -- against a first-principles path/reachability
// model. (The O(n) Tarjan low-link algorithm is a performance optimisation whose
// separate correctness rests on the DFS-tree / low-link theorem; the exact
// bridge SET, proved here, is the genuine content.)

// An undirected graph is a set of directed pairs read symmetrically.
type Edge = (int, int)

predicate Adj(E: set<Edge>, u: int, v: int) {
  (u, v) in E || (v, u) in E
}

// A path is a non-empty vertex sequence with an edge between consecutive nodes.
predicate IsPath(E: set<Edge>, p: seq<int>) {
  |p| >= 1 && forall i :: 0 <= i < |p| - 1 ==> Adj(E, p[i], p[i + 1])
}

ghost predicate Reachable(E: set<Edge>, s: int, t: int) {
  exists p :: IsPath(E, p) && p[0] == s && p[|p| - 1] == t
}

predicate InRange(E: set<Edge>, n: int) {
  forall e :: e in E ==> 0 <= e.0 < n && 0 <= e.1 < n
}

// ---- Basic reachability facts ------------------------------------------------

lemma ReachableRefl(E: set<Edge>, s: int)
  ensures Reachable(E, s, s)
{
  assert IsPath(E, [s]);
}

lemma ReachableStep(E: set<Edge>, s: int, t: int, u: int)
  requires Reachable(E, s, t) && Adj(E, t, u)
  ensures Reachable(E, s, u)
{
  var p :| IsPath(E, p) && p[0] == s && p[|p| - 1] == t;
  var q := p + [u];
  assert IsPath(E, q) by {
    forall i | 0 <= i < |q| - 1 ensures Adj(E, q[i], q[i + 1]) {
      if i < |p| - 1 { assert q[i] == p[i] && q[i + 1] == p[i + 1]; }
      else { assert q[i] == t && q[i + 1] == u; }
    }
  }
  assert q[0] == s && q[|q| - 1] == u;
}

// Adjacency in an in-range graph keeps both endpoints in range.
lemma AdjInRange(E: set<Edge>, n: int, u: int, v: int)
  requires InRange(E, n) && Adj(E, u, v)
  ensures 0 <= u < n && 0 <= v < n
{
}

// A path that starts inside a neighbour-closed set R stays in R.
lemma PathInClosed(E: set<Edge>, n: int, R: set<int>, p: seq<int>)
  requires IsPath(E, p) && p[0] in R
  requires InRange(E, n)
  requires forall u, v :: u in R && 0 <= v < n && Adj(E, u, v) ==> v in R
  ensures p[|p| - 1] in R
  decreases |p|
{
  if |p| >= 2 {
    assert Adj(E, p[0], p[1]);
    AdjInRange(E, n, p[0], p[1]);
    assert p[1] in R;
    assert IsPath(E, p[1..]);
    PathInClosed(E, n, R, p[1..]);
  }
}

// Hence a neighbour-closed set containing s contains everything reachable from s.
lemma ClosedReachableSubset(E: set<Edge>, n: int, s: int, R: set<int>)
  requires s in R && InRange(E, n)
  requires forall u, v :: u in R && 0 <= v < n && Adj(E, u, v) ==> v in R
  ensures forall t :: 0 <= t < n && Reachable(E, s, t) ==> t in R
{
  forall t | 0 <= t < n && Reachable(E, s, t)
    ensures t in R
  {
    var p :| IsPath(E, p) && p[0] == s && p[|p| - 1] == t;
    PathInClosed(E, n, R, p);
  }
}

// ---- Verified reachability computation ---------------------------------------

// Returns EXACTLY the set of vertices reachable from s: grow a frontier by its
// neighbours until closed, then the closure lemma pins down completeness.
method ComputeReachable(n: int, E: set<Edge>, s: int) returns (R: set<int>)
  requires 0 <= s < n && InRange(E, n)
  ensures R == set w | 0 <= w < n && Reachable(E, s, w)
{
  ReachableRefl(E, s);
  R := {s};
  ghost var Target := set w | 0 <= w < n && Reachable(E, s, w);
  var changed := true;
  while changed
    invariant s in R
    invariant forall w :: w in R ==> 0 <= w < n && Reachable(E, s, w)
    invariant R <= Target
    invariant changed ||
              (forall u, v {:trigger Adj(E, u, v)} ::
                 u in R && 0 <= v < n && Adj(E, u, v) ==> v in R)
    decreases Target - R, if changed then 1 else 0
  {
    var newNodes := set u, v | u in R && 0 <= v < n && Adj(E, u, v) && v !in R :: v;
    if newNodes == {} {
      forall u, v {:trigger Adj(E, u, v)} | u in R && 0 <= v < n && Adj(E, u, v)
        ensures v in R
      {
        if v !in R { assert v in newNodes; }
      }
      changed := false;
    } else {
      forall v | v in newNodes
        ensures 0 <= v < n && Reachable(E, s, v)
      {
        var u :| u in R && 0 <= v < n && Adj(E, u, v) && v !in R;
        ReachableStep(E, s, u, v);
      }
      R := R + newNodes;
    }
  }
  ClosedReachableSubset(E, n, s, R);
  assert R == set w | 0 <= w < n && Reachable(E, s, w);
}

// ---- Bridges ----------------------------------------------------------------

// The undirected edge {a,b} deleted (both stored orientations).
function RemoveEdge(E: set<Edge>, a: int, b: int): set<Edge> {
  E - {(a, b), (b, a)}
}

// A bridge / critical connection: an edge whose deletion leaves its endpoints
// mutually unreachable.
ghost predicate IsBridge(E: set<Edge>, a: int, b: int) {
  Adj(E, a, b) && !Reachable(RemoveEdge(E, a, b), a, b)
}

// THE THEOREM: the returned set is EXACTLY the set of bridges of E. Each edge is
// tested by deleting it and asking whether its endpoints are still connected --
// answered by the verified reachability closure.
method CriticalConnections(n: int, E: set<Edge>) returns (bridges: set<Edge>)
  requires n >= 1 && InRange(E, n)
  ensures bridges == set e | e in E && IsBridge(E, e.0, e.1)
{
  bridges := {};
  var remaining := E;
  while remaining != {}
    invariant remaining <= E
    invariant bridges == set e | e in E - remaining && IsBridge(E, e.0, e.1)
    decreases remaining
  {
    var e :| e in remaining;
    var a, b := e.0, e.1;
    assert e == (a, b) && (a, b) in E;
    assert Adj(E, a, b);

    var R := ComputeReachable(n, RemoveEdge(E, a, b), a);
    assert b in R <==> Reachable(RemoveEdge(E, a, b), a, b);   // b is in range

    if b !in R {
      bridges := bridges + {e};
    }
    remaining := remaining - {e};
  }
}

// ---- Concrete LeetCode examples ---------------------------------------------

lemma ReachableWitness(E: set<Edge>, p: seq<int>)
  requires IsPath(E, p)
  ensures Reachable(E, p[0], p[|p| - 1])
{
}

// A vertex with no incident edges is unreachable from any other vertex.
lemma NoNeighborNotReachable(E: set<Edge>, s: int, t: int)
  requires s != t
  requires forall v :: !Adj(E, t, v)
  ensures !Reachable(E, s, t)
{
  if Reachable(E, s, t) {
    var p :| IsPath(E, p) && p[0] == s && p[|p| - 1] == t;
    assert |p| >= 2;
    assert Adj(E, p[|p| - 2], p[|p| - 1]);   // consecutive edge into t
    assert Adj(E, t, p[|p| - 2]);            // Adj is symmetric
  }
}

// n = 4, connections = [[0,1],[1,2],[2,0],[1,3]] -> only [1,3] is critical.
lemma Example4()
  ensures (set e | e in {(0, 1), (1, 2), (2, 0), (1, 3)} && IsBridge({(0, 1), (1, 2), (2, 0), (1, 3)}, e.0, e.1))
       == {(1, 3)}
{
  var E: set<Edge> := {(0, 1), (1, 2), (2, 0), (1, 3)};
  // [1,3] is a bridge: deleting it isolates vertex 3.
  assert forall v :: !Adj(RemoveEdge(E, 1, 3), 3, v);
  NoNeighborNotReachable(RemoveEdge(E, 1, 3), 1, 3);
  assert IsBridge(E, 1, 3);
  // The triangle edges are not bridges: each has an alternate two-hop path.
  ReachableWitness(RemoveEdge(E, 0, 1), [0, 2, 1]);
  ReachableWitness(RemoveEdge(E, 1, 2), [1, 0, 2]);
  ReachableWitness(RemoveEdge(E, 2, 0), [2, 1, 0]);
  assert !IsBridge(E, 0, 1) && !IsBridge(E, 1, 2) && !IsBridge(E, 2, 0);
}

// n = 2, connections = [[0,1]] -> the lone edge is critical.
lemma Example2()
  ensures (set e | e in {(0, 1)} && IsBridge({(0, 1)}, e.0, e.1)) == {(0, 1)}
{
  var E: set<Edge> := {(0, 1)};
  assert forall v :: !Adj(RemoveEdge(E, 0, 1), 1, v);
  NoNeighborNotReachable(RemoveEdge(E, 0, 1), 0, 1);
  assert IsBridge(E, 0, 1);
}
