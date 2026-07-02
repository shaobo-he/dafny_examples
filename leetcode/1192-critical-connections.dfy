// Author: Shaobo He
// LeetCode 1192: Critical Connections in a Network -- EXACT correctness.
//
// A "critical connection" (bridge) is an edge whose removal disconnects the
// network. Removing an edge {a,b} can only ever separate a from b, so the
// denotational definition is exactly:
//
//   Bridge(E, a, b)  <==>  {a,b} in E  and  a is NOT reachable from b in E-{a,b}
//
// This file proves TWO things against that single denotational definition:
//
//   1. CriticalConnections returns EXACTLY the set of bridges (both directions
//      of the set equality), via a verified reachability closure.
//
//   2. THE DEEPER THEOREM (why Tarjan's O(n) algorithm works): on a DFS tree --
//      a rooted spanning tree in which every non-tree edge joins an ancestor to
//      a descendant -- a tree edge (u = par[v], v) is a bridge iff no edge
//      escapes v's subtree, equivalently iff low[v] > disc[u]. See
//      BridgeCharacterization (cut form), TarjanBridge (criterion form), and
//      TarjanBridgeLow (literal low[v] > disc[u]), all reduced to the same
//      IsBridge. TarjanExample runs the criterion on the LeetCode graph and
//      recovers the bridge {1,3} found denotationally in Example4.

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

// =============================================================================
// THE DEEPER THEOREM: Tarjan's low-link bridge criterion.
//
// A DFS of an undirected graph yields a rooted spanning tree in which EVERY
// non-tree edge joins an ancestor to a descendant (there are no cross edges).
// On such a tree, a tree edge (u = par[v], v) is a bridge iff no graph edge
// leaves v's subtree for a proper ancestor -- equivalently low[v] > disc[u].
// We prove that characterization against the SAME denotational IsBridge above.
// =============================================================================

// ---- Reachability is an equivalence on each component -----------------------

lemma ReachableSymm(E: set<Edge>, s: int, t: int)
  requires Reachable(E, s, t)
  ensures Reachable(E, t, s)
{
  var p :| IsPath(E, p) && p[0] == s && p[|p| - 1] == t;
  var q := seq(|p|, i requires 0 <= i < |p| => p[|p| - 1 - i]);
  assert IsPath(E, q) by {
    forall i | 0 <= i < |q| - 1 ensures Adj(E, q[i], q[i + 1]) {
      assert q[i] == p[|p| - 1 - i] && q[i + 1] == p[|p| - 2 - i];
      assert Adj(E, p[|p| - 2 - i], p[|p| - 1 - i]);
    }
  }
  assert q[0] == t && q[|q| - 1] == s;
}

lemma ReachableTrans(E: set<Edge>, s: int, m: int, t: int)
  requires Reachable(E, s, m) && Reachable(E, m, t)
  ensures Reachable(E, s, t)
{
  var p :| IsPath(E, p) && p[0] == s && p[|p| - 1] == m;
  var q :| IsPath(E, q) && q[0] == m && q[|q| - 1] == t;
  var r := p + q[1..];
  assert IsPath(E, r) by {
    forall i | 0 <= i < |r| - 1 ensures Adj(E, r[i], r[i + 1]) {
      if i < |p| - 1 {
        assert r[i] == p[i] && r[i + 1] == p[i + 1];
      } else {
        assert r[i] == q[i - |p| + 1] && r[i + 1] == q[i - |p| + 2];
        assert Adj(E, q[i - |p| + 1], q[i - |p| + 2]);
      }
    }
  }
  assert r[0] == s && r[|r| - 1] == t;
}

// ---- DFS tree: a rooted spanning tree by parent + depth ---------------------

datatype Tree = Tree(n: int, root: int, par: seq<int>, dep: seq<int>)

predicate WF(t: Tree) {
  0 <= t.root < t.n &&
  |t.par| == t.n && |t.dep| == t.n &&
  t.par[t.root] == t.root && t.dep[t.root] == 0 &&
  (forall v :: 0 <= v < t.n ==> t.dep[v] >= 0) &&
  (forall v :: 0 <= v < t.n && v != t.root ==>
                 0 <= t.par[v] < t.n && t.dep[v] == t.dep[t.par[v]] + 1)
}

// w is a descendant of a (equivalently a is an ancestor of w); a == w allowed.
predicate Anc(t: Tree, a: int, w: int)
  requires WF(t) && 0 <= a < t.n && 0 <= w < t.n
  decreases t.dep[w]
{
  a == w || (w != t.root && Anc(t, a, t.par[w]))
}

// Every tree edge {par[v], v} is a graph edge (the tree spans the graph).
predicate TreeInGraph(t: Tree, E: set<Edge>) {
  WF(t) && forall v :: 0 <= v < t.n && v != t.root ==> Adj(E, t.par[v], v)
}

// The defining DFS property: no cross edges -- every graph edge is between an
// ancestor and a descendant.
predicate DFSProp(t: Tree, E: set<Edge>) {
  WF(t) &&
  forall x, y :: 0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y) ==>
                   Anc(t, x, y) || Anc(t, y, x)
}

// ---- Ancestry lemmas --------------------------------------------------------

lemma AncRefl(t: Tree, a: int)
  requires WF(t) && 0 <= a < t.n
  ensures Anc(t, a, a)
{
}

lemma AncParentStep(t: Tree, w: int)
  requires WF(t) && 0 <= w < t.n && w != t.root
  ensures Anc(t, t.par[w], w)
{
  AncRefl(t, t.par[w]);
}

lemma AncDep(t: Tree, a: int, w: int)
  requires WF(t) && 0 <= a < t.n && 0 <= w < t.n && Anc(t, a, w)
  ensures t.dep[a] <= t.dep[w]
  decreases t.dep[w]
{
  if a != w { AncDep(t, a, t.par[w]); }
}

lemma AncTrans(t: Tree, a: int, b: int, c: int)
  requires WF(t) && 0 <= a < t.n && 0 <= b < t.n && 0 <= c < t.n
  requires Anc(t, a, b) && Anc(t, b, c)
  ensures Anc(t, a, c)
  decreases t.dep[c]
{
  if b != c { AncTrans(t, a, b, t.par[c]); }
}

// A strict descendant's parent is still a descendant.
lemma AncParent(t: Tree, v: int, w: int)
  requires WF(t) && 0 <= v < t.n && 0 <= w < t.n && Anc(t, v, w) && w != v
  ensures w != t.root && Anc(t, v, t.par[w])
{
}

// A node's parent is not in the node's own subtree.
lemma ParentNotInSubtree(t: Tree, v: int)
  requires WF(t) && 0 <= v < t.n && v != t.root
  ensures !Anc(t, v, t.par[v])
{
  if Anc(t, v, t.par[v]) { AncDep(t, v, t.par[v]); }
}

// Outside a subtree, the parent is outside too.
lemma NotInSubtreeParent(t: Tree, v: int, w: int)
  requires WF(t) && 0 <= v < t.n && 0 <= w < t.n && !Anc(t, v, w) && w != t.root
  ensures !Anc(t, v, t.par[w])
{
  if Anc(t, v, t.par[w]) { assert Anc(t, v, w); }
}

// ---- Tree-path connectivity, avoiding the cut edge (u,v) --------------------

// An edge distinct (as an unordered pair) from {u,v} survives the deletion.
lemma AdjSurvives(E: set<Edge>, u: int, v: int, p: int, w: int)
  requires Adj(E, p, w)
  requires (p, w) != (u, v) && (p, w) != (v, u) && (w, p) != (u, v) && (w, p) != (v, u)
  ensures Adj(RemoveEdge(E, u, v), p, w)
{
}

// Every node in v's subtree can still reach v after deleting (par[v], v).
lemma WalkUp(t: Tree, E: set<Edge>, v: int, w: int)
  requires TreeInGraph(t, E) && 0 <= v < t.n && v != t.root && 0 <= w < t.n
  requires Anc(t, v, w)
  ensures Reachable(RemoveEdge(E, t.par[v], v), w, v)
  decreases t.dep[w]
{
  var u := t.par[v];
  var E' := RemoveEdge(E, u, v);
  if w == v {
    ReachableRefl(E', v);
  } else {
    AncParent(t, v, w);
    var p := t.par[w];
    AncDep(t, v, w);                 // dep[v] <= dep[w]
    assert w != u;                   // dep[u] = dep[v]-1 < dep[v] <= dep[w]
    assert Adj(E, p, w);
    AdjSurvives(E, u, v, p, w);
    WalkUp(t, E, v, p);              // Reachable(E', p, v)
    ReachableRefl(E', w);
    ReachableStep(E', w, w, p);      // Reachable(E', w, p)
    ReachableTrans(E', w, p, v);
  }
}

// Every node outside v's subtree can still reach the root after deleting (u,v).
lemma WalkUpComp(t: Tree, E: set<Edge>, v: int, w: int)
  requires TreeInGraph(t, E) && 0 <= v < t.n && v != t.root && 0 <= w < t.n
  requires !Anc(t, v, w)
  ensures Reachable(RemoveEdge(E, t.par[v], v), w, t.root)
  decreases t.dep[w]
{
  var u := t.par[v];
  var E' := RemoveEdge(E, u, v);
  AncRefl(t, v);
  assert w != v;                     // v is in its own subtree, w is not
  if w == t.root {
    ReachableRefl(E', t.root);
  } else {
    NotInSubtreeParent(t, v, w);     // !Anc(v, par[w])
    var p := t.par[w];
    if p == v { AncParentStep(t, w); assert Anc(t, v, w); }  // would contradict !Anc(v,w)
    assert p != v;
    assert Adj(E, p, w);
    AdjSurvives(E, u, v, p, w);
    WalkUpComp(t, E, v, p);          // Reachable(E', p, root)
    ReachableRefl(E', w);
    ReachableStep(E', w, w, p);      // Reachable(E', w, p)
    ReachableTrans(E', w, p, t.root);
  }
}

// ---- The bridge characterization --------------------------------------------

// Two ancestors of a common node are themselves ancestor-comparable (the
// ancestors of any node form a chain).
lemma AncChain(t: Tree, a: int, b: int, c: int)
  requires WF(t) && 0 <= a < t.n && 0 <= b < t.n && 0 <= c < t.n
  requires Anc(t, a, c) && Anc(t, b, c)
  ensures Anc(t, a, b) || Anc(t, b, a)
  decreases t.dep[c]
{
  if a != c && b != c {
    AncParent(t, a, c);
    AncParent(t, b, c);
    AncChain(t, a, b, t.par[c]);
  }
}

// No edge leaves v's subtree except the tree edge {u,v}.
predicate NoEscape(t: Tree, E: set<Edge>, u: int, v: int)
  requires WF(t) && 0 <= v < t.n && 0 <= u < t.n
{
  forall x, y :: (0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y)
                  && Anc(t, v, x) && !Anc(t, v, y)) ==> (x == v && y == u)
}

// THE DEEPER THEOREM (cut form): a tree edge (u = par[v], v) is a bridge iff no
// graph edge escapes v's subtree.
lemma BridgeCharacterization(t: Tree, E: set<Edge>, u: int, v: int)
  requires TreeInGraph(t, E) && DFSProp(t, E) && InRange(E, t.n)
  requires 0 <= v < t.n && v != t.root && u == t.par[v]
  ensures IsBridge(E, u, v) <==> NoEscape(t, E, u, v)
{
  var E' := RemoveEdge(E, u, v);
  var S := set w | 0 <= w < t.n && Anc(t, v, w);
  AncRefl(t, v);
  ParentNotInSubtree(t, v);
  assert Adj(E, u, v);
  assert InRange(E', t.n);
  assert !Adj(E', u, v);
  assert v in S && u !in S;

  if NoEscape(t, E, u, v) {
    forall a, b | a in S && 0 <= b < t.n && Adj(E', a, b)
      ensures b in S
    {
      assert Adj(E, a, b);
      if b !in S {
        assert Anc(t, v, a) && !Anc(t, v, b);
        assert a == v && b == u;      // NoEscape
        assert !Adj(E', v, u);        // contradiction: this edge was deleted
      }
    }
    ClosedReachableSubset(E', t.n, v, S);
    assert !Reachable(E', v, u);
    if Reachable(E', u, v) { ReachableSymm(E', u, v); }
    assert IsBridge(E, u, v);
  } else {
    var x, y :| 0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y)
                && Anc(t, v, x) && !Anc(t, v, y) && !(x == v && y == u);
    assert Anc(t, x, y) || Anc(t, y, x);          // DFSProp
    if Anc(t, x, y) { AncTrans(t, v, x, y); }     // would force Anc(v,y): impossible
    assert Anc(t, y, x);
    AncChain(t, v, y, x);                          // Anc(v,y) || Anc(y,v)
    assert Anc(t, y, v);
    assert y != v;                                 // else Anc(v,y)
    AncParent(t, y, v);                            // Anc(y, par[v]) = Anc(y, u)
    assert x != u;                                 // x in S but u not in S
    AdjSurvives(E, u, v, x, y);                    // Adj(E', x, y)
    WalkUpComp(t, E, v, u);                        // Reachable(E', u, root)
    WalkUpComp(t, E, v, y);                        // Reachable(E', y, root)
    WalkUp(t, E, v, x);                            // Reachable(E', x, v)
    ReachableSymm(E', y, t.root);
    ReachableTrans(E', u, t.root, y);              // Reachable(E', u, y)
    ReachableStep(E', u, y, x);                    // Adj(E',y,x): Reachable(E', u, x)
    ReachableTrans(E', u, x, v);                   // Reachable(E', u, v)
    assert !IsBridge(E, u, v);
  }
}

// ---- Low-link numeric layer -------------------------------------------------

// Discovery times of a DFS: a strict ancestor is discovered strictly earlier.
predicate DiscWF(t: Tree, disc: seq<int>)
  requires WF(t)
{
  |disc| == t.n &&
  forall a, w :: 0 <= a < t.n && 0 <= w < t.n && Anc(t, a, w) && a != w ==>
                   disc[a] < disc[w]
}

lemma AncDiscLe(t: Tree, disc: seq<int>, a: int, w: int)
  requires WF(t) && DiscWF(t, disc) && 0 <= a < t.n && 0 <= w < t.n && Anc(t, a, w)
  ensures disc[a] <= disc[w]
{
}

// low[v] > disc[u]: every graph edge out of v's subtree, other than the tree
// edge to a node's parent, lands at a discovery time beyond disc[u]. (This is
// exactly the value low[v] = min disc reachable from the subtree via one
// non-tree edge; see LowValueCriterion below.)
predicate LowCriterion(t: Tree, E: set<Edge>, disc: seq<int>, u: int, v: int)
  requires WF(t) && |disc| == t.n && 0 <= v < t.n && 0 <= u < t.n
{
  forall x, y :: (0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y)
                  && Anc(t, v, x) && y != t.par[x]) ==> disc[y] > disc[u]
}

// The low-link criterion coincides with the no-escape (cut) condition.
lemma LowLinkCriterion(t: Tree, E: set<Edge>, disc: seq<int>, u: int, v: int)
  requires WF(t) && TreeInGraph(t, E) && DFSProp(t, E) && DiscWF(t, disc)
  requires 0 <= v < t.n && v != t.root && u == t.par[v]
  ensures NoEscape(t, E, u, v) <==> LowCriterion(t, E, disc, u, v)
{
  AncParentStep(t, v);              // Anc(u, v)
  assert disc[u] < disc[v];         // DiscWF, u != v
  if NoEscape(t, E, u, v) {
    forall x, y | 0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y)
                  && Anc(t, v, x) && y != t.par[x]
      ensures disc[y] > disc[u]
    {
      if Anc(t, v, y) {
        AncDiscLe(t, disc, v, y);   // disc[v] <= disc[y]
      } else {
        assert x == v && y == u;    // NoEscape
        assert y == t.par[x];       // u == par[v] == par[x] -- contradicts premise
      }
    }
  } else {
    var x, y :| 0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y)
                && Anc(t, v, x) && !Anc(t, v, y) && !(x == v && y == u);
    if Anc(t, x, y) { AncTrans(t, v, x, y); }
    assert Anc(t, y, x);
    AncChain(t, v, y, x);
    assert Anc(t, y, v) && y != v;
    AncParent(t, y, v);             // Anc(y, u)
    AncDiscLe(t, disc, y, u);       // disc[y] <= disc[u]
    if y == t.par[x] {
      AncParent(t, v, x);           // x != v ==> Anc(v, par[x]) = Anc(v, y), contra
      assert x == v && y == u;      // then par[x] = par[v] = u -- excluded
    }
    assert y != t.par[x];
    assert !LowCriterion(t, E, disc, u, v);
  }
}

// THE TARJAN CRITERION: tree edge (u = par[v], v) is a bridge iff low[v] > disc[u].
lemma TarjanBridge(t: Tree, E: set<Edge>, disc: seq<int>, u: int, v: int)
  requires WF(t) && TreeInGraph(t, E) && DFSProp(t, E) && DiscWF(t, disc) && InRange(E, t.n)
  requires 0 <= v < t.n && v != t.root && u == t.par[v]
  ensures IsBridge(E, u, v) <==> LowCriterion(t, E, disc, u, v)
{
  BridgeCharacterization(t, E, u, v);
  LowLinkCriterion(t, E, disc, u, v);
}

// ---- low[v] as an actual minimum value --------------------------------------

// Minimum of a finite non-empty set of integers (postconditions prove it is a
// member and a lower bound, so callers reason about it directly).
ghost function SetMin(s: set<int>): (m: int)
  requires |s| >= 1
  ensures m in s
  ensures forall z :: z in s ==> m <= z
  decreases |s|
{
  var x :| x in s;
  if s == {x} then x
  else
    var rest := SetMin(s - {x});
    assert forall z :: z in s ==> z == x || z in s - {x};
    if x <= rest then x else rest
}

// The discovery times low[v] is the minimum of: disc[v] together with disc[y]
// over every edge {x,y} leaving the subtree of some x in subtree(v) that is not
// x's own parent edge -- i.e. the classic low-link value.
function CandidateDiscs(t: Tree, E: set<Edge>, disc: seq<int>, v: int): set<int>
  requires WF(t) && |disc| == t.n && 0 <= v < t.n
{
  {disc[v]} +
  (set x, y | 0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y) && Anc(t, v, x) && y != t.par[x]
     :: disc[y])
}

// low[v] > disc[u] holds exactly when the low-link criterion does.
lemma LowValueCriterion(t: Tree, E: set<Edge>, disc: seq<int>, u: int, v: int)
  requires WF(t) && TreeInGraph(t, E) && DiscWF(t, disc)
  requires 0 <= v < t.n && v != t.root && u == t.par[v]
  ensures SetMin(CandidateDiscs(t, E, disc, v)) > disc[u]
     <==> LowCriterion(t, E, disc, u, v)
{
  var C := CandidateDiscs(t, E, disc, v);
  assert disc[v] in C;
  AncParentStep(t, v);
  assert disc[u] < disc[v];
  if SetMin(C) > disc[u] {
    forall x, y | 0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y)
                  && Anc(t, v, x) && y != t.par[x]
      ensures disc[y] > disc[u]
    {
      assert disc[y] in C;
    }
  } else {
    var m := SetMin(C);
    assert m in C;
    if m != disc[v] {
      var x, y :| 0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y)
                  && Anc(t, v, x) && y != t.par[x] && disc[y] == m;
      assert !LowCriterion(t, E, disc, u, v);
    }
  }
}

// THE TARJAN CRITERION, literal form: a tree edge (u = par[v], v) is a bridge
// iff low[v] > disc[u].
lemma TarjanBridgeLow(t: Tree, E: set<Edge>, disc: seq<int>, u: int, v: int)
  requires WF(t) && TreeInGraph(t, E) && DFSProp(t, E) && DiscWF(t, disc) && InRange(E, t.n)
  requires 0 <= v < t.n && v != t.root && u == t.par[v]
  ensures IsBridge(E, u, v) <==> SetMin(CandidateDiscs(t, E, disc, v)) > disc[u]
{
  TarjanBridge(t, E, disc, u, v);
  LowValueCriterion(t, E, disc, u, v);
}

// ---- Non-vacuity: the low-link theorem decides the LeetCode example ----------

// DFS of {[0,1],[1,2],[2,0],[1,3]} from root 0 gives tree edges 0-1,1-2,1-3 and
// the single back edge 2-0. Running TarjanBridge on that tree reproduces exactly
// the bridge set {1,3} established denotationally in Example4.
lemma {:fuel Anc, 8} TarjanExample()
{
  var E: set<Edge> := {(0, 1), (1, 2), (2, 0), (1, 3)};
  var t := Tree(4, 0, [0, 0, 1, 1], [0, 1, 2, 2]);
  var disc := [0, 1, 2, 3];

  assert WF(t);
  assert Anc(t, 0, 1) && Anc(t, 0, 2) && Anc(t, 0, 3) && Anc(t, 1, 2) && Anc(t, 1, 3);
  assert !Anc(t, 3, 0) && !Anc(t, 3, 1) && !Anc(t, 3, 2);   // 3 is a leaf
  assert !Anc(t, 2, 0) && !Anc(t, 2, 1) && !Anc(t, 2, 3);
  assert TreeInGraph(t, E) && DFSProp(t, E) && DiscWF(t, disc) && InRange(E, 4);

  // Edge {1,3}: subtree(3) = {3}, no non-parent edge leaves it -> low[3] high.
  TarjanBridge(t, E, disc, 1, 3);
  assert LowCriterion(t, E, disc, 1, 3);       // vacuously: only edge at 3 is its parent edge
  assert IsBridge(E, 1, 3);

  // Edge {1,2}: the back edge 2-0 escapes subtree(2) to an ancestor of 1.
  TarjanBridge(t, E, disc, 1, 2);
  assert Adj(E, 2, 0) && Anc(t, 2, 2) && 0 != t.par[2] && !(disc[0] > disc[1]);
  assert !LowCriterion(t, E, disc, 1, 2);
  assert !IsBridge(E, 1, 2);

  // Edge {0,1}: the back edge 2-0 escapes subtree(1) as well.
  TarjanBridge(t, E, disc, 0, 1);
  assert Adj(E, 2, 0) && Anc(t, 1, 2) && 0 != t.par[2] && !(disc[0] > disc[0]);
  assert !LowCriterion(t, E, disc, 0, 1);
  assert !IsBridge(E, 0, 1);
}
