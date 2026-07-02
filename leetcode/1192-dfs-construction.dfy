// Author: Shaobo He
// LeetCode 1192, the last mile: a VERIFIED DFS that actually constructs a DFS
// tree, closing the loop into TarjanBridgeLow.
//
// A recursive depth-first search over the graph builds par/disc/dep. DFS proves
// the result is a GENUINE DFS tree of a connected graph: a spanning tree with
// pre-order discovery times (WF, TreeInGraph, DiscWF) whose non-tree edges are
// all back edges (DFSProp). The no-cross-edge invariant -- the deep part -- is
// carried as an immutable ghost `ancSet[w]` (w's ancestors, recorded when w is
// discovered), maintained via the black-closed frontier: a finished vertex has
// no white neighbours, so a freshly discovered vertex's already-seen neighbours
// are all on the current stack, i.e. its ancestors. BridgesViaTarjan then feeds
// the tree to TarjanBridgeLow: every tree edge is a bridge iff low[v] > disc[u].

include "1192-critical-connections.dfy"

// A partially-built tree over the visited vertices (disc[v] == -1 means white).
// Discovery times are a pre-order: a parent is visited strictly before its
// child, all times lie in [0, time), and are distinct.
predicate PTree(n: int, E: set<Edge>, disc: seq<int>, par: seq<int>, dep: seq<int>, time: int)
{
  n >= 1 && |disc| == n && |par| == n && |dep| == n && time >= 1 &&
  disc[0] == 0 && par[0] == 0 && dep[0] == 0 &&
  (forall v :: 0 <= v < n && disc[v] != -1 ==> 0 <= disc[v] < time && dep[v] >= 0) &&
  (forall v :: 0 <= v < n && disc[v] != -1 && v != 0 ==>
                 0 <= par[v] < n && disc[par[v]] != -1 && disc[par[v]] < disc[v] &&
                 dep[v] == dep[par[v]] + 1 && Adj(E, par[v], v)) &&
  (forall a, b :: (0 <= a < n && 0 <= b < n && disc[a] != -1 && disc[b] != -1 && a != b)
                  ==> disc[a] != disc[b])
}

// The white (unvisited) vertices -- the DFS termination measure.
ghost function White(n: int, disc: seq<int>): set<int>
  requires |disc| == n
{
  set u {:trigger disc[u]} | 0 <= u < n && disc[u] == -1
}

// Every finished (black = visited, not on the current stack `gray`) vertex has
// all of its neighbours discovered. This is what forbids cross edges.
predicate BlackClosed(n: int, E: set<Edge>, disc: seq<int>, gray: set<int>)
  requires |disc| == n
{
  forall u :: (0 <= u < n && disc[u] != -1 && u !in gray) ==>
                (forall w :: (0 <= w < n && Adj(E, u, w)) ==> disc[w] != -1)
}

// ancSet[w] is the (immutable, recorded-at-discovery) set of w's tree ancestors,
// kept consistent with par: ancSet[w] == ancSet[par[w]] + {par[w]}.
predicate AncSetInv(n: int, disc: seq<int>, par: seq<int>, ancSet: seq<set<int>>)
  requires n >= 1 && |disc| == n && |par| == n && |ancSet| == n
{
  ancSet[0] == {} &&
  (forall w :: (0 <= w < n && disc[w] != -1 && w != 0) ==>
                 0 <= par[w] < n && ancSet[w] == ancSet[par[w]] + {par[w]})
}

// Recorded ancestors are discovered strictly earlier (so a fresh node is in no
// existing ancestor set).
predicate AncSetBounded(n: int, disc: seq<int>, ancSet: seq<set<int>>)
  requires |disc| == n && |ancSet| == n
{
  forall u, a :: (0 <= u < n && disc[u] != -1 && a in ancSet[u]) ==>
                   0 <= a < n && disc[a] != -1 && disc[a] < disc[u]
}

// No cross edges: adjacent discovered vertices are ancestor-comparable.
predicate NoCross(n: int, E: set<Edge>, disc: seq<int>, ancSet: seq<set<int>>)
  requires |disc| == n && |ancSet| == n
{
  forall x, y :: (0 <= x < n && 0 <= y < n && disc[x] != -1 && disc[y] != -1
                  && Adj(E, x, y) && x != y) ==> (x in ancSet[y] || y in ancSet[x])
}

// Discovering w (a fresh leaf whose already-discovered neighbours all lie in
// `stack`) preserves NoCross.
lemma NoCrossExtend(n: int, E: set<Edge>, discPre: seq<int>, ancPre: seq<set<int>>,
                    disc1: seq<int>, ancSet1: seq<set<int>>, w: int, stack: set<int>)
  requires |discPre| == n && |ancPre| == n && |disc1| == n && |ancSet1| == n
  requires 0 <= w < n && discPre[w] == -1 && disc1[w] != -1 && ancSet1[w] == stack
  requires forall u :: (0 <= u < n && u != w) ==>
                         disc1[u] == discPre[u] && ancSet1[u] == ancPre[u]
  requires NoCross(n, E, discPre, ancPre)
  requires forall u :: (0 <= u < n && discPre[u] != -1 && Adj(E, u, w)) ==> u in stack
  ensures NoCross(n, E, disc1, ancSet1)
{
  forall x, y | 0 <= x < n && 0 <= y < n && disc1[x] != -1 && disc1[y] != -1
                && Adj(E, x, y) && x != y
    ensures x in ancSet1[y] || y in ancSet1[x]
  {
    if x == w {
      assert Adj(E, y, w) && discPre[y] != -1;   // y in stack == ancSet1[x]
    } else if y == w {
      assert Adj(E, x, w) && discPre[x] != -1;   // x in stack == ancSet1[y]
    }
  }
}

// Visit vertex v (already discovered) and recurse into every white neighbour.
// Returns the extended state. Afterwards all of v's neighbours are discovered.
method DFSVisit(n: int, E: set<Edge>, v: int,
                disc0: seq<int>, par0: seq<int>, dep0: seq<int>, t0: int,
                ghost gray: set<int>, ghost ancSet0: seq<set<int>>)
  returns (disc1: seq<int>, par1: seq<int>, dep1: seq<int>, t1: int, ghost ancSet1: seq<set<int>>)
  requires InRange(E, n)
  requires PTree(n, E, disc0, par0, dep0, t0)
  requires 0 <= v < n && disc0[v] != -1
  requires |ancSet0| == n && gray == ancSet0[v]
  requires AncSetInv(n, disc0, par0, ancSet0) && AncSetBounded(n, disc0, ancSet0)
  requires NoCross(n, E, disc0, ancSet0)
  requires forall g :: g in gray ==> 0 <= g < n && disc0[g] != -1
  requires v !in gray && BlackClosed(n, E, disc0, gray + {v})
  ensures PTree(n, E, disc1, par1, dep1, t1)
  ensures |disc1| == n && |par1| == n && |dep1| == n && t1 >= t0 && |ancSet1| == n
  // monotone: nothing already visited changes
  ensures forall u :: (0 <= u < n && disc0[u] != -1) ==>
                        (disc1[u] == disc0[u] && par1[u] == par0[u] && dep1[u] == dep0[u]
                         && ancSet1[u] == ancSet0[u])
  ensures White(n, disc1) <= White(n, disc0)
  ensures forall w :: 0 <= w < n && Adj(E, v, w) ==> disc1[w] != -1
  ensures BlackClosed(n, E, disc1, gray)
  ensures AncSetInv(n, disc1, par1, ancSet1) && AncSetBounded(n, disc1, ancSet1)
  ensures NoCross(n, E, disc1, ancSet1)
  decreases White(n, disc0)
{
  disc1, par1, dep1, t1, ancSet1 := disc0, par0, dep0, t0, ancSet0;
  var w := 0;
  while w < n
    invariant 0 <= w <= n
    invariant PTree(n, E, disc1, par1, dep1, t1) && t1 >= t0 && |ancSet1| == n
    invariant forall u :: (0 <= u < n && disc0[u] != -1) ==>
                            (disc1[u] == disc0[u] && par1[u] == par0[u] && dep1[u] == dep0[u]
                             && ancSet1[u] == ancSet0[u])
    invariant White(n, disc1) <= White(n, disc0)
    invariant disc1[v] != -1
    invariant forall g :: g in gray ==> 0 <= g < n && disc1[g] != -1
    invariant forall w' :: 0 <= w' < w && Adj(E, v, w') ==> disc1[w'] != -1
    invariant BlackClosed(n, E, disc1, gray + {v})
    invariant AncSetInv(n, disc1, par1, ancSet1) && AncSetBounded(n, disc1, ancSet1)
    invariant NoCross(n, E, disc1, ancSet1)
    decreases n - w
  {
    if Adj(E, v, w) && disc1[w] == -1 {
      // discover w as a child of v; record its ancestor set
      ghost var discPre := disc1;
      ghost var ancPre := ancSet1;
      assert ancSet1[v] == gray;                    // v visited => ancSet unchanged from entry
      disc1 := disc1[w := t1];
      par1 := par1[w := v];
      dep1 := dep1[w := dep1[v] + 1];
      ancSet1 := ancSet1[w := gray + {v}];
      t1 := t1 + 1;
      assert disc1[w] != -1 && discPre[w] == -1;
      assert White(n, disc1) <= White(n, disc0) - {w};
      assert BlackClosed(n, E, disc1, gray + {v} + {w});
      // every already-discovered neighbour of w is on the stack gray+{v}
      forall u | 0 <= u < n && discPre[u] != -1 && Adj(E, u, w)
        ensures u in gray + {v}
      {
        if u !in gray + {v} { assert disc1[w] == -1; }   // BlackClosed contradiction
      }
      NoCrossExtend(n, E, discPre, ancPre, disc1, ancSet1, w, gray + {v});
      var d, p, dp, tt, as1 := DFSVisit(n, E, w, disc1, par1, dep1, t1, gray + {v}, ancSet1);
      disc1, par1, dep1, t1, ancSet1 := d, p, dp, tt, as1;
    }
    w := w + 1;
  }
}

// ---- Top-level DFS: a spanning pre-order tree of a connected graph ----------

// Discovery times increase strictly down any ancestor chain.
lemma DiscStrict(t: Tree, disc: seq<int>, a: int, w: int)
  requires WF(t) && |disc| == t.n
  requires forall x :: 0 <= x < t.n && x != t.root ==> disc[t.par[x]] < disc[x]
  requires 0 <= a < t.n && 0 <= w < t.n && Anc(t, a, w)
  ensures a == w || disc[a] < disc[w]
  decreases t.dep[w]
{
  if a != w { DiscStrict(t, disc, a, t.par[w]); }
}

// A closed visited set in a connected graph covers everything (spanning).
lemma SpanningFromClosed(n: int, E: set<Edge>, d: seq<int>)
  requires n >= 1 && InRange(E, n) && |d| == n && d[0] != -1
  requires BlackClosed(n, E, d, {})
  requires forall v :: 0 <= v < n ==> Reachable(E, 0, v)
  ensures forall v :: 0 <= v < n ==> d[v] != -1
{
  ghost var Visited := set u {:trigger d[u]} | 0 <= u < n && d[u] != -1;
  assert 0 in Visited;
  assert forall a, b :: (a in Visited && 0 <= b < n && Adj(E, a, b)) ==> b in Visited;
  ClosedReachableSubset(E, n, 0, Visited);
  forall v | 0 <= v < n
    ensures d[v] != -1
  {
    assert Reachable(E, 0, v) && v in Visited;
  }
}

// A fully-discovered PTree is a well-formed spanning tree with pre-order disc.
lemma PackageTree(n: int, E: set<Edge>, disc: seq<int>, par: seq<int>, dep: seq<int>, tm: int)
  requires PTree(n, E, disc, par, dep, tm)
  requires forall v :: 0 <= v < n ==> disc[v] != -1
  ensures WF(Tree(n, 0, par, dep))
  ensures TreeInGraph(Tree(n, 0, par, dep), E)
  ensures DiscWF(Tree(n, 0, par, dep), disc)
{
  var t := Tree(n, 0, par, dep);
  assert WF(t);
  assert forall x :: 0 <= x < t.n && x != t.root ==> disc[t.par[x]] < disc[x];
  forall a, w | 0 <= a < t.n && 0 <= w < t.n && Anc(t, a, w) && a != w
    ensures disc[a] < disc[w]
  {
    DiscStrict(t, disc, a, w);
  }
}

// A recorded ancestor really is a tree ancestor.
lemma AncSetToAnc(t: Tree, disc: seq<int>, ancSet: seq<set<int>>, a: int, w: int)
  requires WF(t) && t.root == 0 && |disc| == t.n && |ancSet| == t.n
  requires forall v :: 0 <= v < t.n ==> disc[v] != -1
  requires AncSetInv(t.n, disc, t.par, ancSet)
  requires 0 <= a < t.n && 0 <= w < t.n && a in ancSet[w]
  ensures Anc(t, a, w)
  decreases t.dep[w]
{
  assert w != t.root;                    // ancSet[root] == {}
  if a == t.par[w] {
    AncParentStep(t, w);
  } else {
    AncSetToAnc(t, disc, ancSet, a, t.par[w]);
  }
}

// NoCross over recorded ancestors gives DFSProp over the tree.
lemma DFSPropFromNoCross(t: Tree, E: set<Edge>, disc: seq<int>, ancSet: seq<set<int>>)
  requires WF(t) && t.root == 0 && |disc| == t.n && |ancSet| == t.n
  requires forall v :: 0 <= v < t.n ==> disc[v] != -1
  requires AncSetInv(t.n, disc, t.par, ancSet)
  requires NoCross(t.n, E, disc, ancSet)
  ensures DFSProp(t, E)
{
  forall x, y | 0 <= x < t.n && 0 <= y < t.n && Adj(E, x, y)
    ensures Anc(t, x, y) || Anc(t, y, x)
  {
    if x == y {
      AncRefl(t, x);
    } else if x in ancSet[y] {
      AncSetToAnc(t, disc, ancSet, x, y);
    } else {
      AncSetToAnc(t, disc, ancSet, y, x);
    }
  }
}

// Runs DFS from vertex 0 of a connected graph and returns a genuine DFS tree:
// a spanning pre-order tree whose non-tree edges are all back edges (DFSProp).
method DFS(n: int, E: set<Edge>) returns (t: Tree, disc: seq<int>)
  requires n >= 1 && InRange(E, n)
  requires forall v :: 0 <= v < n ==> Reachable(E, 0, v)   // connected from 0
  ensures t.n == n && t.root == 0 && |disc| == n
  ensures WF(t) && TreeInGraph(t, E) && DiscWF(t, disc) && DFSProp(t, E)
  ensures forall v :: 0 <= v < n ==> disc[v] != -1
{
  var disc0 := seq(n, i requires 0 <= i < n => if i == 0 then 0 else -1);
  var par0 := seq(n, i requires 0 <= i < n => 0);
  var dep0 := seq(n, i requires 0 <= i < n => 0);
  ghost var ancSet0: seq<set<int>> := seq(n, i requires 0 <= i < n => {});
  assert PTree(n, E, disc0, par0, dep0, 1);

  var d, p, dp, tt;
  ghost var ancF;
  d, p, dp, tt, ancF := DFSVisit(n, E, 0, disc0, par0, dep0, 1, {}, ancSet0);

  SpanningFromClosed(n, E, d);
  PackageTree(n, E, d, p, dp, tt);
  t := Tree(n, 0, p, dp);
  disc := d;
  DFSPropFromNoCross(t, E, d, ancF);
}

// ---- The complete pipeline --------------------------------------------------

// Run DFS on a connected graph, then EVERY tree edge's bridge status is decided
// by Tarjan's low[v] > disc[u]. This closes the loop: construction (DFS) +
// criterion (TarjanBridgeLow), all against the denotational IsBridge.
method BridgesViaTarjan(n: int, E: set<Edge>) returns (t: Tree, disc: seq<int>)
  requires n >= 1 && InRange(E, n)
  requires forall v :: 0 <= v < n ==> Reachable(E, 0, v)   // connected
  ensures WF(t) && TreeInGraph(t, E) && DFSProp(t, E) && DiscWF(t, disc)
  ensures t.n == n && t.root == 0 && forall v :: 0 <= v < n ==> disc[v] != -1
  ensures forall v :: (0 <= v < n && v != t.root) ==>
                        (IsBridge(E, t.par[v], v)
                         <==> SetMin(CandidateDiscs(t, E, disc, v)) > disc[t.par[v]])
{
  t, disc := DFS(n, E);
  forall v | 0 <= v < n && v != t.root
    ensures IsBridge(E, t.par[v], v)
       <==> SetMin(CandidateDiscs(t, E, disc, v)) > disc[t.par[v]]
  {
    TarjanBridgeLow(t, E, disc, t.par[v], v);
  }
}
