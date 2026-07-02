// Author: Shaobo He
// LeetCode 1192, the last mile: a VERIFIED DFS that actually constructs a DFS
// tree, closing the loop into TarjanBridgeLow.
//
// A recursive depth-first search over the graph builds par/disc/dep. DFS proves
// the result is a valid spanning tree with pre-order discovery times: WF,
// TreeInGraph, and DiscWF, and that every vertex of a connected graph is
// discovered. (The remaining DFS-tree property -- DFSProp, that every non-tree
// edge is a back edge -- is the deep no-cross-edge invariant; with it the tree
// feeds TarjanBridgeLow to decide bridges by low[v] > disc[u].)

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

// Visit vertex v (already discovered) and recurse into every white neighbour.
// Returns the extended state. Afterwards all of v's neighbours are discovered.
method DFSVisit(n: int, E: set<Edge>, v: int,
                disc0: seq<int>, par0: seq<int>, dep0: seq<int>, t0: int,
                ghost gray: set<int>)
  returns (disc1: seq<int>, par1: seq<int>, dep1: seq<int>, t1: int)
  requires InRange(E, n)
  requires PTree(n, E, disc0, par0, dep0, t0)
  requires 0 <= v < n && disc0[v] != -1
  requires forall g :: g in gray ==> 0 <= g < n && disc0[g] != -1
  requires v !in gray && BlackClosed(n, E, disc0, gray + {v})
  ensures PTree(n, E, disc1, par1, dep1, t1)
  ensures |disc1| == n && |par1| == n && |dep1| == n && t1 >= t0
  // monotone: nothing already visited changes
  ensures forall u :: (0 <= u < n && disc0[u] != -1) ==>
                        (disc1[u] == disc0[u] && par1[u] == par0[u] && dep1[u] == dep0[u])
  ensures White(n, disc1) <= White(n, disc0)
  // v is now fully explored: every neighbour is discovered
  ensures forall w :: 0 <= w < n && Adj(E, v, w) ==> disc1[w] != -1
  ensures BlackClosed(n, E, disc1, gray)
  decreases White(n, disc0)
{
  disc1, par1, dep1, t1 := disc0, par0, dep0, t0;
  var w := 0;
  while w < n
    invariant 0 <= w <= n
    invariant PTree(n, E, disc1, par1, dep1, t1) && t1 >= t0
    invariant forall u :: (0 <= u < n && disc0[u] != -1) ==>
                            (disc1[u] == disc0[u] && par1[u] == par0[u] && dep1[u] == dep0[u])
    invariant White(n, disc1) <= White(n, disc0)
    invariant disc1[v] != -1
    invariant forall g :: g in gray ==> 0 <= g < n && disc1[g] != -1
    invariant forall w' :: 0 <= w' < w && Adj(E, v, w') ==> disc1[w'] != -1
    invariant BlackClosed(n, E, disc1, gray + {v})
    decreases n - w
  {
    if Adj(E, v, w) && disc1[w] == -1 {
      // discover w as a child of v
      ghost var discPre := disc1;
      disc1 := disc1[w := t1];
      par1 := par1[w := v];
      dep1 := dep1[w := dep1[v] + 1];
      t1 := t1 + 1;
      assert disc1[w] != -1 && discPre[w] == -1;
      assert White(n, disc1) <= White(n, disc0) - {w};
      assert BlackClosed(n, E, disc1, gray + {v} + {w});
      var d, p, dp, tt := DFSVisit(n, E, w, disc1, par1, dep1, t1, gray + {v});
      disc1, par1, dep1, t1 := d, p, dp, tt;
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

// Runs DFS from vertex 0 of a connected graph and returns a genuine spanning
// tree with pre-order discovery times.
method DFS(n: int, E: set<Edge>) returns (t: Tree, disc: seq<int>)
  requires n >= 1 && InRange(E, n)
  requires forall v :: 0 <= v < n ==> Reachable(E, 0, v)   // connected from 0
  ensures t.n == n && t.root == 0 && |disc| == n
  ensures WF(t) && TreeInGraph(t, E) && DiscWF(t, disc)
  ensures forall v :: 0 <= v < n ==> disc[v] != -1
{
  var disc0 := seq(n, i requires 0 <= i < n => if i == 0 then 0 else -1);
  var par0 := seq(n, i requires 0 <= i < n => 0);
  var dep0 := seq(n, i requires 0 <= i < n => 0);
  assert PTree(n, E, disc0, par0, dep0, 1);

  var d, p, dp, tt := DFSVisit(n, E, 0, disc0, par0, dep0, 1, {});

  SpanningFromClosed(n, E, d);
  PackageTree(n, E, d, p, dp, tt);
  t := Tree(n, 0, p, dp);
  disc := d;
}
