// Author: Shaobo He
// LeetCode 407: Trapping Rain Water II
//
// Flood the m x n height map inward from the boundary using a min-priority
// queue (the verified leftist heap in lib/adt/PriorityQueue.dfy): repeatedly
// pop the lowest water level on the frontier and, for each unvisited neighbour,
// trap max(0, level - height) and push it back at level max(level, height).
//
// HeapFloodNonnegative proves memory safety, termination, and non-negative
// output for the heap-flood implementation. It is deliberately not exposed as
// the full LeetCode solution: this file does not prove the heap flood equivalent
// to the denotational escape-level specification in
// 0407-trapping-rain-water-ii-correct.dfy.

include "0407-trapping-rain-water-ii-correct.dfy"
include "../lib/adt/PriorityQueue.dfy"

import opened PriorityQueue

lemma SubsetCard(a: set<(int, int)>, b: set<(int, int)>)
  requires a <= b
  ensures |a| <= |b|
{
  if a != {} {
    var x :| x in a;
    SubsetCard(a - {x}, b - {x});
  }
}

lemma BoundaryOnlyAllVisited(m: int, n: int, AC: set<(int, int)>, visited: set<(int, int)>)
  requires m >= 1 && n >= 1
  requires AC == set a, b | 0 <= a < m && 0 <= b < n :: (a, b)
  requires visited <= AC
  requires m <= 2 || n <= 2
  requires forall a, b :: (0 <= a < m && 0 <= b < n &&
                           (a == 0 || a == m - 1 || b == 0 || b == n - 1)) ==> (a, b) in visited
  ensures visited == AC
{
  forall p | p in AC
    ensures p in visited
  {
    assert 0 <= p.0 < m && 0 <= p.1 < n;
    if m <= 2 {
      assert p.0 == 0 || p.0 == m - 1;
    } else {
      assert n <= 2;
      assert p.1 == 0 || p.1 == n - 1;
    }
  }
}
// One frontier expansion step onto neighbour (x, y). Either (x, y) is out of
// bounds / already seen (nothing changes) or it is trapped and pushed. In both
// cases the termination measure (|AC| - |visited|) + Size(heap) is preserved.
method ProcessNeighbor(heightMap: seq<seq<int>>, m: int, n: int, ghost AC: set<(int, int)>,
                       h: int, x: int, y: int,
                       water: int, visited: set<(int, int)>, heap: PQ<(int, int)>)
  returns (water': int, visited': set<(int, int)>, heap': PQ<(int, int)>)
  requires m == |heightMap| && m >= 1 && n >= 1
  requires forall i :: 0 <= i < m ==> |heightMap[i]| == n
  requires AC == set a, b | 0 <= a < m && 0 <= b < n :: (a, b)
  requires water >= 0
  requires HeapOrdered(heap)
  requires visited <= AC
  requires forall e :: e in Items(heap) ==> e.1 in visited
  ensures water' >= 0
  ensures HeapOrdered(heap')
  ensures visited <= visited' <= AC
  ensures forall e :: e in Items(heap') ==> e.1 in visited'
  ensures (|AC| - |visited'|) + Size(heap') == (|AC| - |visited|) + Size(heap)
  ensures (((0 <= x < m && 0 <= y < n) ==> (x, y) in visited)) ==> water' == water && visited' == visited && heap' == heap
{
  if 0 <= x < m && 0 <= y < n && (x, y) !in visited {
    var height := heightMap[x][y];
    var level := if h > height then h else height;
    water' := water + (if h > height then h - height else 0);
    assert (x, y) in AC;
    visited' := visited + {(x, y)};
    InsertCorrect(level, (x, y), heap);
    heap' := Insert(level, (x, y), heap);
  } else {
    water', visited', heap' := water, visited, heap;
  }
}

method HeapFloodNonnegative(heightMap: seq<seq<int>>, n: int) returns (water: int)
  requires |heightMap| >= 1 && n >= 1
  requires forall i :: 0 <= i < |heightMap| ==> |heightMap[i]| == n
  ensures water >= 0
  ensures (|heightMap| <= 2 || n <= 2) ==> water == 0
{
  var m := |heightMap|;
  ghost var AC := set a, b | 0 <= a < m && 0 <= b < n :: (a, b);
  water := 0;
  var visited: set<(int, int)> := {};
  var heap: PQ<(int, int)> := Empty;

  // Seed the queue with every boundary cell.
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant HeapOrdered(heap)
    invariant visited <= AC
    invariant forall e :: e in Items(heap) ==> e.1 in visited
    invariant forall a, b :: (0 <= a < i && 0 <= b < n &&
                               (a == 0 || a == m - 1 || b == 0 || b == n - 1)) ==> (a, b) in visited
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant HeapOrdered(heap)
      invariant visited <= AC
      invariant forall e :: e in Items(heap) ==> e.1 in visited
      invariant forall a, b :: (0 <= a < i && 0 <= b < n &&
                                 (a == 0 || a == m - 1 || b == 0 || b == n - 1)) ==> (a, b) in visited
      invariant forall b :: (0 <= b < j &&
                              (i == 0 || i == m - 1 || b == 0 || b == n - 1)) ==> (i, b) in visited
    {
      if (i == 0 || i == m - 1 || j == 0 || j == n - 1) && (i, j) !in visited {
        assert (i, j) in AC;
        visited := visited + {(i, j)};
        InsertCorrect(heightMap[i][j], (i, j), heap);
        heap := Insert(heightMap[i][j], (i, j), heap);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  if m <= 2 || n <= 2 {
    BoundaryOnlyAllVisited(m, n, AC, visited);
  }

  // Flood inward, always from the current lowest frontier level.
  while heap.Node?
    invariant water >= 0
    invariant HeapOrdered(heap)
    invariant visited <= AC
    invariant forall e :: e in Items(heap) ==> e.1 in visited
    invariant (m <= 2 || n <= 2) ==> visited == AC && water == 0
    decreases (|AC| - |visited|) + Size(heap)
  {
    var h := heap.key;
    var cell := heap.data;
    DeleteMinCorrect(heap);
    heap := DeleteMin(heap);
    var ci, cj := cell.0, cell.1;
    water, visited, heap := ProcessNeighbor(heightMap, m, n, AC, h, ci - 1, cj, water, visited, heap);
    water, visited, heap := ProcessNeighbor(heightMap, m, n, AC, h, ci + 1, cj, water, visited, heap);
    water, visited, heap := ProcessNeighbor(heightMap, m, n, AC, h, ci, cj - 1, water, visited, heap);
    water, visited, heap := ProcessNeighbor(heightMap, m, n, AC, h, ci, cj + 1, water, visited, heap);
    SubsetCard(visited, AC);
  }
}
// Public heap entry point with an honest bridge to the denotational spec.  For
// general grids this exposes the currently verified heap facts.  On grids with
// no interior cells, the heap result is proved to be the same exact zero-volume
// escape-level solution specified by TrappingRainWater.
method HeapFloodTrappingRainWater(heightMap: seq<seq<int>>) returns (water: int)
  requires Rect(heightMap)
  requires forall i, j :: InGrid(heightMap, i, j) ==> 0 <= heightMap[i][j] <= 20000
  ensures water >= 0
  ensures (|heightMap| <= 2 || |heightMap[0]| <= 2) ==>
            exists L :: IsWater(heightMap, L) &&
                        (forall L' :: IsWater(heightMap, L') ==>
                           forall i, j :: InGrid(heightMap, i, j) ==> L'[i][j] <= L[i][j]) &&
                        water == Vol(L, heightMap)
{
  water := HeapFloodNonnegative(heightMap, |heightMap[0]|);
  if |heightMap| <= 2 || |heightMap[0]| <= 2 {
    BoundaryOnlyHeightIsGreatestWater(heightMap);
    assert water == 0;
    assert IsWater(heightMap, heightMap);
    assert forall L' :: IsWater(heightMap, L') ==>
                         forall i, j :: InGrid(heightMap, i, j) ==> L'[i][j] <= heightMap[i][j];
    assert Vol(heightMap, heightMap) == 0;
    assert exists L :: IsWater(heightMap, L) &&
                       (forall L' :: IsWater(heightMap, L') ==>
                          forall i, j :: InGrid(heightMap, i, j) ==> L'[i][j] <= L[i][j]) &&
                       water == Vol(L, heightMap);
  }
}
