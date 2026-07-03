// Author: Shaobo He
// LeetCode 407: Trapping Rain Water II -- TRUE correctness (the hard part).
//
// The water level over a cell is the "minimax escape level": the lowest height
// at which water can still flow off the grid, i.e. the greatest configuration L
// with  L >= H,  L == H on the boundary (water drains off the edge), and for
// every interior cell and neighbour  L(c) <= max(H(c), L(d))  (water never sits
// higher than its lowest surrounding wall). The trapped volume is
// sum over cells of (L(c) - H(c)).
//
// This file develops that denotationally and proves the escape-level fixpoint
// IS that greatest configuration (equilibrium + maximality) -- so its volume is
// the true trapped water. (Groundwork; the imperative flood is 0407-...-ii.dfy.)

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

// A rectangular, non-empty grid.
predicate Rect(H: seq<seq<int>>) {
  |H| >= 1 && |H[0]| >= 1 && forall i :: 0 <= i < |H| ==> |H[i]| == |H[0]|
}

predicate InGrid(H: seq<seq<int>>, i: int, j: int)
  requires Rect(H)
{
  0 <= i < |H| && 0 <= j < |H[0]|
}

predicate Boundary(H: seq<seq<int>>, i: int, j: int)
  requires Rect(H)
{
  InGrid(H, i, j) && (i == 0 || i == |H| - 1 || j == 0 || j == |H[0]| - 1)
}

predicate Interior(H: seq<seq<int>>, i: int, j: int)
  requires Rect(H)
{
  InGrid(H, i, j) && !Boundary(H, i, j)
}

// The smallest neighbour level of an interior cell (all four neighbours exist).
function MinNbr(H: seq<seq<int>>, L: seq<seq<int>>, i: int, j: int): int
  requires Rect(H) && Rect(L) && |L| == |H| && |L[0]| == |H[0]|
  requires Interior(H, i, j)
{
  Min(Min(L[i - 1][j], L[i + 1][j]), Min(L[i][j - 1], L[i][j + 1]))
}

// L is a valid (non-overflowing) water configuration over H.
ghost predicate IsWater(H: seq<seq<int>>, L: seq<seq<int>>)
  requires Rect(H)
{
  Rect(L) && |L| == |H| && |L[0]| == |H[0]| &&
  (forall i, j :: InGrid(H, i, j) ==> L[i][j] >= H[i][j]) &&
  (forall i, j :: Boundary(H, i, j) ==> L[i][j] == H[i][j]) &&
  (forall i, j :: Interior(H, i, j) ==> L[i][j] <= Max(H[i][j], MinNbr(H, L, i, j)))
}

// ---- Escape level by k-bounded relaxation from an upper bound `hi` ----------
// EscCell(H, hi, k, i, j): the level of (i,j) after k relaxation rounds started
// from H on the boundary and `hi` in the interior. Non-increasing in k; its
// fixpoint is the true water level.

function EscCell(H: seq<seq<int>>, hi: int, k: nat, i: int, j: int): int
  requires Rect(H) && InGrid(H, i, j)
  decreases k
{
  if Boundary(H, i, j) then H[i][j]
  else if k == 0 then hi
  else Max(H[i][j],
           Min(Min(EscCell(H, hi, k - 1, i - 1, j), EscCell(H, hi, k - 1, i + 1, j)),
               Min(EscCell(H, hi, k - 1, i, j - 1), EscCell(H, hi, k - 1, i, j + 1))))
}

// The whole grid at round k, as a rectangular seq<seq<int>>.
function EscGrid(H: seq<seq<int>>, hi: int, k: nat): seq<seq<int>>
  requires Rect(H)
  ensures Rect(EscGrid(H, hi, k))
  ensures |EscGrid(H, hi, k)| == |H| && |EscGrid(H, hi, k)[0]| == |H[0]|
  ensures forall i, j :: InGrid(H, i, j) ==> EscGrid(H, hi, k)[i][j] == EscCell(H, hi, k, i, j)
{
  seq(|H|, i requires 0 <= i < |H| =>
    seq(|H[0]|, j requires 0 <= j < |H[0]| =>
      if InGrid(H, i, j) then EscCell(H, hi, k, i, j) else 0))
}

// Relaxation never raises a cell (monotone non-increasing in k), provided hi is
// an upper bound on all heights (so the interior starts no lower than H).
lemma EscMonotone(H: seq<seq<int>>, hi: int, k: nat, i: int, j: int)
  requires Rect(H) && InGrid(H, i, j)
  requires forall a, b :: InGrid(H, a, b) ==> H[a][b] <= hi
  ensures EscCell(H, hi, k + 1, i, j) <= EscCell(H, hi, k, i, j)
  decreases k
{
  if !Boundary(H, i, j) {
    if k == 0 {
      // EscCell(.,1,.) = Max(H, Min of round-0 neighbours) <= Max(hi, hi) = hi.
    } else {
      EscMonotone(H, hi, k - 1, i - 1, j);
      EscMonotone(H, hi, k - 1, i + 1, j);
      EscMonotone(H, hi, k - 1, i, j - 1);
      EscMonotone(H, hi, k - 1, i, j + 1);
    }
  }
}

// Every escape level is at least the cell's own height.
lemma EscGeH(H: seq<seq<int>>, hi: int, k: nat, i: int, j: int)
  requires Rect(H) && InGrid(H, i, j)
  requires forall a, b :: InGrid(H, a, b) ==> 0 <= H[a][b] <= hi
  ensures EscCell(H, hi, k, i, j) >= H[i][j]
{
}

// ---- Maximality: any valid water configuration is bounded by the escape
// level (so the escape-level fixpoint is the GREATEST valid water). ----------

// A valid water config never exceeds the height bound: walking straight up to
// row 0 (the boundary) bounds each cell by an already-bounded cell above it.
lemma ValidBoundedByRow(H: seq<seq<int>>, L: seq<seq<int>>, hi: int, i: int)
  requires Rect(H) && IsWater(H, L) && 0 <= i < |H|
  requires forall a, b :: InGrid(H, a, b) ==> H[a][b] <= hi
  ensures forall j :: 0 <= j < |H[0]| ==> L[i][j] <= hi
  decreases i
{
  if i > 0 {
    ValidBoundedByRow(H, L, hi, i - 1);   // once: row i-1 is bounded by hi
  }
  forall j | 0 <= j < |H[0]|
    ensures L[i][j] <= hi
  {
    if Interior(H, i, j) {
      assert MinNbr(H, L, i, j) <= L[i - 1][j];   // <= hi by the IH above
    }
  }
}

lemma ValidBounded(H: seq<seq<int>>, L: seq<seq<int>>, hi: int)
  requires Rect(H) && IsWater(H, L)
  requires forall a, b :: InGrid(H, a, b) ==> H[a][b] <= hi
  ensures forall i, j :: InGrid(H, i, j) ==> L[i][j] <= hi
{
  forall i, j | InGrid(H, i, j)
    ensures L[i][j] <= hi
  {
    ValidBoundedByRow(H, L, hi, i);
  }
}

lemma EscMaximal(H: seq<seq<int>>, L: seq<seq<int>>, hi: int, k: nat, i: int, j: int)
  requires Rect(H) && IsWater(H, L) && InGrid(H, i, j)
  requires forall a, b :: InGrid(H, a, b) ==> 0 <= H[a][b] <= hi
  ensures L[i][j] <= EscCell(H, hi, k, i, j)
  decreases k
{
  if Boundary(H, i, j) {
  } else if k == 0 {
    ValidBounded(H, L, hi);
  } else {
    EscMaximal(H, L, hi, k - 1, i - 1, j);
    EscMaximal(H, L, hi, k - 1, i + 1, j);
    EscMaximal(H, L, hi, k - 1, i, j - 1);
    EscMaximal(H, L, hi, k - 1, i, j + 1);
    // MinNbr(L) <= min of the neighbour escape levels, and
    // L[i][j] <= Max(H[i][j], MinNbr(L)) by validity.
    assert MinNbr(H, L, i, j) <=
           Min(Min(EscCell(H, hi, k - 1, i - 1, j), EscCell(H, hi, k - 1, i + 1, j)),
               Min(EscCell(H, hi, k - 1, i, j - 1), EscCell(H, hi, k - 1, i, j + 1)));
  }
}

// ---- Equilibrium: once relaxation stabilises, the escape grid is a valid
// water configuration. ------------------------------------------------------

lemma EquilibriumWhenStable(H: seq<seq<int>>, hi: int, K: nat)
  requires Rect(H)
  requires forall a, b :: InGrid(H, a, b) ==> 0 <= H[a][b] <= hi
  requires forall i, j :: InGrid(H, i, j) ==>
                            EscCell(H, hi, K + 1, i, j) == EscCell(H, hi, K, i, j)
  ensures IsWater(H, EscGrid(H, hi, K))
{
  var L := EscGrid(H, hi, K);
  forall i, j | InGrid(H, i, j)
    ensures L[i][j] >= H[i][j]
  {
    EscGeH(H, hi, K, i, j);
  }
  forall i, j | Interior(H, i, j)
    ensures L[i][j] <= Max(H[i][j], MinNbr(H, L, i, j))
  {
    // EscCell(K+1,i,j) = Max(H[i][j], MinNbr(L)); stability gives EscCell(K)=that.
    assert L[i][j] == EscCell(H, hi, K, i, j) == EscCell(H, hi, K + 1, i, j);
    assert MinNbr(H, L, i, j) ==
           Min(Min(EscCell(H, hi, K, i - 1, j), EscCell(H, hi, K, i + 1, j)),
               Min(EscCell(H, hi, K, i, j - 1), EscCell(H, hi, K, i, j + 1)));
  }
}

// THE THEOREM: once relaxation stabilises, the escape grid is a valid water
// configuration AND it dominates every valid water configuration -- i.e. it is
// the unique greatest standing water, so its per-cell overflow is exactly the
// true trapped water.
lemma EscIsGreatestWater(H: seq<seq<int>>, hi: int, K: nat)
  requires Rect(H)
  requires forall a, b :: InGrid(H, a, b) ==> 0 <= H[a][b] <= hi
  requires forall i, j :: InGrid(H, i, j) ==>
                            EscCell(H, hi, K + 1, i, j) == EscCell(H, hi, K, i, j)
  ensures IsWater(H, EscGrid(H, hi, K))
  ensures forall L' :: IsWater(H, L') ==>
                         forall i, j :: InGrid(H, i, j) ==> L'[i][j] <= EscGrid(H, hi, K)[i][j]
{
  EquilibriumWhenStable(H, hi, K);
  forall L' | IsWater(H, L')
    ensures forall i, j :: InGrid(H, i, j) ==> L'[i][j] <= EscGrid(H, hi, K)[i][j]
  {
    forall i, j | InGrid(H, i, j)
      ensures L'[i][j] <= EscGrid(H, hi, K)[i][j]
    {
      EscMaximal(H, L', hi, K, i, j);
    }
  }
}

// ---- Volume, and a relaxation algorithm that computes the fixpoint. ---------

function RowSum(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
{
  if |a| == 0 then 0 else (a[0] - b[0]) + RowSum(a[1..], b[1..])
}

// Total standing water = sum over all cells of (L - H), summing rows [i, |L|).
function GridSum(L: seq<seq<int>>, H: seq<seq<int>>, i: nat): int
  requires |L| == |H| && i <= |L|
  requires forall r :: 0 <= r < |L| ==> |L[r]| == |H[r]|
  decreases |L| - i
{
  if i == |L| then 0 else RowSum(L[i], H[i]) + GridSum(L, H, i + 1)
}

function Vol(L: seq<seq<int>>, H: seq<seq<int>>): int
  requires |L| == |H| && forall r :: 0 <= r < |L| ==> |L[r]| == |H[r]|
{
  GridSum(L, H, 0)
}

lemma RowSumLe(a: seq<int>, a2: seq<int>, b: seq<int>)
  requires |a| == |a2| == |b|
  requires forall k :: 0 <= k < |a| ==> a2[k] <= a[k]
  ensures RowSum(a2, b) <= RowSum(a, b)
{
  if |a| > 0 {
    RowSumLe(a[1..], a2[1..], b[1..]);
  }
}

lemma RowSumStrict(a: seq<int>, a2: seq<int>, b: seq<int>, j0: int)
  requires |a| == |a2| == |b| && 0 <= j0 < |a|
  requires forall k :: 0 <= k < |a| ==> a2[k] <= a[k]
  requires a2[j0] < a[j0]
  ensures RowSum(a2, b) < RowSum(a, b)
{
  if j0 == 0 {
    RowSumLe(a[1..], a2[1..], b[1..]);
  } else {
    RowSumStrict(a[1..], a2[1..], b[1..], j0 - 1);
  }
}

// If G2 is pointwise <= G and strictly smaller at one cell, its volume is
// strictly smaller -- the relaxation's termination measure.
lemma VolStrictDecrease(G: seq<seq<int>>, G2: seq<seq<int>>, H: seq<seq<int>>, i0: int, j0: int)
  requires |G| == |G2| == |H|
  requires forall r :: 0 <= r < |G| ==> |G[r]| == |G2[r]| == |H[r]|
  requires forall i, j :: 0 <= i < |G| && 0 <= j < |G[i]| ==> G2[i][j] <= G[i][j]
  requires 0 <= i0 < |G| && 0 <= j0 < |G[i0]| && G2[i0][j0] < G[i0][j0]
  ensures Vol(G2, H) < Vol(G, H)
{
  GridSumStrict(G, G2, H, 0, i0, j0);
}

lemma GridSumStrict(G: seq<seq<int>>, G2: seq<seq<int>>, H: seq<seq<int>>, i: nat, i0: int, j0: int)
  requires |G| == |G2| == |H| && i <= |G|
  requires forall r :: 0 <= r < |G| ==> |G[r]| == |G2[r]| == |H[r]|
  requires forall a, b :: 0 <= a < |G| && 0 <= b < |G[a]| ==> G2[a][b] <= G[a][b]
  requires i <= i0 < |G| && 0 <= j0 < |G[i0]| && G2[i0][j0] < G[i0][j0]
  ensures GridSum(G2, H, i) < GridSum(G, H, i)
  decreases |G| - i
{
  if i == i0 {
    RowSumStrict(G[i], G2[i], H[i], j0);
    GridSumLe(G, G2, H, i + 1);
  } else {
    RowSumLe(G[i], G2[i], H[i]);
    GridSumStrict(G, G2, H, i + 1, i0, j0);
  }
}

lemma GridSumLe(G: seq<seq<int>>, G2: seq<seq<int>>, H: seq<seq<int>>, i: nat)
  requires |G| == |G2| == |H| && i <= |G|
  requires forall r :: 0 <= r < |G| ==> |G[r]| == |G2[r]| == |H[r]|
  requires forall a, b :: 0 <= a < |G| && 0 <= b < |G[a]| ==> G2[a][b] <= G[a][b]
  ensures GridSum(G2, H, i) <= GridSum(G, H, i)
  decreases |G| - i
{
  if i < |G| {
    RowSumLe(G[i], G2[i], H[i]);
    GridSumLe(G, G2, H, i + 1);
  }
}

lemma RowSumNonneg(a: seq<int>, b: seq<int>)
  requires |a| == |b| && forall k :: 0 <= k < |a| ==> a[k] >= b[k]
  ensures RowSum(a, b) >= 0
{
  if |a| > 0 {
    RowSumNonneg(a[1..], b[1..]);
  }
}

lemma GridSumNonneg(L: seq<seq<int>>, H: seq<seq<int>>, i: nat)
  requires |L| == |H| && i <= |L|
  requires forall r :: 0 <= r < |L| ==> |L[r]| == |H[r]|
  requires forall a, b :: 0 <= a < |L| && 0 <= b < |L[a]| ==> L[a][b] >= H[a][b]
  ensures GridSum(L, H, i) >= 0
  decreases |L| - i
{
  if i < |L| {
    RowSumNonneg(L[i], H[i]);
    GridSumNonneg(L, H, i + 1);
  }
}

lemma VolNonneg(H: seq<seq<int>>, hi: int, k: nat)
  requires Rect(H)
  requires forall a, b :: InGrid(H, a, b) ==> 0 <= H[a][b] <= hi
  ensures Vol(EscGrid(H, hi, k), H) >= 0
{
  var G := EscGrid(H, hi, k);
  forall a, b | 0 <= a < |G| && 0 <= b < |G[a]|
    ensures G[a][b] >= H[a][b]
  {
    EscGeH(H, hi, k, a, b);
  }
  GridSumNonneg(G, H, 0);
}

// Boundary-only grids have no interior basin. The height map itself is the
// greatest valid water configuration, and its trapped volume is zero.
lemma BoundaryOnlyEveryCellBoundary(H: seq<seq<int>>)
  requires Rect(H)
  requires |H| <= 2 || |H[0]| <= 2
  ensures forall i, j :: InGrid(H, i, j) ==> Boundary(H, i, j)
{
}

lemma BoundaryOnlyWaterEqualsHeight(H: seq<seq<int>>, L: seq<seq<int>>)
  requires Rect(H) && IsWater(H, L)
  requires |H| <= 2 || |H[0]| <= 2
  ensures forall i, j :: InGrid(H, i, j) ==> L[i][j] == H[i][j]
{
  BoundaryOnlyEveryCellBoundary(H);
}

lemma RowSumPointwiseSame(a: seq<int>, b: seq<int>)
  requires |a| == |b|
  requires forall k :: 0 <= k < |a| ==> a[k] == b[k]
  ensures RowSum(a, b) == 0
{
  if |a| > 0 {
    assert a[0] - b[0] == 0;
    assert forall k :: 0 <= k < |a[1..]| ==> a[1..][k] == b[1..][k];
    RowSumPointwiseSame(a[1..], b[1..]);
  }
}

lemma GridSumPointwiseSame(L: seq<seq<int>>, H: seq<seq<int>>, i: nat)
  requires |L| == |H| && i <= |L|
  requires forall r :: 0 <= r < |L| ==> |L[r]| == |H[r]|
  requires forall a, b :: 0 <= a < |L| && 0 <= b < |L[a]| ==> L[a][b] == H[a][b]
  ensures GridSum(L, H, i) == 0
  decreases |L| - i
{
  if i < |L| {
    RowSumPointwiseSame(L[i], H[i]);
    GridSumPointwiseSame(L, H, i + 1);
  }
}

lemma BoundaryOnlyHeightIsGreatestWater(H: seq<seq<int>>)
  requires Rect(H)
  requires |H| <= 2 || |H[0]| <= 2
  ensures IsWater(H, H)
  ensures forall L' :: IsWater(H, L') ==>
                         forall i, j :: InGrid(H, i, j) ==> L'[i][j] <= H[i][j]
  ensures Vol(H, H) == 0
{
  BoundaryOnlyEveryCellBoundary(H);
  GridSumPointwiseSame(H, H, 0);
  forall L' | IsWater(H, L')
    ensures forall i, j :: InGrid(H, i, j) ==> L'[i][j] <= H[i][j]
  {
    BoundaryOnlyWaterEqualsHeight(H, L');
  }
}
// One relaxation round strictly lowers the total volume (termination measure).
lemma StepDecreasesVol(H: seq<seq<int>>, hi: int, k: nat, wi: int, wj: int)
  requires Rect(H)
  requires forall a, b :: InGrid(H, a, b) ==> 0 <= H[a][b] <= hi
  requires InGrid(H, wi, wj) && EscCell(H, hi, k + 1, wi, wj) < EscCell(H, hi, k, wi, wj)
  ensures Vol(EscGrid(H, hi, k + 1), H) < Vol(EscGrid(H, hi, k), H)
{
  var G := EscGrid(H, hi, k);
  var G2 := EscGrid(H, hi, k + 1);
  forall a, b | 0 <= a < |G| && 0 <= b < |G[a]|
    ensures G2[a][b] <= G[a][b]
  {
    EscMonotone(H, hi, k, a, b);
  }
  VolStrictDecrease(G, G2, H, wi, wj);
}

// Is round k already the fixpoint? If not, hand back a cell that still drops.
method IsStable(H: seq<seq<int>>, hi: int, k: nat)
  returns (stable: bool, ghost wi: int, ghost wj: int)
  requires Rect(H)
  requires forall a, b :: InGrid(H, a, b) ==> 0 <= H[a][b] <= hi
  ensures stable ==> forall i, j :: InGrid(H, i, j) ==>
                                      EscCell(H, hi, k + 1, i, j) == EscCell(H, hi, k, i, j)
  ensures !stable ==> InGrid(H, wi, wj) &&
                      EscCell(H, hi, k + 1, wi, wj) < EscCell(H, hi, k, wi, wj)
{
  var i := 0;
  stable := true;
  wi, wj := 0, 0;
  while i < |H|
    invariant 0 <= i <= |H|
    invariant stable ==> forall a, b :: 0 <= a < i && 0 <= b < |H[0]| ==>
                                          EscCell(H, hi, k + 1, a, b) == EscCell(H, hi, k, a, b)
    invariant !stable ==> InGrid(H, wi, wj) &&
                          EscCell(H, hi, k + 1, wi, wj) < EscCell(H, hi, k, wi, wj)
  {
    var j := 0;
    while j < |H[0]|
      invariant 0 <= j <= |H[0]|
      invariant stable ==> (forall a, b :: 0 <= a < i && 0 <= b < |H[0]| ==>
                                             EscCell(H, hi, k + 1, a, b) == EscCell(H, hi, k, a, b))
                           && (forall b :: 0 <= b < j ==>
                                             EscCell(H, hi, k + 1, i, b) == EscCell(H, hi, k, i, b))
      invariant !stable ==> InGrid(H, wi, wj) &&
                            EscCell(H, hi, k + 1, wi, wj) < EscCell(H, hi, k, wi, wj)
    {
      EscMonotone(H, hi, k, i, j);
      if EscCell(H, hi, k + 1, i, j) != EscCell(H, hi, k, i, j) {
        stable := false;
        wi, wj := i, j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method ComputeTrappedWater(H: seq<seq<int>>, hi: int) returns (vol: int, ghost L: seq<seq<int>>)
  requires Rect(H)
  requires forall a, b :: InGrid(H, a, b) ==> 0 <= H[a][b] <= hi
  ensures IsWater(H, L)                                  // the result is a valid water config
  ensures forall L' :: IsWater(H, L') ==>               // and it is the greatest such
                         forall i, j :: InGrid(H, i, j) ==> L'[i][j] <= L[i][j]
  ensures vol == Vol(L, H)                              // the returned volume is its overflow total
{
  var k := 0;
  VolNonneg(H, hi, k);
  var stable, wi, wj := IsStable(H, hi, k);
  while !stable
    invariant stable ==> forall i, j :: InGrid(H, i, j) ==>
                                          EscCell(H, hi, k + 1, i, j) == EscCell(H, hi, k, i, j)
    invariant !stable ==> InGrid(H, wi, wj) &&
                          EscCell(H, hi, k + 1, wi, wj) < EscCell(H, hi, k, wi, wj)
    invariant Vol(EscGrid(H, hi, k), H) >= 0
    decreases Vol(EscGrid(H, hi, k), H)
  {
    StepDecreasesVol(H, hi, k, wi, wj);
    k := k + 1;
    VolNonneg(H, hi, k);
    stable, wi, wj := IsStable(H, hi, k);
  }
  EscIsGreatestWater(H, hi, k);
  L := EscGrid(H, hi, k);
  vol := Vol(EscGrid(H, hi, k), H);
}

// Public exact solution backed by the denotational escape-level proof above.
method TrappingRainWaterByEscapeLevels(heightMap: seq<seq<int>>) returns (water: int)
  requires Rect(heightMap)
  requires forall i, j :: InGrid(heightMap, i, j) ==> 0 <= heightMap[i][j] <= 20000
  ensures exists L :: IsWater(heightMap, L) &&
                      (forall L' :: IsWater(heightMap, L') ==>
                         forall i, j :: InGrid(heightMap, i, j) ==> L'[i][j] <= L[i][j]) &&
                      water == Vol(L, heightMap)
{
  ghost var L: seq<seq<int>>;
  water, L := ComputeTrappedWater(heightMap, 20000);
}


method TrappingRainWater(heightMap: seq<seq<int>>) returns (water: int)
  requires Rect(heightMap)
  requires forall i, j :: InGrid(heightMap, i, j) ==> 0 <= heightMap[i][j] <= 20000
  ensures exists L :: IsWater(heightMap, L) &&
                      (forall L' :: IsWater(heightMap, L') ==>
                         forall i, j :: InGrid(heightMap, i, j) ==> L'[i][j] <= L[i][j]) &&
                      water == Vol(L, heightMap)
{
  water := TrappingRainWaterByEscapeLevels(heightMap);
}

// A concrete anchor: a 3x3 bowl of height-5 walls around a height-1 pit holds
// exactly 5-1 = 4 units. Relaxation stabilises after one round.
lemma {:fuel EscCell, 4} {:fuel EscGrid, 2} {:fuel GridSum, 4} {:fuel RowSum, 4}
ExampleBowl()
  ensures var H := [[5, 5, 5], [5, 1, 5], [5, 5, 5]];
          Rect(H) &&
          (forall i, j :: InGrid(H, i, j) ==>
                            EscCell(H, 5, 2, i, j) == EscCell(H, 5, 1, i, j)) &&
          Vol(EscGrid(H, 5, 1), H) == 4
{
}
