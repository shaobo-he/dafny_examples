// Author: Shaobo He
// LeetCode 42: Trapping Rain Water (1-D) -- EXACT correctness.
//
// The water standing over bar i is min(tallest-to-the-left, tallest-to-the-
// right) - height[i] (clamped at 0). This file proves the clever two-pointer
// algorithm returns EXACTLY that denotational total -- not merely >= 0.
//
//   WaterAt(h, i)   = max(0, min(PrefMax(h,i), SufMax(h,i)) - h[i])
//   TrappedTotal(h) = sum of WaterAt(h, i) over all i
//
// (The 2-D version, LeetCode 407, computes the analogous minimax level via a
// heap; proving THAT optimal is the bottleneck-shortest-path Dijkstra theorem
// and is out of scope -- see 0407-trapping-rain-water-ii.dfy.)

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

// Tallest bar at or to the left of i.
function PrefMax(h: seq<int>, i: int): int
  requires 0 <= i < |h|
  decreases i
{
  if i == 0 then h[0] else Max(PrefMax(h, i - 1), h[i])
}

// Tallest bar at or to the right of i.
function SufMax(h: seq<int>, i: int): int
  requires 0 <= i < |h|
  decreases |h| - i
{
  if i == |h| - 1 then h[i] else Max(h[i], SufMax(h, i + 1))
}

function WaterAt(h: seq<int>, i: int): int
  requires 0 <= i < |h|
{
  Max(0, Min(PrefMax(h, i), SufMax(h, i)) - h[i])
}

// Sum of WaterAt over [lo, hi).
function TrappedRange(h: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |h|
  decreases hi - lo
{
  if lo == hi then 0 else WaterAt(h, lo) + TrappedRange(h, lo + 1, hi)
}

function TrappedTotal(h: seq<int>): int
{
  TrappedRange(h, 0, |h|)
}

// max(0, h[0..k)) -- the running left maximum with a 0 floor.
function MaxUpTo(h: seq<int>, k: int): int
  requires 0 <= k <= |h|
  decreases k
{
  if k == 0 then 0 else Max(MaxUpTo(h, k - 1), h[k - 1])
}

// max(0, h[k..|h|)) -- the running right maximum with a 0 floor.
function MaxFrom(h: seq<int>, k: int): int
  requires 0 <= k <= |h|
  decreases |h| - k
{
  if k == |h| then 0 else Max(h[k], MaxFrom(h, k + 1))
}

// ---- Bridging lemmas: with non-negative heights the floored running maxima
// coincide with PrefMax / SufMax. --------------------------------------------

lemma PrefMaxEqMaxUpTo(h: seq<int>, i: int)
  requires 0 <= i < |h| && forall k :: 0 <= k < |h| ==> h[k] >= 0
  ensures PrefMax(h, i) == MaxUpTo(h, i + 1)
{
  if i > 0 {
    PrefMaxEqMaxUpTo(h, i - 1);
  }
}

lemma SufMaxEqMaxFrom(h: seq<int>, i: int)
  requires 0 <= i < |h| && forall k :: 0 <= k < |h| ==> h[k] >= 0
  ensures SufMax(h, i) == MaxFrom(h, i)
  decreases |h| - i
{
  if i < |h| - 1 {
    SufMaxEqMaxFrom(h, i + 1);
  }
}

lemma MaxUpToMono(h: seq<int>, a: int, b: int)
  requires 0 <= a <= b <= |h|
  ensures MaxUpTo(h, a) <= MaxUpTo(h, b)
  decreases b - a
{
  if a < b {
    MaxUpToMono(h, a, b - 1);
  }
}

lemma MaxFromMono(h: seq<int>, a: int, b: int)
  requires 0 <= a <= b <= |h|
  ensures MaxFrom(h, a) >= MaxFrom(h, b)
  decreases b - a
{
  if a < b {
    MaxFromMono(h, a + 1, b);
  }
}

// Appending one more index adds its WaterAt to the running sum.
lemma TrappedRangeExtend(h: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi < |h|
  ensures TrappedRange(h, lo, hi + 1) == TrappedRange(h, lo, hi) + WaterAt(h, hi)
  decreases hi - lo
{
  if lo < hi {
    TrappedRangeExtend(h, lo + 1, hi);
  }
}

lemma TrappedRangeSplit(h: seq<int>, lo: int, mid: int, hi: int)
  requires 0 <= lo <= mid <= hi <= |h|
  ensures TrappedRange(h, lo, hi) == TrappedRange(h, lo, mid) + TrappedRange(h, mid, hi)
  decreases mid - lo
{
  if lo < mid {
    TrappedRangeSplit(h, lo + 1, mid, hi);
  }
}

// ---- The algorithm: two pointers, always advancing the side with the smaller
// running maximum. Returns EXACTLY TrappedTotal(h). ---------------------------

method TrapWater(h: seq<int>) returns (water: int)
  requires |h| >= 1
  requires forall k :: 0 <= k < |h| ==> h[k] >= 0
  ensures water == TrappedTotal(h)
{
  var left, right := 0, |h| - 1;
  var leftMax, rightMax := 0, 0;
  water := 0;
  while left <= right
    invariant 0 <= left && right < |h| && left <= right + 1
    invariant leftMax == MaxUpTo(h, left)
    invariant rightMax == MaxFrom(h, right + 1)
    invariant water == TrappedRange(h, 0, left) + TrappedRange(h, right + 1, |h|)
    decreases right - left + 1
  {
    if leftMax <= rightMax {
      // The left cell's water level is fixed by the left maximum: because
      // some bar on the right is at least rightMax >= leftMax, SufMax(left)
      // dominates, so min(PrefMax, SufMax) at `left` equals PrefMax(left).
      PrefMaxEqMaxUpTo(h, left);
      SufMaxEqMaxFrom(h, left);
      MaxFromMono(h, left, right + 1);          // SufMax(left) >= rightMax
      leftMax := Max(leftMax, h[left]);
      assert leftMax == MaxUpTo(h, left + 1);
      assert leftMax == PrefMax(h, left);
      assert PrefMax(h, left) <= SufMax(h, left);
      assert leftMax - h[left] == WaterAt(h, left);
      TrappedRangeExtend(h, 0, left);
      water := water + leftMax - h[left];
      left := left + 1;
    } else {
      // Symmetric: the right cell's level is fixed by the right maximum.
      PrefMaxEqMaxUpTo(h, right);
      SufMaxEqMaxFrom(h, right);
      MaxUpToMono(h, left, right + 1);          // PrefMax(right) >= leftMax
      rightMax := Max(rightMax, h[right]);
      assert rightMax == MaxFrom(h, right);
      assert rightMax == SufMax(h, right);
      assert SufMax(h, right) <= PrefMax(h, right);
      assert rightMax - h[right] == WaterAt(h, right);
      water := water + rightMax - h[right];
      right := right - 1;
    }
  }
  TrappedRangeSplit(h, 0, left, |h|);
}

// Concrete checks that the denotational spec TrappedTotal matches known
// answers (so TrapWater, which returns TrappedTotal, is genuinely correct).
lemma {:fuel TrappedRange, 5} {:fuel PrefMax, 5} {:fuel SufMax, 5} {:fuel WaterAt, 5}
  ExampleBasin()
  ensures TrappedTotal([2, 0, 2]) == 2
{
}

lemma {:fuel TrappedRange, 8} {:fuel PrefMax, 8} {:fuel SufMax, 8} {:fuel WaterAt, 8}
  ExampleLeetCode()
  ensures TrappedTotal([4, 2, 0, 3, 2, 5]) == 9
{
}
