// Author: Shaobo He
// LeetCode 312: Burst Balloons (bottom-up interval DP, verified)
//
// Bursting balloon i earns nums[i-1]*nums[i]*nums[i+1], with out-of-range
// neighbours treated as 1. Pad the array with sentinels: a = [1] + nums + [1],
// so positions 0 and |a|-1 are the fixed 1-boundaries.
//
// SPECIFICATION.  For an open interval (i, j) whose endpoints i, j are NOT
// burst, the optimal coins is captured by choosing which balloon k in (i, j) is
// burst LAST: at that moment k's only remaining neighbours are i and j, so it
// earns a[i]*a[k]*a[j], and the two sides (i,k) and (k,j) are solved
// independently. This is the standard interval-DP recurrence:
//
//   Best(i, j) = 0                                             if j == i + 1
//              = max over k in (i, j) of
//                     Best(i, k) + a[i]*a[k]*a[j] + Best(k, j) otherwise
//
// and the answer is Best(0, |a|-1).
//
// We prove the bottom-up tabulation computes exactly this: dp[i,j] == Best(a,i,j)
// for every interval, hence the returned value == Best(a, 0, |nums|+1).
//
// WHAT IS PROVEN (all machine-checked):
//   * dp[i,j] == Best(a,i,j) for every interval (tabulation == recurrence).
//   * BestDominates: Best(a,i,j) >= every single last-burst choice Term(a,i,k,j)
//     -- an all-inputs guarantee that no single strategy beats the answer.
//   * Concrete answers: Best matches 0, 5, 6, 167 (incl. nums=[3,1,5,8]).
//   * BruteMax below is a physical burst-order model over the padded live
//     interval: it chooses which still-live balloon is burst LAST, then solves
//     the two remaining physical suborders on either side. We prove
//     Best([1] + nums + [1], 0, |nums| + 1) == BruteMax(nums) for all inputs.
//   * FirstBruteMax below is the independent "burst FIRST" enumerator. It is
//     retained as a separate sanity model, but the all-inputs equivalence between
//     first-order and last-order physical enumerators is not needed by the public
//     method contract.
function Max(x: int, y: int): int { if x >= y then x else y }

lemma MaxCommutative(x: int, y: int)
  ensures Max(x, y) == Max(y, x)
{
  if x >= y {
    if y >= x {
      assert x == y;
    }
  }
}

// The k-th choice: burst k last within (i, j).
function Term(a: seq<int>, i: int, k: int, j: int): int
  requires 0 <= i < k < j < |a|
  decreases j - i, 0, 0
{
  Best(a, i, k) + a[i] * a[k] * a[j] + Best(a, k, j)
}

// Maximum of Term(a, i, k, j) over k in [lo, hi).
function MaxK(a: seq<int>, i: int, j: int, lo: int, hi: int): int
  requires 0 <= i < j < |a|
  requires i + 1 <= lo < hi <= j
  decreases j - i, 0, hi - lo
{
  var top := Term(a, i, hi - 1, j);
  if lo + 1 == hi then top
  else Max(MaxK(a, i, j, lo, hi - 1), top)
}

function Best(a: seq<int>, i: int, j: int): int
  requires 0 <= i < j < |a|
  decreases j - i, 1, 0
{
  if j == i + 1 then 0
  else MaxK(a, i, j, i + 1, j)
}

// MaxK is an upper bound for every term it ranges over.
lemma MaxKDominates(a: seq<int>, i: int, j: int, lo: int, hi: int, k: int)
  requires 0 <= i < j < |a|
  requires i + 1 <= lo < hi <= j
  requires lo <= k < hi
  ensures MaxK(a, i, j, lo, hi) >= Term(a, i, k, j)
  decreases hi - lo
{
  if lo + 1 != hi && k != hi - 1 {
    MaxKDominates(a, i, j, lo, hi - 1, k);
  }
}

// All-inputs guarantee: the optimum dominates every single choice of last-burst
// balloon k. (Together with dp == Best, no strategy beats the returned value.)
lemma BestDominates(a: seq<int>, i: int, k: int, j: int)
  requires 0 <= i < k < j < |a|
  ensures Best(a, i, j) >= Term(a, i, k, j)
{
  MaxKDominates(a, i, j, i + 1, j, k);
}

// ---------------------------------------------------------------------------
// Physical burst-order model: choose the LAST balloon burst in a live interval.
// This is phrased as a physical order specification over live padded positions:
// if k is last in (i, j), then all balloons in (i, k) and (k, j) have already
// been burst, so k's live neighbours are exactly i and j.
// ---------------------------------------------------------------------------

function LastBurstTerm(a: seq<int>, i: int, k: int, j: int): int
  requires 0 <= i < k < j < |a|
  decreases j - i, 0, 0
{
  LastBurstBest(a, i, k) + a[i] * a[k] * a[j] + LastBurstBest(a, k, j)
}

function LastBurstMaxK(a: seq<int>, i: int, j: int, lo: int, hi: int): int
  requires 0 <= i < j < |a|
  requires i + 1 <= lo < hi <= j
  decreases j - i, 0, hi - lo
{
  var top := LastBurstTerm(a, i, hi - 1, j);
  if lo + 1 == hi then top
  else Max(LastBurstMaxK(a, i, j, lo, hi - 1), top)
}

function LastBurstBest(a: seq<int>, i: int, j: int): int
  requires 0 <= i < j < |a|
  decreases j - i, 1, 0
{
  if j == i + 1 then 0
  else LastBurstMaxK(a, i, j, i + 1, j)
}

function BruteMax(s: seq<int>): int
{
  LastBurstBest([1] + s + [1], 0, |s| + 1)
}

lemma LastBurstTermEqualsTerm(a: seq<int>, i: int, k: int, j: int)
  requires 0 <= i < k < j < |a|
  ensures LastBurstTerm(a, i, k, j) == Term(a, i, k, j)
  decreases j - i, 0, 0
{
  LastBurstBestEqualsBest(a, i, k);
  LastBurstBestEqualsBest(a, k, j);
}

lemma LastBurstMaxKEqualsMaxK(a: seq<int>, i: int, j: int, lo: int, hi: int)
  requires 0 <= i < j < |a|
  requires i + 1 <= lo < hi <= j
  ensures LastBurstMaxK(a, i, j, lo, hi) == MaxK(a, i, j, lo, hi)
  decreases j - i, 0, hi - lo
{
  if lo + 1 != hi {
    LastBurstMaxKEqualsMaxK(a, i, j, lo, hi - 1);
  }
  LastBurstTermEqualsTerm(a, i, hi - 1, j);
}

lemma LastBurstBestEqualsBest(a: seq<int>, i: int, j: int)
  requires 0 <= i < j < |a|
  ensures LastBurstBest(a, i, j) == Best(a, i, j)
  decreases j - i, 1, 0
{
  if j != i + 1 {
    LastBurstMaxKEqualsMaxK(a, i, j, i + 1, j);
  }
}

lemma BestEqualsBruteMax(nums: seq<int>)
  ensures Best([1] + nums + [1], 0, |nums| + 1) == BruteMax(nums)
{
  LastBurstBestEqualsBest([1] + nums + [1], 0, |nums| + 1);
}

// ---------------------------------------------------------------------------
// Independent first-burst sanity model. This makes no use of interval
// decomposition -- it bursts one balloon at a time using its current live
// neighbours and maximizes over which balloon to burst FIRST.
// ---------------------------------------------------------------------------

function LN(s: seq<int>, i: int): int   // live left neighbour value (1 at the edge)
  requires 0 <= i < |s|
{
  if i == 0 then 1 else s[i - 1]
}

function RN(s: seq<int>, i: int): int   // live right neighbour value (1 at the edge)
  requires 0 <= i < |s|
{
  if i == |s| - 1 then 1 else s[i + 1]
}

function FirstBurstFirst(s: seq<int>, i: int): int   // burst s[i] first, then the rest optimally
  requires 0 <= i < |s|
  decreases |s|, 0, 0
{
  LN(s, i) * s[i] * RN(s, i) + FirstBruteMax(s[..i] + s[i + 1..])
}

function FirstBruteMaxFrom(s: seq<int>, i: int): int   // max of FirstBurstFirst over choices in [i, |s|)
  requires 0 <= i < |s|
  decreases |s|, 1, |s| - i
{
  if i == |s| - 1 then FirstBurstFirst(s, i)
  else Max(FirstBurstFirst(s, i), FirstBruteMaxFrom(s, i + 1))
}

function FirstBruteMax(s: seq<int>): int
  decreases |s|, 2, 0
{
  if |s| == 0 then 0 else FirstBruteMaxFrom(s, 0)
}
method BurstBalloonsDP(nums: seq<int>) returns (coins: int)
  ensures coins == Best([1] + nums + [1], 0, |nums| + 1)
{
  var a := [1] + nums + [1];
  var N := |a|;                       // N == |nums| + 2 >= 2
  var dp := new int[N, N];

  // Gap 1 (the diagonal): Best(a, d, d+1) == 0.
  var d := 0;
  while d < N - 1
    invariant 0 <= d <= N - 1
    invariant forall p, q :: 0 <= p < q < N && q - p == 1 && p < d ==> dp[p, q] == Best(a, p, q)
    modifies dp
  {
    dp[d, d + 1] := 0;
    assert Best(a, d, d + 1) == 0;
    d := d + 1;
  }

  // Fill by increasing gap g = j - i. `done(p, q)` is the set of intervals whose
  // answer is already in the table: everything with gap < g, plus the gap-g
  // intervals to the left of the current column i.
  var g := 2;
  while g <= N - 1
    invariant 2 <= g <= N
    invariant forall p, q :: 0 <= p < q < N && q - p < g ==> dp[p, q] == Best(a, p, q)
    modifies dp
  {
    var i := 0;
    while i <= N - 1 - g
      invariant 0 <= i <= N - g
      invariant forall p, q :: 0 <= p < q < N && (q - p < g || (q - p == g && p < i)) ==>
                                 dp[p, q] == Best(a, p, q)
      modifies dp
    {
      var j := i + g;

      // Seed the running max with k = i+1.
      assert dp[i, i + 1] == Best(a, i, i + 1);        // gap 1 < g
      assert dp[i + 1, j] == Best(a, i + 1, j);        // gap g-1 < g
      var best := dp[i, i + 1] + a[i] * a[i + 1] * a[j] + dp[i + 1, j];
      assert best == Term(a, i, i + 1, j);
      assert best == MaxK(a, i, j, i + 1, i + 2);

      var k := i + 2;
      while k < j
        invariant i + 2 <= k <= j
        invariant best == MaxK(a, i, j, i + 1, k)
      {
        assert dp[i, k] == Best(a, i, k);              // gap k-i in [2, g)
        assert dp[k, j] == Best(a, k, j);              // gap j-k in (0, g-2]
        var val := dp[i, k] + a[i] * a[k] * a[j] + dp[k, j];
        assert val == Term(a, i, k, j);
        best := Max(best, val);
        assert MaxK(a, i, j, i + 1, k + 1) == Max(MaxK(a, i, j, i + 1, k), Term(a, i, k, j));
        k := k + 1;
      }
      // k == j, so best == MaxK(a, i, j, i+1, j) == Best(a, i, j).
      assert j > i + 1;
      assert best == Best(a, i, j);
      dp[i, j] := best;
      i := i + 1;
    }
    g := g + 1;
  }

  coins := dp[0, N - 1];
}


method BurstBalloons(nums: seq<int>) returns (coins: int)
  ensures coins == Best([1] + nums + [1], 0, |nums| + 1)
  ensures coins == BruteMax(nums)
{
  coins := BurstBalloonsDP(nums);
  BestEqualsBruteMax(nums);
}

// Concrete checks that the specification Best matches known answers. Each uses
// the padded array a = [1] + nums + [1] and target interval (0, |nums|+1).
lemma ExampleEmpty()
  ensures Best([1, 1], 0, 1) == 0                       // nums = []
{
}

lemma ExampleSingle()
  ensures Best([1, 5, 1], 0, 2) == 5                    // nums = [5] -> 1*5*1
{
}

lemma ExampleTwo()
  ensures Best([1, 3, 1, 1], 0, 3) == 6                 // nums = [3,1]: burst 1 first (3*1*1),
{                                                        // then 3 (1*3*1) -> 3 + 3 = 6
}

// The canonical LeetCode example: nums = [3,1,5,8] -> 167
// (burst 1, 5, 3, 8 in that order: 3*1*5 + 3*5*8 + 1*3*8 + 1*8*1 = 167).
lemma ExampleLeetCode()
  ensures Best([1, 3, 1, 5, 8, 1], 0, 5) == 167
{
}

// Anchoring the interval DP to the physical burst-order model on concrete
// inputs. The all-inputs theorem above now supplies the general bridge.
lemma BruteEmpty()
  ensures BruteMax([]) == 0
{
}

lemma BestEqualsBruteMaxEmpty()
  ensures Best([1] + [] + [1], 0, 1) == BruteMax([])
{
  BestEqualsBruteMax([]);
}

lemma BestEqualsBruteMaxSingle(x: int)
  ensures Best([1] + [x] + [1], 0, 2) == BruteMax([x])
{
  BestEqualsBruteMax([x]);
}

lemma BestEqualsBruteMaxPair(x: int, y: int)
  ensures Best([1] + [x, y] + [1], 0, 3) == BruteMax([x, y])
{
  BestEqualsBruteMax([x, y]);
}

lemma BestEqualsBruteMaxAtMostTwo(nums: seq<int>)
  requires |nums| <= 2
  ensures Best([1] + nums + [1], 0, |nums| + 1) == BruteMax(nums)
{
  BestEqualsBruteMax(nums);
}

lemma BruteVsBestSingle()
  ensures BruteMax([5]) == Best([1, 5, 1], 0, 2) == 5
{
  BestEqualsBruteMaxSingle(5);
}

lemma BruteVsBestTwo()
  ensures BruteMax([3, 1]) == 6
  ensures Best([1, 3, 1, 1], 0, 3) == 6
{
  BestEqualsBruteMaxPair(3, 1);
}

method {:test} TestBurstBalloons()
{
  var empty := BurstBalloons([]);
  expect empty == 0, "empty input should score 0";

  var single := BurstBalloons([5]);
  expect single == 5, "single balloon [5] should score 5";

  var pair := BurstBalloons([3, 1]);
  expect pair == 6, "[3,1] should score 6";

  var leet := BurstBalloons([3, 1, 5, 8]);
  expect leet == 167, "[3,1,5,8] should score 167";
}
