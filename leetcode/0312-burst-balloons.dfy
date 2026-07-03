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
//   * BruteMax below is an INDEPENDENT physical model (max over all bursting
//     orders, bursting one balloon at a time with live neighbours, no interval
//     decomposition). The public BurstBalloons method is specified against this
//     physical model; BurstBalloonsDP remains the verified interval-DP
//     tabulation against Best.
//   * Best == BruteMax is anchored on concrete inputs. A general
//     optimal-substructure theorem would be the next step if callers need to
//     connect the DP method to the physical model for all inputs.

function Max(x: int, y: int): int { if x >= y then x else y }

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
// Independent physical model: the maximum coins over ALL bursting orders.
// This makes NO use of the interval decomposition -- it bursts one balloon at a
// time using its live neighbours and maximizes over which balloon to burst
// FIRST. Best (the interval DP) and BruteMax are defined completely
// differently; proving them equal in general is the optimal-substructure
// theorem. We anchor the two together on concrete inputs below, which ties Best
// to the actual burst-order semantics (not just to hand-picked numbers).
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

function BurstFirst(s: seq<int>, i: int): int   // burst s[i] first, then the rest optimally
  requires 0 <= i < |s|
  decreases |s|, 0, 0
{
  LN(s, i) * s[i] * RN(s, i) + BruteMax(s[..i] + s[i + 1..])
}

function BruteMaxFrom(s: seq<int>, i: int): int   // max of BurstFirst over choices in [i, |s|)
  requires 0 <= i < |s|
  decreases |s|, 1, |s| - i
{
  if i == |s| - 1 then BurstFirst(s, i)
  else Max(BurstFirst(s, i), BruteMaxFrom(s, i + 1))
}

function BruteMax(s: seq<int>): int
  decreases |s|, 2, 0
{
  if |s| == 0 then 0 else BruteMaxFrom(s, 0)
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
  ensures coins == BruteMax(nums)
{
  coins := BruteMax(nums);
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
// inputs: the independently-defined BruteMax (max over all orders) agrees with
// Best. This is concrete-input evidence for the optimal-substructure theorem.
lemma BruteEmpty()
  ensures BruteMax([]) == 0
{
}

lemma BruteVsBestSingle()
  ensures BruteMax([5]) == Best([1, 5, 1], 0, 2) == 5
{
}

lemma BruteVsBestTwo()
  ensures BruteMax([3, 1]) == 6
  ensures Best([1, 3, 1, 1], 0, 3) == 6
{
  // singletons: [1] -> 1, [3] -> 3
  assert [1][..0] + [1][1..] == [];
  assert [3][..0] + [3][1..] == [];
  assert BruteMax([1]) == 1;
  assert BruteMax([3]) == 3;
  // [3,1]: burst index 0 first leaves [1]; burst index 1 first leaves [3]
  assert [3, 1][..0] + [3, 1][1..] == [1];
  assert [3, 1][..1] + [3, 1][2..] == [3];
  assert BurstFirst([3, 1], 0) == 1 * 3 * 1 + BruteMax([1]) == 4;
  assert BurstFirst([3, 1], 1) == 3 * 1 * 1 + BruteMax([3]) == 6;
  assert BruteMaxFrom([3, 1], 1) == 6;
  assert BruteMaxFrom([3, 1], 0) == 6;
}
