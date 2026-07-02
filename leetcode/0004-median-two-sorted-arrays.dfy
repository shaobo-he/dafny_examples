// Author: Shaobo He
// LeetCode 4: Median of Two Sorted Arrays -- TRUE correctness.
//
// The median is defined denotationally, on the sorted merge of the two inputs.
// The hard part (this is a "Hard" problem because of it) is the O(log(m+n))
// "k-th smallest" recursion that avoids building the merge. We prove that
// recursion returns exactly Merge(a, b)[k-1], hence the median formula is exact.

function Min(a: int, b: int): int { if a <= b then a else b }
function Max(a: int, b: int): int { if a >= b then a else b }

predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}

// Sorted merge of two sorted sequences.
function Merge(a: seq<int>, b: seq<int>): seq<int>
  decreases |a| + |b|
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else if a[0] <= b[0] then [a[0]] + Merge(a[1..], b)
  else [b[0]] + Merge(a, b[1..])
}

lemma MergeLen(a: seq<int>, b: seq<int>)
  ensures |Merge(a, b)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| > 0 && |b| > 0 {
    if a[0] <= b[0] { MergeLen(a[1..], b); } else { MergeLen(a, b[1..]); }
  }
}

lemma MergeMultiset(a: seq<int>, b: seq<int>)
  ensures multiset(Merge(a, b)) == multiset(a) + multiset(b)
  decreases |a| + |b|
{
  if |a| > 0 && |b| > 0 {
    if a[0] <= b[0] {
      MergeMultiset(a[1..], b);
      assert a == [a[0]] + a[1..];
    } else {
      MergeMultiset(a, b[1..]);
      assert b == [b[0]] + b[1..];
    }
  }
}

lemma SortedTail(s: seq<int>)
  requires Sorted(s) && |s| > 0
  ensures Sorted(s[1..])
{
}

lemma SortedHeadMin(s: seq<int>)
  requires Sorted(s) && |s| > 0
  ensures forall x :: x in s ==> s[0] <= x
{
}

lemma SortedPrepend(v: int, s: seq<int>)
  requires Sorted(s)
  requires forall x :: x in s ==> v <= x
  ensures Sorted([v] + s)
{
  var t := [v] + s;
  forall i, j | 0 <= i <= j < |t|
    ensures t[i] <= t[j]
  {
    if i == 0 {
      if j > 0 { assert t[j] == s[j - 1] && s[j - 1] in s; }
    } else {
      assert t[i] == s[i - 1] && t[j] == s[j - 1];
    }
  }
}

// A lower bound v of both runs lower-bounds their merge.
lemma MergeHeadLe(a: seq<int>, b: seq<int>, v: int)
  requires forall x :: x in a ==> v <= x
  requires forall x :: x in b ==> v <= x
  ensures forall x :: x in Merge(a, b) ==> v <= x
  decreases |a| + |b|
{
  if |a| > 0 && |b| > 0 {
    if a[0] <= b[0] {
      forall x | x in a[1..] ensures v <= x { assert x in a; }
      MergeHeadLe(a[1..], b, v);
      forall x | x in Merge(a, b) ensures v <= x {
        assert Merge(a, b) == [a[0]] + Merge(a[1..], b);
        if x == a[0] { assert a[0] in a; }
      }
    } else {
      forall x | x in b[1..] ensures v <= x { assert x in b; }
      MergeHeadLe(a, b[1..], v);
      forall x | x in Merge(a, b) ensures v <= x {
        assert Merge(a, b) == [b[0]] + Merge(a, b[1..]);
        if x == b[0] { assert b[0] in b; }
      }
    }
  }
}

lemma MergeSorted(a: seq<int>, b: seq<int>)
  requires Sorted(a) && Sorted(b)
  ensures Sorted(Merge(a, b))
  decreases |a| + |b|
{
  if |a| > 0 && |b| > 0 {
    SortedHeadMin(a);
    SortedHeadMin(b);
    if a[0] <= b[0] {
      SortedTail(a);
      MergeSorted(a[1..], b);
      MergeHeadLe(a[1..], b, a[0]);
      SortedPrepend(a[0], Merge(a[1..], b));
    } else {
      SortedTail(b);
      MergeSorted(a, b[1..]);
      MergeHeadLe(a, b[1..], b[0]);
      SortedPrepend(b[0], Merge(a, b[1..]));
    }
  }
}

// Two sorted sequences with the same multiset are identical.
lemma SortedMultisetUnique(x: seq<int>, y: seq<int>)
  requires Sorted(x) && Sorted(y) && multiset(x) == multiset(y)
  ensures x == y
  decreases |x|
{
  if |x| > 0 {
    SortedHeadMin(x);
    SortedHeadMin(y);
    assert |y| > 0;                        // equal multisets have equal size
    assert x[0] in multiset(x) && y[0] in multiset(y);
    assert x[0] in y && y[0] in x;         // each head is in the other seq (equal multisets)
    assert x[0] <= y[0] && y[0] <= x[0];   // each head is the minimum of its seq
    SortedTail(x);
    SortedTail(y);
    assert x == [x[0]] + x[1..] && y == [y[0]] + y[1..];
    assert multiset(x) == multiset{x[0]} + multiset(x[1..]);
    assert multiset(y) == multiset{y[0]} + multiset(y[1..]);
    assert multiset{x[0]} == multiset{y[0]};
    assert multiset(x[1..]) == multiset(x) - multiset{x[0]};
    assert multiset(y[1..]) == multiset(y) - multiset{y[0]};
    assert multiset(x[1..]) == multiset(y[1..]);
    SortedMultisetUnique(x[1..], y[1..]);
  }
}

// If every element of L is <= every element of R, their merge is the plain
// concatenation.
lemma MergeConcat(L: seq<int>, R: seq<int>)
  requires forall p, q :: p in L && q in R ==> p <= q
  ensures Merge(L, R) == L + R
  decreases |L|
{
  if |L| > 0 && |R| > 0 {
    assert L[0] in L && R[0] in R;
    forall p, q | p in L[1..] && q in R ensures p <= q { assert p in L; }
    MergeConcat(L[1..], R);
    assert L == [L[0]] + L[1..];
  }
}

lemma MergeMember(a: seq<int>, b: seq<int>, x: int)
  ensures x in Merge(a, b) <==> (x in a || x in b)
{
  MergeMultiset(a, b);
}

// The merge's multiset is unchanged by splitting each input at i / j.
lemma SplitMultiset(a: seq<int>, b: seq<int>, i: int, j: int)
  requires 0 <= i <= |a| && 0 <= j <= |b|
  ensures multiset(Merge(a, b))
       == multiset(Merge(a[..i], b[..j]) + Merge(a[i..], b[j..]))
{
  assert a == a[..i] + a[i..] && b == b[..j] + b[j..];
  calc {
     multiset(Merge(a, b));
  == { MergeMultiset(a, b); }
     multiset(a) + multiset(b);
  == multiset(a[..i]) + multiset(a[i..]) + multiset(b[..j]) + multiset(b[j..]);
  == { MergeMultiset(a[..i], b[..j]); MergeMultiset(a[i..], b[j..]); }
     multiset(Merge(a[..i], b[..j])) + multiset(Merge(a[i..], b[j..]));
  == multiset(Merge(a[..i], b[..j]) + Merge(a[i..], b[j..]));
  }
}

// THE PARTITION LEMMA: if a[..i]+b[..j] are all <= a[i..]+b[j..], the merge
// splits exactly there.
lemma MergeSplit(a: seq<int>, b: seq<int>, i: int, j: int)
  requires Sorted(a) && Sorted(b) && 0 <= i <= |a| && 0 <= j <= |b|
  requires forall p, q :: p in a[..i] + b[..j] && q in a[i..] + b[j..] ==> p <= q
  ensures Merge(a, b) == Merge(a[..i], b[..j]) + Merge(a[i..], b[j..])
{
  var L := Merge(a[..i], b[..j]);
  var R := Merge(a[i..], b[j..]);
  MergeSorted(a[..i], b[..j]);
  MergeSorted(a[i..], b[j..]);
  forall p, q | p in L && q in R
    ensures p <= q
  {
    MergeMember(a[..i], b[..j], p);
    MergeMember(a[i..], b[j..], q);
    assert p in a[..i] + b[..j] && q in a[i..] + b[j..];
  }
  MergeConcat(L, R);
  MergeSorted(L, R);
  MergeSorted(a, b);
  SplitMultiset(a, b, i, j);
  SortedMultisetUnique(Merge(a, b), L + R);
}

lemma SortedLastMax(s: seq<int>)
  requires Sorted(s) && |s| > 0
  ensures forall x :: x in s ==> x <= s[|s| - 1]
{
}

lemma FirstOfMerge(x: seq<int>, y: seq<int>)
  requires |x| + |y| > 0
  ensures |Merge(x, y)| == |x| + |y|
  ensures Merge(x, y)[0] ==
          (if |x| == 0 then y[0] else if |y| == 0 then x[0] else Min(x[0], y[0]))
{
  MergeLen(x, y);
}

lemma LastOfMerge(x: seq<int>, y: seq<int>)
  requires Sorted(x) && Sorted(y) && |x| + |y| > 0
  ensures |Merge(x, y)| == |x| + |y|
  ensures Merge(x, y)[|x| + |y| - 1] ==
          (if |x| == 0 then y[|y| - 1]
           else if |y| == 0 then x[|x| - 1]
           else Max(x[|x| - 1], y[|y| - 1]))
{
  MergeLen(x, y);
  MergeSorted(x, y);
  var M := Merge(x, y);
  SortedLastMax(M);
  var v := if |x| == 0 then y[|y| - 1]
  else if |y| == 0 then x[|x| - 1]
  else Max(x[|x| - 1], y[|y| - 1]);
  if |x| > 0 { SortedLastMax(x); assert x[|x| - 1] in x; }
  if |y| > 0 { SortedLastMax(y); assert y[|y| - 1] in y; }
  MergeMember(x, y, v);                 // v in M, so v <= M[last]
  MergeMember(x, y, M[|M| - 1]);        // M[last] in x or y, so M[last] <= v
}

// Boundary values of a partition (i, j): the largest on the left, smallest on
// the right.
function LeftVal(a: seq<int>, b: seq<int>, i: int, j: int): int
  requires 0 <= i <= |a| && 0 <= j <= |b| && i + j >= 1
{
  if i == 0 then b[j - 1] else if j == 0 then a[i - 1] else Max(a[i - 1], b[j - 1])
}

function RightVal(a: seq<int>, b: seq<int>, i: int, j: int): int
  requires 0 <= i <= |a| && 0 <= j <= |b| && (i < |a| || j < |b|)
{
  if i == |a| then b[j] else if j == |b| then a[i] else Min(a[i], b[j])
}

// k-th smallest (1-indexed) of the two sorted sequences = merge position k-1.
function Kth(a: seq<int>, b: seq<int>, k: int): int
  requires Sorted(a) && Sorted(b)
  requires 1 <= k <= |a| + |b|
{
  MergeLen(a, b);
  Merge(a, b)[k - 1]
}

lemma SortedSlice(s: seq<int>, lo: int, hi: int)
  requires Sorted(s) && 0 <= lo <= hi <= |s|
  ensures Sorted(s[lo..hi])
{
}

// The checkable "crossing" conditions (with -inf/+inf sentinels at the array
// ends) imply the partition precondition of MergeSplit.
lemma CrossingImpliesPartition(a: seq<int>, b: seq<int>, i: int, j: int)
  requires Sorted(a) && Sorted(b) && 0 <= i <= |a| && 0 <= j <= |b|
  requires i == 0 || j == |b| || a[i - 1] <= b[j]   // C1: left-a-max <= right-b-min
  requires j == 0 || i == |a| || b[j - 1] <= a[i]   // C2: left-b-max <= right-a-min
  ensures forall p, q :: p in a[..i] + b[..j] && q in a[i..] + b[j..] ==> p <= q
{
  if i > 0 { SortedSlice(a, 0, i); SortedLastMax(a[..i]); }
  if j > 0 { SortedSlice(b, 0, j); SortedLastMax(b[..j]); }
  if i < |a| { SortedSlice(a, i, |a|); SortedHeadMin(a[i..]); }
  if j < |b| { SortedSlice(b, j, |b|); SortedHeadMin(b[j..]); }
  forall p, q | p in a[..i] + b[..j] && q in a[i..] + b[j..]
    ensures p <= q
  {
    // p bounded above by a[i-1] or b[j-1]; q bounded below by a[i] or b[j].
  }
}

// Given a valid partition at (i, j) with the left side holding the lower half,
// the median values are exactly the partition's boundary values.
lemma MedianFromPartition(a: seq<int>, b: seq<int>, i: int, j: int)
  requires Sorted(a) && Sorted(b) && 0 <= i <= |a| && 0 <= j <= |b|
  requires |a| + |b| >= 1
  requires i + j == (|a| + |b| + 1) / 2
  requires forall p, q :: p in a[..i] + b[..j] && q in a[i..] + b[j..] ==> p <= q
  ensures Kth(a, b, (|a| + |b| + 1) / 2) == LeftVal(a, b, i, j)
  ensures (|a| + |b|) % 2 == 0 ==>
            Kth(a, b, (|a| + |b| + 1) / 2 + 1) == RightVal(a, b, i, j)
{
  var half := (|a| + |b| + 1) / 2;
  MergeSplit(a, b, i, j);
  var L := Merge(a[..i], b[..j]);
  var R := Merge(a[i..], b[j..]);
  MergeLen(a[..i], b[..j]);
  MergeLen(a[i..], b[j..]);
  MergeLen(a, b);
  assert |L| == half;
  assert Merge(a, b) == L + R;
  LastOfMerge(a[..i], b[..j]);
  assert Kth(a, b, half) == (L + R)[half - 1] == L[half - 1];
  if (|a| + |b|) % 2 == 0 {
    FirstOfMerge(a[i..], b[j..]);
    assert Kth(a, b, half + 1) == (L + R)[half] == R[0];
  }
}

// The median as a doubled integer (avoids floats): for total length t,
//   t odd  -> 2 * middle element
//   t even -> the two middle elements' sum
// The real median is MedianX2 / 2.
function MedianX2(a: seq<int>, b: seq<int>): int
  requires Sorted(a) && Sorted(b) && |a| + |b| >= 1
{
  var t := |a| + |b|;
  if t % 2 == 1 then 2 * Kth(a, b, (t + 1) / 2)
  else Kth(a, b, t / 2) + Kth(a, b, t / 2 + 1)
}

// The left-partition condition C1 at index i (j = half - i): a's left maximum
// does not exceed b's right minimum. Includes the index-range facts so it can
// be used freely in invariants. Monotone: true for small i, false for large i.
predicate C1(a: seq<int>, b: seq<int>, half: int, i: int) {
  0 <= i <= |a| && 0 <= half - i <= |b| &&
  (i == 0 || half - i == |b| || a[i - 1] <= b[half - i])
}

lemma C1Step(a: seq<int>, b: seq<int>, half: int, i: int)
  requires Sorted(a) && Sorted(b)
  requires 0 <= i < |a| && 0 <= half - (i + 1) && half - i <= |b|
  requires !C1(a, b, half, i)
  ensures !C1(a, b, half, i + 1)
{
  // !C1(i): a[i-1] > b[half-i]. Then a[i] >= a[i-1] > b[half-i] >= b[half-i-1].
}

lemma C1FalseUp(a: seq<int>, b: seq<int>, half: int, i: int, i2: int)
  requires Sorted(a) && Sorted(b)
  requires 0 <= i <= i2 <= |a| && 0 <= half - i2 && half - i <= |b|
  requires !C1(a, b, half, i)
  ensures !C1(a, b, half, i2)
  decreases i2 - i
{
  if i < i2 {
    C1Step(a, b, half, i);
    C1FalseUp(a, b, half, i + 1, i2);
  }
}

// The median in doubled-integer form, via the O(log) partition binary search.
// Requires |a| <= |b| (so j = half - i is always a valid index into b).
method MedianX2Search(a: seq<int>, b: seq<int>) returns (r: int)
  requires Sorted(a) && Sorted(b) && |a| + |b| >= 1 && |a| <= |b|
  ensures r == MedianX2(a, b)
{
  var m, n := |a|, |b|;
  var half := (m + n + 1) / 2;

  // Binary search for the largest i in [0, m] with C1(a, b, half, i).
  var lo, hi := 0, m;
  while lo < hi
    invariant 0 <= lo <= hi <= m
    invariant C1(a, b, half, lo)
    invariant forall i2 :: hi < i2 <= m ==> !C1(a, b, half, i2)
    decreases hi - lo
  {
    var mid := (lo + hi + 1) / 2;
    if C1(a, b, half, mid) {
      lo := mid;
    } else {
      forall i2 | mid <= i2 <= m ensures !C1(a, b, half, i2) { C1FalseUp(a, b, half, mid, i2); }
      hi := mid - 1;
    }
  }

  var i := lo;
  var j := half - i;
  // C1(i) holds; and if i < m then !C1(i+1), which yields C2 at i.
  assert C1(a, b, half, i);
  assert i == 0 || j == n || a[i - 1] <= b[j];             // C1 unfolded
  if i < m {
    assert !C1(a, b, half, i + 1);
  }
  assert j == 0 || i == m || b[j - 1] <= a[i];             // C2

  CrossingImpliesPartition(a, b, i, j);
  MedianFromPartition(a, b, i, j);
  if (m + n) % 2 == 1 {
    r := 2 * LeftVal(a, b, i, j);
  } else {
    r := LeftVal(a, b, i, j) + RightVal(a, b, i, j);
  }
}

// The LeetCode examples (doubled to stay in the integers): [1,3],[2] has
// median 2.0 (= 4/2) and [1,2],[3,4] has median 2.5 (= 5/2). Proved by
// exhibiting the merged arrays explicitly (keeping Merge at default fuel, so
// the heavier multiset lemmas stay fast).
lemma ExampleOdd()
  ensures MedianX2([1, 3], [2]) == 4
{
  assert Merge([1, 3], [2]) == [1, 2, 3];
  MergeLen([1, 3], [2]);
}

lemma ExampleEven()
  ensures MedianX2([1, 2], [3, 4]) == 5
{
  assert Merge([1, 2], [3, 4]) == [1, 2, 3, 4];
  MergeLen([1, 2], [3, 4]);
}
