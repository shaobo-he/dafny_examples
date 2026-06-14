// Author: Shaobo He
// LeetCode 340: Longest Substring with At Most K Distinct Characters
// Given a string s and an integer k, return the length of the longest substring
// of s that contains at most k distinct characters.

function CharsOf(s: string): set<char> {
  set idx | 0 <= idx < |s| :: s[idx]
}

function Distinct(s: string): nat {
  |CharsOf(s)|
}

lemma CharsOfSubseq(s: string, i: int, j: int, i': int, j': int)
  requires 0 <= i' <= i <= j <= j' <= |s|
  ensures CharsOf(s[i..j]) <= CharsOf(s[i'..j'])
{
  forall c | c in CharsOf(s[i..j])
    ensures c in CharsOf(s[i'..j'])
  {
    var idx :| 0 <= idx < |s[i..j]| && s[i..j][idx] == c;
    assert s[i..j][idx] == s[i + idx];
    assert 0 <= i + idx - i' < j' - i';
    assert s[i'..j'][i + idx - i'] == s[i + idx];
  }
}

lemma SetCardSubset<T>(a: set<T>, b: set<T>)
  requires a <= b
  ensures |a| <= |b|
{
  if |a| > 0 {
    var x :| x in a;
    SetCardSubset(a - {x}, b - {x});
  }
}

lemma DistinctSubseq(s: string, i: int, j: int, i': int, j': int)
  requires 0 <= i' <= i <= j <= j' <= |s|
  ensures Distinct(s[i..j]) <= Distinct(s[i'..j'])
{
  CharsOfSubseq(s, i, j, i', j');
  SetCardSubset(CharsOf(s[i..j]), CharsOf(s[i'..j']));
}

method LongestSubstring(s: string, k: nat) returns (result: nat)
  ensures result <= |s|
  ensures forall i, j :: 0 <= i <= j <= |s| && Distinct(s[i..j]) <= k ==> j - i <= result
  ensures exists i, j :: 0 <= i <= j <= |s| && Distinct(s[i..j]) <= k && j - i == result
{
  result := 0;
  var l := 0;
  var r := 0;
  ghost var wi, wj := 0, 0;
  assert s[0..0] == "";
  while r < |s|
    invariant 0 <= l <= r <= |s|
    invariant result <= r
    invariant Distinct(s[l..r]) <= k
    invariant forall l' :: 0 <= l' < l ==> Distinct(s[l'..r]) > k
    invariant forall i, j :: 0 <= i <= j <= r && Distinct(s[i..j]) <= k ==> j - i <= result
    invariant 0 <= wi <= wj <= |s| && Distinct(s[wi..wj]) <= k && wj - wi == result
  {
    forall l' {:trigger Distinct(s[l'..r+1])} | 0 <= l' < l
      ensures Distinct(s[l'..r+1]) > k
    {
      DistinctSubseq(s, l', r, l', r+1);
    }
    while Distinct(s[l..r+1]) > k
      invariant 0 <= l <= r + 1
      invariant forall l' {:trigger Distinct(s[l'..r+1])} :: 0 <= l' < l ==> Distinct(s[l'..r+1]) > k
      decreases r + 1 - l
    {
      l := l + 1;
    }
    r := r + 1;
    if r - l > result {
      result := r - l;
      wi, wj := l, r;
    }
  }
}
