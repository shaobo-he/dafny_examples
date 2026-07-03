// Author: Shaobo He
// LeetCode 123: Best Time to Buy and Sell Stock III
// At most two non-overlapping transactions; max profit.
//
// The DP states are given as recursive specifications B1/S1/B2/S2 (best buy1,
// sell1, buy2, sell2 considering the first m prices). The loop only maintains
// the cheap, quantifier-free equalities state == spec; the quantified upper
// bound and the existential achievability are each proved as an isolated
// induction (keeping every verification condition small and stable).

function Max(a: int, b: int): int { if a >= b then a else b }

function B1(p: seq<int>, m: int): int   // max over 0<=b<m of  -p[b]
  requires 1 <= m <= |p|
  decreases m, 0
{
  if m == 1 then -p[0] else Max(B1(p, m - 1), -p[m - 1])
}

function S1(p: seq<int>, m: int): int   // max over 0<=b<=s<m of  p[s]-p[b]
  requires 1 <= m <= |p|
  decreases m, 1
{
  if m == 1 then 0 else Max(S1(p, m - 1), B1(p, m) + p[m - 1])
}

function B2(p: seq<int>, m: int): int   // max over 0<=b1<=s1<=b2<m ... one tx then buy again
  requires 1 <= m <= |p|
  decreases m, 2
{
  if m == 1 then -p[0] else Max(B2(p, m - 1), S1(p, m) - p[m - 1])
}

function S2(p: seq<int>, m: int): int   // max two-transaction profit over first m prices
  requires 1 <= m <= |p|
  decreases m, 3
{
  if m == 1 then 0 else Max(S2(p, m - 1), B2(p, m) + p[m - 1])
}

// ---- Upper bounds: each spec dominates every corresponding choice of indices.

lemma B1UB(p: seq<int>, m: int, b: int)
  requires 1 <= m <= |p| && 0 <= b < m
  ensures -p[b] <= B1(p, m)
{
  if b < m - 1 {
    B1UB(p, m - 1, b);
  }
}

lemma S1UB(p: seq<int>, m: int, b: int, s: int)
  requires 1 <= m <= |p| && 0 <= b <= s < m
  ensures p[s] - p[b] <= S1(p, m)
{
  if s < m - 1 {
    S1UB(p, m - 1, b, s);
  } else {
    B1UB(p, m, b);
  }
}

lemma B2UB(p: seq<int>, m: int, b1: int, s1: int, b2: int)
  requires 1 <= m <= |p| && 0 <= b1 <= s1 <= b2 < m
  ensures p[s1] - p[b1] - p[b2] <= B2(p, m)
{
  if b2 < m - 1 {
    B2UB(p, m - 1, b1, s1, b2);
  } else {
    S1UB(p, m, b1, s1);
  }
}

lemma S2UB(p: seq<int>, m: int, b1: int, s1: int, b2: int, s2: int)
  requires 1 <= m <= |p| && 0 <= b1 <= s1 <= b2 <= s2 < m
  ensures (p[s1] - p[b1]) + (p[s2] - p[b2]) <= S2(p, m)
{
  if s2 < m - 1 {
    S2UB(p, m - 1, b1, s1, b2, s2);
  } else {
    B2UB(p, m, b1, s1, b2);
  }
}

lemma S2NonNeg(p: seq<int>, m: int)
  requires 1 <= m <= |p|
  ensures S2(p, m) >= 0
{
  if m > 1 {
    S2NonNeg(p, m - 1);
  }
}

// ---- Achievability: each spec is realized by an actual choice of indices.

lemma B1Ach(p: seq<int>, m: int)
  requires 1 <= m <= |p|
  ensures exists b :: 0 <= b < m && B1(p, m) == -p[b]
  decreases m
{
  if m == 1 {
    assert 0 <= 0 < 1 && B1(p, m) == -p[0];
  } else if B1(p, m) == -p[m - 1] {
    assert 0 <= m - 1 < m && B1(p, m) == -p[m - 1];
  } else {
    B1Ach(p, m - 1);
    var b :| 0 <= b < m - 1 && B1(p, m - 1) == -p[b];
    assert 0 <= b < m && B1(p, m) == -p[b];
  }
}

lemma S1Ach(p: seq<int>, m: int)
  requires 1 <= m <= |p|
  ensures exists b, s :: 0 <= b <= s < m && S1(p, m) == p[s] - p[b]
  decreases m
{
  if m == 1 {
    assert 0 <= 0 <= 0 < 1 && S1(p, m) == p[0] - p[0];
  } else if S1(p, m) == B1(p, m) + p[m - 1] {
    B1Ach(p, m);
    var b :| 0 <= b < m && B1(p, m) == -p[b];
    assert 0 <= b <= m - 1 < m && S1(p, m) == p[m - 1] - p[b];
  } else {
    S1Ach(p, m - 1);
    var b, s :| 0 <= b <= s < m - 1 && S1(p, m - 1) == p[s] - p[b];
    assert 0 <= b <= s < m && S1(p, m) == p[s] - p[b];
  }
}

lemma B2Ach(p: seq<int>, m: int)
  requires 1 <= m <= |p|
  ensures exists b1, s1, b2 :: 0 <= b1 <= s1 <= b2 < m && B2(p, m) == p[s1] - p[b1] - p[b2]
  decreases m
{
  if m == 1 {
    assert 0 <= 0 <= 0 <= 0 < 1 && B2(p, m) == p[0] - p[0] - p[0];
  } else if B2(p, m) == S1(p, m) - p[m - 1] {
    S1Ach(p, m);
    var b1, s1 :| 0 <= b1 <= s1 < m && S1(p, m) == p[s1] - p[b1];
    assert 0 <= b1 <= s1 <= m - 1 < m && B2(p, m) == p[s1] - p[b1] - p[m - 1];
  } else {
    B2Ach(p, m - 1);
    var b1, s1, b2 :| 0 <= b1 <= s1 <= b2 < m - 1 && B2(p, m - 1) == p[s1] - p[b1] - p[b2];
    assert 0 <= b1 <= s1 <= b2 < m && B2(p, m) == p[s1] - p[b1] - p[b2];
  }
}

lemma S2Ach(p: seq<int>, m: int)
  requires 1 <= m <= |p|
  ensures exists b1, s1, b2, s2 ::
            0 <= b1 <= s1 <= b2 <= s2 < m && S2(p, m) == (p[s1] - p[b1]) + (p[s2] - p[b2])
  decreases m
{
  if m == 1 {
    assert 0 <= 0 <= 0 <= 0 <= 0 < 1 && S2(p, m) == (p[0] - p[0]) + (p[0] - p[0]);
  } else if S2(p, m) == B2(p, m) + p[m - 1] {
    B2Ach(p, m);
    var b1, s1, b2 :| 0 <= b1 <= s1 <= b2 < m && B2(p, m) == p[s1] - p[b1] - p[b2];
    assert 0 <= b1 <= s1 <= b2 <= m - 1 < m &&
           S2(p, m) == (p[s1] - p[b1]) + (p[m - 1] - p[b2]);
  } else {
    S2Ach(p, m - 1);
    var b1, s1, b2, s2 :|
      0 <= b1 <= s1 <= b2 <= s2 < m - 1 && S2(p, m - 1) == (p[s1] - p[b1]) + (p[s2] - p[b2]);
    assert 0 <= b1 <= s1 <= b2 <= s2 < m && S2(p, m) == (p[s1] - p[b1]) + (p[s2] - p[b2]);
  }
}

method MaxProfit(prices: array<int>) returns (profit: int)
  requires 1 <= prices.Length
  ensures profit >= 0
  // Upper bound: no two-transaction strategy beats profit.
  ensures forall b1, s1, b2, s2 ::
            0 <= b1 <= s1 <= b2 <= s2 < prices.Length ==>
              (prices[s1] - prices[b1]) + (prices[s2] - prices[b2]) <= profit
  // Achievability: profit is realized by an actual choice of indices.
  ensures exists b1, s1, b2, s2 ::
            0 <= b1 <= s1 <= b2 <= s2 < prices.Length &&
            profit == (prices[s1] - prices[b1]) + (prices[s2] - prices[b2])
{
  var buy1, sell1, buy2, sell2 := -prices[0], 0, -prices[0], 0;
  var k := 1;
  while k < prices.Length
    invariant 1 <= k <= prices.Length
    invariant buy1 == B1(prices[..], k)
    invariant sell1 == S1(prices[..], k)
    invariant buy2 == B2(prices[..], k)
    invariant sell2 == S2(prices[..], k)
  {
    var nb1 := Max(buy1, -prices[k]);         // == B1(prices[..], k+1)
    var ns1 := Max(sell1, nb1 + prices[k]);   // == S1(prices[..], k+1)
    var nb2 := Max(buy2, ns1 - prices[k]);    // == B2(prices[..], k+1)
    var ns2 := Max(sell2, nb2 + prices[k]);   // == S2(prices[..], k+1)
    buy1, sell1, buy2, sell2 := nb1, ns1, nb2, ns2;
    k := k + 1;
  }
  profit := sell2;
  S2NonNeg(prices[..], prices.Length);
  forall b1, s1, b2, s2 | 0 <= b1 <= s1 <= b2 <= s2 < prices.Length
    ensures (prices[s1] - prices[b1]) + (prices[s2] - prices[b2]) <= profit
  {
    S2UB(prices[..], prices.Length, b1, s1, b2, s2);
  }
  S2Ach(prices[..], prices.Length);
}
