// Author: Shaobo He
// LeetCode 123: Best Time to Buy and Sell Stock III
// At most two non-overlapping transactions; max profit.

method MaxProfit(prices: array<int>) returns (profit: int)
  requires 1 <= prices.Length
  ensures profit >= 0
  // Upper bound: no two-transaction strategy beats profit.
  ensures forall b1, s1, b2, s2 ::
            0 <= b1 <= s1 <= b2 <= s2 < prices.Length ==>
              (prices[s1] - prices[b1]) + (prices[s2] - prices[b2]) <= profit
  // Achievability: profit is realized by an actual choice of indices (so it is
  // the exact maximum, not merely an upper bound -- a large constant would fail).
  ensures exists b1, s1, b2, s2 ::
            0 <= b1 <= s1 <= b2 <= s2 < prices.Length &&
            profit == (prices[s1] - prices[b1]) + (prices[s2] - prices[b2])
{
  var buy1, sell1, buy2, sell2 := -prices[0], 0, -prices[0], 0;
  // Ghost witnesses realizing each running optimum (degenerate at index 0).
  ghost var wb1 := 0;
  ghost var e1b1, e1s1 := 0, 0;
  ghost var e2b1, e2s1, e2b2 := 0, 0, 0;
  ghost var e3b1, e3s1, e3b2, e3s2 := 0, 0, 0, 0;
  var k := 1;
  while k < prices.Length
    invariant 1 <= k <= prices.Length
    invariant sell1 >= 0 && sell2 >= 0
    invariant forall b :: 0 <= b < k ==> -prices[b] <= buy1
    invariant forall b, s :: 0 <= b <= s < k ==> prices[s] - prices[b] <= sell1
    invariant forall b1, s1, b2 :: 0 <= b1 <= s1 <= b2 < k ==>
                                     prices[s1] - prices[b1] - prices[b2] <= buy2
    invariant forall b1, s1, b2, s2 :: 0 <= b1 <= s1 <= b2 <= s2 < k ==>
                                         (prices[s1] - prices[b1]) + (prices[s2] - prices[b2]) <= sell2
    // witnesses stay in range and realize the current values
    invariant 0 <= wb1 < k && buy1 == -prices[wb1]
    invariant 0 <= e1b1 <= e1s1 < k && sell1 == prices[e1s1] - prices[e1b1]
    invariant 0 <= e2b1 <= e2s1 <= e2b2 < k &&
              buy2 == prices[e2s1] - prices[e2b1] - prices[e2b2]
    invariant 0 <= e3b1 <= e3s1 <= e3b2 <= e3s2 < k &&
              sell2 == (prices[e3s1] - prices[e3b1]) + (prices[e3s2] - prices[e3b2])
  {
    var nb1 := if -prices[k] > buy1 then -prices[k] else buy1;
    var ns1 := if nb1 + prices[k] > sell1 then nb1 + prices[k] else sell1;
    var nb2 := if ns1 - prices[k] > buy2 then ns1 - prices[k] else buy2;
    var ns2 := if nb2 + prices[k] > sell2 then nb2 + prices[k] else sell2;

    // Update witnesses in lockstep with the max choices.
    ghost var nwb1 := if -prices[k] > buy1 then k else wb1;
    ghost var f1b1 := if nb1 + prices[k] > sell1 then nwb1 else e1b1;
    ghost var f1s1 := if nb1 + prices[k] > sell1 then k else e1s1;
    ghost var f2b1 := if ns1 - prices[k] > buy2 then f1b1 else e2b1;
    ghost var f2s1 := if ns1 - prices[k] > buy2 then f1s1 else e2s1;
    ghost var f2b2 := if ns1 - prices[k] > buy2 then k else e2b2;
    ghost var f3b1 := if nb2 + prices[k] > sell2 then f2b1 else e3b1;
    ghost var f3s1 := if nb2 + prices[k] > sell2 then f2s1 else e3s1;
    ghost var f3b2 := if nb2 + prices[k] > sell2 then f2b2 else e3b2;
    ghost var f3s2 := if nb2 + prices[k] > sell2 then k else e3s2;

    buy1, sell1, buy2, sell2 := nb1, ns1, nb2, ns2;
    wb1 := nwb1;
    e1b1, e1s1 := f1b1, f1s1;
    e2b1, e2s1, e2b2 := f2b1, f2s1, f2b2;
    e3b1, e3s1, e3b2, e3s2 := f3b1, f3s1, f3b2, f3s2;
    k := k + 1;
  }
  profit := sell2;
}
