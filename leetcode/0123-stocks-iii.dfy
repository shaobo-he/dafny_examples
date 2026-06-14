// Author: Shaobo He
// LeetCode 123: Best Time to Buy and Sell Stock III
// At most two non-overlapping transactions; max profit.

method MaxProfit(prices: array<int>) returns (profit: int)
  requires 1 <= prices.Length
  ensures profit >= 0
  ensures forall b1, s1, b2, s2 ::
            0 <= b1 <= s1 <= b2 <= s2 < prices.Length ==>
              (prices[s1] - prices[b1]) + (prices[s2] - prices[b2]) <= profit
{
  var buy1: int := -prices[0];
  var sell1: int := 0;
  var buy2: int := -prices[0];
  var sell2: int := 0;
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
  {
    var nb1 := if -prices[k] > buy1 then -prices[k] else buy1;
    var ns1 := if nb1 + prices[k] > sell1 then nb1 + prices[k] else sell1;
    var nb2 := if ns1 - prices[k] > buy2 then ns1 - prices[k] else buy2;
    var ns2 := if nb2 + prices[k] > sell2 then nb2 + prices[k] else sell2;
    buy1, sell1, buy2, sell2 := nb1, ns1, nb2, ns2;
    k := k + 1;
  }
  profit := sell2;
}
