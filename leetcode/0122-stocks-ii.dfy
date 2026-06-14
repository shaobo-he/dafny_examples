// Author: Shaobo He
// LeetCode 122: Best Time to Buy and Sell Stock II
// Unlimited transactions; greedy sum of positive consecutive deltas.

function Greedy(prices: seq<int>, k: nat): int
  requires k <= |prices|
{
  if k <= 1 then 0
  else Greedy(prices, k - 1) +
       (if prices[k - 1] > prices[k - 2] then prices[k - 1] - prices[k - 2] else 0)
}

lemma GreedyNonNeg(prices: seq<int>, k: nat)
  requires k <= |prices|
  ensures Greedy(prices, k) >= 0
{
  if k > 1 {
    GreedyNonNeg(prices, k - 1);
  }
}

lemma GreedyMono(prices: seq<int>, a: nat, b: nat)
  requires a <= b <= |prices|
  ensures Greedy(prices, a) <= Greedy(prices, b)
{
  if a < b {
    GreedyMono(prices, a, b - 1);
  }
}

lemma SingleTxUB(prices: seq<int>, b: nat, s: nat)
  requires b <= s < |prices|
  ensures prices[s] - prices[b] <= Greedy(prices, s + 1) - Greedy(prices, b + 1)
{
  if s > b {
    SingleTxUB(prices, b, s - 1);
  }
}

method MaxProfit(prices: array<int>) returns (profit: int)
  requires 1 <= prices.Length
  ensures profit >= 0
  ensures profit == Greedy(prices[..], prices.Length)
  ensures forall i, j :: 0 <= i <= j < prices.Length ==> prices[j] - prices[i] <= profit
{
  profit := 0;
  var k := 1;
  while k < prices.Length
    invariant 1 <= k <= prices.Length
    invariant profit == Greedy(prices[..], k)
  {
    if prices[k] > prices[k - 1] {
      profit := profit + prices[k] - prices[k - 1];
    }
    k := k + 1;
  }
  GreedyNonNeg(prices[..], prices.Length);
  forall i, j | 0 <= i <= j < prices.Length
    ensures prices[j] - prices[i] <= profit
  {
    SingleTxUB(prices[..], i, j);
    GreedyMono(prices[..], j + 1, prices.Length);
    GreedyNonNeg(prices[..], i + 1);
  }
}
