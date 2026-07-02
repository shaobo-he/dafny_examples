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

// A schedule of non-overlapping transactions: each (buy, sell) has buy <= sell,
// and one transaction's sell is no later than the next transaction's buy.
predicate ValidTxns(txns: seq<(nat, nat)>, n: nat) {
  (forall i :: 0 <= i < |txns| ==> txns[i].0 <= txns[i].1 < n) &&
  (forall i :: 0 <= i < |txns| - 1 ==> txns[i].1 <= txns[i + 1].0)
}

function TxnProfit(prices: seq<int>, txns: seq<(nat, nat)>): int
  requires forall i :: 0 <= i < |txns| ==> txns[i].0 <= txns[i].1 < |prices|
{
  if |txns| == 0 then 0
  else (prices[txns[0].1] - prices[txns[0].0]) + TxnProfit(prices, txns[1..])
}

lemma ValidTxnsTail(txns: seq<(nat, nat)>, n: nat)
  requires |txns| > 0 && ValidTxns(txns, n)
  ensures ValidTxns(txns[1..], n)
{
  forall i | 0 <= i < |txns[1..]|
    ensures txns[1..][i].0 <= txns[1..][i].1 < n
  {
    assert txns[1..][i] == txns[i + 1];
  }
}

// The greedy total dominates any non-overlapping schedule's profit. Generalized
// with a lower cut `lo` so the telescoping goes through.
lemma TxnProfitUBAux(prices: seq<int>, txns: seq<(nat, nat)>, n: nat, lo: nat)
  requires n <= |prices|
  requires ValidTxns(txns, n)
  requires lo <= n
  requires |txns| == 0 || lo <= txns[0].0 + 1
  ensures forall i :: 0 <= i < |txns| ==> txns[i].0 <= txns[i].1 < |prices|
  ensures TxnProfit(prices, txns) <= Greedy(prices, n) - Greedy(prices, lo)
  decreases |txns|
{
  if |txns| == 0 {
    GreedyMono(prices, lo, n);
  } else {
    var b0, s0 := txns[0].0, txns[0].1;
    ValidTxnsTail(txns, n);
    SingleTxUB(prices, b0, s0);
    TxnProfitUBAux(prices, txns[1..], n, s0 + 1);
    GreedyMono(prices, lo, b0 + 1);
  }
}

lemma TxnProfitUB(prices: seq<int>, txns: seq<(nat, nat)>, n: nat)
  requires n <= |prices|
  requires ValidTxns(txns, n)
  ensures forall i :: 0 <= i < |txns| ==> txns[i].0 <= txns[i].1 < |prices|
  ensures TxnProfit(prices, txns) <= Greedy(prices, n)
{
  TxnProfitUBAux(prices, txns, n, 0);
}

method MaxProfit(prices: array<int>) returns (profit: int)
  requires 1 <= prices.Length
  ensures profit >= 0
  ensures profit == Greedy(prices[..], prices.Length)
  ensures forall i, j :: 0 <= i <= j < prices.Length ==> prices[j] - prices[i] <= profit
  // Optimality over ALL non-overlapping multi-transaction schedules, not just a
  // single transaction: no schedule earns more than profit.
  ensures forall txns: seq<(nat, nat)> :: ValidTxns(txns, prices.Length) ==>
                                            (forall i :: 0 <= i < |txns| ==> txns[i].0 <= txns[i].1 < prices.Length) &&
                                            TxnProfit(prices[..], txns) <= profit
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
  forall txns: seq<(nat, nat)> | ValidTxns(txns, prices.Length)
    ensures (forall i :: 0 <= i < |txns| ==> txns[i].0 <= txns[i].1 < prices.Length)
    ensures TxnProfit(prices[..], txns) <= profit
  {
    TxnProfitUB(prices[..], txns, prices.Length);
  }
}
