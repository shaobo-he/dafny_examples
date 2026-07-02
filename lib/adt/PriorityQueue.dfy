// Author: Shaobo He
// A verified functional min-priority-queue (leftist heap). Each element is a
// (key, data) pair ordered by the integer key. FindMin returns an element of
// minimum key; Insert / DeleteMin / Merge preserve both the heap order and the
// multiset of elements. (The leftist rank keeps operations O(log n); we verify
// the functional contract, not the balance bound.)

module PriorityQueue {

  datatype PQ<T> = Empty | Node(rank: nat, key: int, data: T, left: PQ<T>, right: PQ<T>)

  function Rank<T>(h: PQ<T>): nat {
    match h case Empty => 0 case Node(r, _, _, _, _) => r
  }

  function Size<T>(h: PQ<T>): nat {
    match h case Empty => 0 case Node(_, _, _, l, r) => 1 + Size(l) + Size(r)
  }

  function Items<T(==)>(h: PQ<T>): multiset<(int, T)> {
    match h
    case Empty => multiset{}
    case Node(_, k, d, l, r) => multiset{(k, d)} + Items(l) + Items(r)
  }

  // Every element's key is at least the root key, recursively.
  predicate HeapOrdered<T(==)>(h: PQ<T>) {
    match h
    case Empty => true
    case Node(_, k, d, l, r) =>
      HeapOrdered(l) && HeapOrdered(r) &&
      (forall e :: e in Items(l) ==> k <= e.0) &&
      (forall e :: e in Items(r) ==> k <= e.0)
  }

  // Combine two ordered subtrees under a key that is a lower bound of both,
  // placing the higher-rank child on the left (the leftist property).
  function MakeNode<T>(k: int, d: T, a: PQ<T>, b: PQ<T>): PQ<T> {
    if Rank(a) >= Rank(b) then Node(Rank(b) + 1, k, d, a, b)
    else Node(Rank(a) + 1, k, d, b, a)
  }

  lemma MakeNodeItems<T>(k: int, d: T, a: PQ<T>, b: PQ<T>)
    ensures Items(MakeNode(k, d, a, b)) == multiset{(k, d)} + Items(a) + Items(b)
  {
  }

  lemma MakeNodeOrdered<T>(k: int, d: T, a: PQ<T>, b: PQ<T>)
    requires HeapOrdered(a) && HeapOrdered(b)
    requires forall e :: e in Items(a) ==> k <= e.0
    requires forall e :: e in Items(b) ==> k <= e.0
    ensures HeapOrdered(MakeNode(k, d, a, b))
  {
  }

  function Merge<T(==)>(a: PQ<T>, b: PQ<T>): PQ<T>
    decreases Size(a) + Size(b)
  {
    if a.Empty? then b
    else if b.Empty? then a
    else if a.key <= b.key then MakeNode(a.key, a.data, a.left, Merge(a.right, b))
    else MakeNode(b.key, b.data, b.left, Merge(a, b.right))
  }

  lemma MergeSize<T>(a: PQ<T>, b: PQ<T>)
    ensures Size(Merge(a, b)) == Size(a) + Size(b)
    decreases Size(a) + Size(b)
  {
    if !a.Empty? && !b.Empty? {
      if a.key <= b.key {
        MergeSize(a.right, b);
      } else {
        MergeSize(a, b.right);
      }
    }
  }

  lemma MergeItems<T>(a: PQ<T>, b: PQ<T>)
    ensures Items(Merge(a, b)) == Items(a) + Items(b)
    decreases Size(a) + Size(b)
  {
    if !a.Empty? && !b.Empty? {
      if a.key <= b.key {
        MergeItems(a.right, b);
        MakeNodeItems(a.key, a.data, a.left, Merge(a.right, b));
      } else {
        MergeItems(a, b.right);
        MakeNodeItems(b.key, b.data, b.left, Merge(a, b.right));
      }
    }
  }

  lemma MergeOrdered<T>(a: PQ<T>, b: PQ<T>)
    requires HeapOrdered(a) && HeapOrdered(b)
    ensures HeapOrdered(Merge(a, b))
    decreases Size(a) + Size(b)
  {
    if !a.Empty? && !b.Empty? {
      if a.key <= b.key {
        MergeOrdered(a.right, b);
        MergeItems(a.right, b);
        assert forall e :: e in Items(Merge(a.right, b)) ==> a.key <= e.0;
        MakeNodeOrdered(a.key, a.data, a.left, Merge(a.right, b));
      } else {
        MergeOrdered(a, b.right);
        MergeItems(a, b.right);
        assert forall e :: e in Items(Merge(a, b.right)) ==> b.key <= e.0;
        MakeNodeOrdered(b.key, b.data, b.left, Merge(a, b.right));
      }
    }
  }

  // ---- Public operations -------------------------------------------------

  function Singleton<T>(k: int, d: T): PQ<T> {
    Node(1, k, d, Empty, Empty)
  }

  function Insert<T(==)>(k: int, d: T, h: PQ<T>): PQ<T> {
    Merge(Singleton(k, d), h)
  }

  function FindMin<T>(h: PQ<T>): (int, T)
    requires h.Node?
  {
    (h.key, h.data)
  }

  function DeleteMin<T(==)>(h: PQ<T>): PQ<T>
    requires h.Node?
  {
    Merge(h.left, h.right)
  }

  // ---- Contracts the public operations satisfy ---------------------------

  lemma InsertCorrect<T>(k: int, d: T, h: PQ<T>)
    requires HeapOrdered(h)
    ensures HeapOrdered(Insert(k, d, h))
    ensures Items(Insert(k, d, h)) == Items(h) + multiset{(k, d)}
    ensures Size(Insert(k, d, h)) == Size(h) + 1
  {
    MergeOrdered(Singleton(k, d), h);
    MergeItems(Singleton(k, d), h);
    MergeSize(Singleton(k, d), h);
  }

  // FindMin returns an element with the smallest key in the queue.
  lemma FindMinIsMin<T>(h: PQ<T>)
    requires h.Node? && HeapOrdered(h)
    ensures FindMin(h) in Items(h)
    ensures forall e :: e in Items(h) ==> FindMin(h).0 <= e.0
  {
  }

  lemma DeleteMinCorrect<T>(h: PQ<T>)
    requires h.Node? && HeapOrdered(h)
    ensures HeapOrdered(DeleteMin(h))
    ensures Items(DeleteMin(h)) == Items(h) - multiset{(h.key, h.data)}
    ensures Size(DeleteMin(h)) == Size(h) - 1
  {
    MergeOrdered(h.left, h.right);
    MergeItems(h.left, h.right);
    MergeSize(h.left, h.right);
  }
}
