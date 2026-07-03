module MinMax {

  function Min(a: int, b: int): int {
    if a <= b then a else b
  }

  function Max(a: int, b: int): int {
    if a >= b then a else b
  }

  lemma MinProps(a: int, b: int)
    ensures Min(a, b) <= a
    ensures Min(a, b) <= b
    ensures Min(a, b) == a || Min(a, b) == b
  {
  }

  lemma MaxProps(a: int, b: int)
    ensures a <= Max(a, b)
    ensures b <= Max(a, b)
    ensures Max(a, b) == a || Max(a, b) == b
  {
  }

  lemma MinGreatestLowerBound(a: int, b: int, x: int)
    ensures x <= a && x <= b ==> x <= Min(a, b)
  {
  }

  lemma MaxLeastUpperBound(a: int, b: int, x: int)
    ensures a <= x && b <= x ==> Max(a, b) <= x
  {
  }

  lemma MinCommutative(a: int, b: int)
    ensures Min(a, b) == Min(b, a)
  {
  }

  lemma MaxCommutative(a: int, b: int)
    ensures Max(a, b) == Max(b, a)
  {
  }

  lemma MinIdempotent(a: int)
    ensures Min(a, a) == a
  {
  }

  lemma MaxIdempotent(a: int)
    ensures Max(a, a) == a
  {
  }

  lemma MinAssociative(a: int, b: int, c: int)
    ensures Min(Min(a, b), c) == Min(a, Min(b, c))
  {
  }

  lemma MaxAssociative(a: int, b: int, c: int)
    ensures Max(Max(a, b), c) == Max(a, Max(b, c))
  {
  }

  lemma MinMaxAbsorption(a: int, b: int)
    ensures Min(a, Max(a, b)) == a
    ensures Max(a, Min(a, b)) == a
  {
  }

  lemma MinEqMax(a: int, b: int)
    requires Min(a, b) == Max(a, b)
    ensures a == b
  {
  }

}