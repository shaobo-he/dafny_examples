include "Abs.dfy"

function {:opaque} Gcd(a: int, b: int): int
  decreases Abs(b)
{
  if b != 0 then Gcd(b, a % b) else if a == 0 then 1 else Abs(a)
}

lemma Gcd00()
  ensures Gcd(0, 0) == 1
{
  reveal Gcd();
}

lemma GcdPos(a: int, b: int)
  ensures 0 < Gcd(a, b)
  decreases Abs(b)
{
  reveal Gcd();
  if b != 0 {
    GcdPos(b, a % b);
  }
}

// Adding any integer multiple of the modulus leaves the remainder unchanged.
lemma ModAddMultiple(a: int, k: int, b: int)
  requires b != 0
  ensures (a + k * b) % b == a % b
  decreases if k >= 0 then k else -k
{
  if k > 0 {
    DivMod.DivModAdd1(a + (k - 1) * b, b);
    assert a + (k - 1) * b + b == a + k * b;
    ModAddMultiple(a, k - 1, b);
  } else if k < 0 {
    DivMod.DivModSub1(a + (k + 1) * b, b);
    assert a + (k + 1) * b - b == a + k * b;
    ModAddMultiple(a, k + 1, b);
  }
}

lemma AddMod(a: int, b: int, c: int)
  requires c != 0
  ensures (a + b) % c == (a % c + b % c) % c
{
  var ra, rb := a % c, b % c;
  assert a + b == (ra + rb) + (a / c + b / c) * c;
  ModAddMultiple(ra + rb, a / c + b / c, c);
}

lemma MulMod(a: int, b: int, c: int)
  requires c != 0
  ensures (a * b) % c == (a % c) * (b % c) % c
{
  var qa, ra := a / c, a % c;
  var qb, rb := b / c, b % c;
  assert a == qa * c + ra && b == qb * c + rb;
  var k := qa * qb * c + qa * rb + ra * qb;
  assert a * b == ra * rb + k * c by {
    assert (qa * c + ra) * (qb * c + rb)
        == qa * qb * c * c + qa * c * rb + ra * qb * c + ra * rb;
  }
  ModAddMultiple(ra * rb, k, c);
}

lemma GcdIsDivisor(a: int, b: int)
  ensures 0 < Gcd(a, b)
  ensures a % Gcd(a, b) == 0 && b % Gcd(a, b) == 0
  // ensures forall c :: c != 0 && a % c == 0 && b % c == 0 ==> Gcd(a, b) % c == 0
  decreases Abs(b)
{
  if b == 0 {
    reveal Gcd();
    if a != 0 {
      assert Gcd(a, 0) == Abs(a);
      if a > 0 {
        assert Abs(a) == a;
        assert a % a == 0;
      } else {
        assert a < 0;
        assert Abs(a) == -a;
        var x := -a;
        assert x > 0;
        assert a + x == 0;
        DivMod.DivModAdd1(a, x);
        assert (a + x) % x == a % x;
        assert (a + x) % x == 0 % x;
        assert a % x == 0;
        assert a % Abs(a) == 0;
      }
      assert 0 % Abs(a) == 0;
    }
  } else {
    assert Gcd(a, b) == Gcd(b, a % b) by {
      reveal Gcd();
    }
    GcdIsDivisor(b, a % b);
    assert b % Gcd(a, b) == 0;
    assert (a % b) % Gcd(a, b) == 0;
    calc {
      a % Gcd(a, b);
      (a / b * b + a % b) % Gcd(a, b);
      { AddMod(a / b * b, a % b, Gcd(a, b)); }
      (a / b * b % Gcd(a, b) + (a % b) % Gcd(a, b)) % Gcd(a, b);
      { MulMod(a / b, b, Gcd(a, b)); }
      (a / b % Gcd(a, b) * (b % Gcd(a, b)) % Gcd(a, b) + 0) % Gcd(a, b);
      (a / b % Gcd(a, b) * 0 % Gcd(a, b)) % Gcd(a, b);
      0;
    }
  }
}

// --- Divisibility helpers (d | x is written x % d == 0) ---

lemma DividesAbs(a: int, d: int)
  requires d != 0 && a % d == 0
  ensures Abs(a) % d == 0
{
  assert a == (a / d) * d;
  if a < 0 {
    assert -a == (-(a / d)) * d;
    ModAddMultiple(0, -(a / d), d);
  }
}

lemma DividesSub(a: int, b: int, d: int)
  requires d != 0 && a % d == 0 && b % d == 0
  ensures (a - b) % d == 0
{
  assert a == (a / d) * d && b == (b / d) * d;
  assert a - b == (a / d - b / d) * d;
  ModAddMultiple(0, a / d - b / d, d);
}

lemma DividesMulAny(q: int, b: int, d: int)
  requires d != 0 && b % d == 0
  ensures (q * b) % d == 0
{
  assert b == (b / d) * d;
  assert q * b == (q * (b / d)) * d;
  ModAddMultiple(0, q * (b / d), d);
}

lemma DividesModOp(a: int, b: int, d: int)
  requires d != 0 && b != 0 && a % d == 0 && b % d == 0
  ensures (a % b) % d == 0
{
  assert a % b == a - (a / b) * b;
  DividesMulAny(a / b, b, d);
  DividesSub(a, (a / b) * b, d);
}

// A positive number that divides a positive number cannot exceed it.
lemma DivideBound(x: int, y: int)
  requires x > 0 && y > 0 && x % y == 0
  ensures y <= x
{
  assert x == (x / y) * y;
  if x / y <= 0 {
    assert (x / y) * y <= 0;
  }
}

// Gcd is the GREATEST common divisor: every common divisor d divides it.
// (Excludes (0,0), where Gcd is defined as 1.)
lemma GcdGreatest(a: int, b: int, d: int)
  requires d != 0
  requires a % d == 0 && b % d == 0
  requires !(a == 0 && b == 0)
  ensures Gcd(a, b) % d == 0
  decreases Abs(b)
{
  reveal Gcd();
  if b == 0 {
    DividesAbs(a, d);
  } else {
    DividesModOp(a, b, d);
    GcdGreatest(b, a % b, d);
  }
}

// Symmetry now follows: each of Gcd(a,b), Gcd(b,a) divides the other (both
// positive), so they are equal.
lemma GcdSym(a: int, b: int)
  ensures Gcd(a, b) == Gcd(b, a)
{
  GcdPos(a, b);
  GcdPos(b, a);
  if !(a == 0 && b == 0) {
    GcdIsDivisor(a, b);
    GcdIsDivisor(b, a);
    GcdGreatest(b, a, Gcd(a, b));
    GcdGreatest(a, b, Gcd(b, a));
    DivideBound(Gcd(a, b), Gcd(b, a));
    DivideBound(Gcd(b, a), Gcd(a, b));
  }
}
