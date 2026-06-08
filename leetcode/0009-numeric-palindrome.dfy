include "../lib/seq/Digits.dfy"
include "../lib/Seq.dfy"

import opened Seq
import opened DigitsModule

predicate NumericPalindrome(n: int)
  requires 0 <= n
{
  Digits(n, 10) == Reverse(Digits(n, 10))
}

// Helper: digits of a positive number split by leading division.
lemma DigitsSplitHi(a: int, base: int)
  requires 2 <= base
  requires 0 < a
  ensures Digits(a, base) == (if a < base then [] else Digits(a / base, base)) + [a % base]
{
  reveal Digits();
}

method ReverseNumber(n: int) returns (r: int)
  requires 0 <= n
  requires n == 0 || n % 10 != 0
  ensures Digits(r, 10) == Reverse(Digits(n, 10))
{
  r := 0;
  var x := n;
  ghost var b := 1;
  ghost var y := 0;
  assert Digits(r, 10) == Reverse(Digits(y, 10)) by {
    reveal Digits();
  }
  while x > 0
    invariant 0 <= r
    invariant 0 <= x
    invariant 1 <= b
    invariant x == n / b
    invariant y == n % b
    invariant r == 0 ==> x == n
    invariant n == 0 ==> r == 0
    invariant r > 0 ==> Digits(r, 10) + (if x > 0 then Reverse(Digits(x, 10)) else []) == Reverse(Digits(n, 10))
  {
    ghost var oldR := r;
    ghost var oldY := y;
    ghost var oldX := x;
    ghost var oldB := b;
    var d := x % 10;
    r := r * 10 + d;
    y := y + d * b;
    b := b * 10;

    // Discharge y == n % b.
    assert y == n % b by {
      assert oldY < oldB;
      assert 0 <= d <= 9;
      assert d * oldB + oldY < 10 * oldB;
      assert d * oldB + oldY >= 0;
      assert n == oldX * oldB + oldY;
      assert oldX == (oldX / 10) * 10 + d;
      assert n == (oldX / 10) * (10 * oldB) + (d * oldB + oldY);
      assert y == d * oldB + oldY;
      assert b == 10 * oldB;
      DivMod.DivModSpec(n, b, oldX / 10, y);
    }

    ghost var newX := oldX / 10;
    assert newX == n / b by {
      DivMod.DivModSpec(n, b, oldX / 10, y);
    }

    if oldR > 0 {
      assert Digits(r, 10) == Digits(oldR, 10) + [d] by {
        DigitsSplit(oldR, d, 10);
      }
    } else {
      assert oldX == n;
      assert n > 0;
      assert n % 10 != 0;
      assert d == n % 10;
      assert d > 0;
      assert r == d;
      assert Digits(r, 10) == [d] by {
        DigitsOne(r, 10);
      }
    }

    ghost var revOldX := Reverse(Digits(oldX, 10));
    ghost var revNewX := if newX > 0 then Reverse(Digits(newX, 10)) else [];
    assert oldX > 0;
    DigitsSplitHi(oldX, 10);
    if oldX < 10 {
      assert newX == 0;
      assert d == oldX;
      DigitsOne(oldX, 10);
      assert Digits(oldX, 10) == [d];
      calc {
        revOldX;
        Reverse(Digits(oldX, 10));
        Reverse([d]);
        Reverse([]) + [d];
        [] + [d];
        [d];
      }
      assert revNewX == [];
    } else {
      assert newX > 0;
      assert Digits(oldX, 10) == Digits(newX, 10) + [d];
      ReverseConcat(Digits(newX, 10), [d]);
      assert revOldX == [d] + Reverse(Digits(newX, 10));
      assert revNewX == Reverse(Digits(newX, 10));
      assert revOldX == [d] + revNewX;
    }

    if oldR > 0 {
      assert Digits(oldR, 10) + revOldX == Reverse(Digits(n, 10));
      if oldX < 10 {
        assert Digits(r, 10) == Digits(oldR, 10) + [d];
        assert Digits(oldR, 10) + [d] == Digits(oldR, 10) + revOldX;
        assert Digits(r, 10) + revNewX == Digits(r, 10);
      } else {
        assert Digits(r, 10) == Digits(oldR, 10) + [d];
        assert Digits(r, 10) + revNewX == Digits(oldR, 10) + [d] + revNewX;
        assert Digits(oldR, 10) + [d] + revNewX == Digits(oldR, 10) + revOldX;
      }
    } else {
      assert oldX == n;
      assert revOldX == Reverse(Digits(n, 10));
      if oldX < 10 {
        assert Digits(r, 10) == [d];
        assert Digits(r, 10) + revNewX == [d];
        assert [d] == revOldX;
      } else {
        assert Digits(r, 10) == [d];
        assert Digits(r, 10) + revNewX == [d] + revNewX;
        assert [d] + revNewX == revOldX;
      }
    }

    assert r > 0 by {
      if oldR > 0 {
      } else {
        assert d > 0;
      }
    }

    x := x / 10;
    assert x == newX;
  }

  if n == 0 {
    assert r == 0;
    reveal Digits();
  } else {
    assert r > 0 by {
    }
  }
}

method IsPalindrome(n: int) returns (r: bool)
  requires 0 <= n
  ensures r == true ==> NumericPalindrome(n)
{
  if n > 0 && n % 10 == 0 {
    return false;
  }
  var rev := ReverseNumber(n);
  r := (rev == n);
  if r {
    assert Digits(rev, 10) == Reverse(Digits(n, 10));
    assert rev == n;
    assert Digits(n, 10) == Reverse(Digits(n, 10));
  }
}
