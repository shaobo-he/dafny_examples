module Random {
  method {:axiom} random(a: int, b: int) returns (r: int)
    // Bounded nondeterministic choice only. No distribution, independence, or
    // uniformity property is specified.
    requires a <= b
    ensures a <= r <= b
}

method {:axiom} rand(n: int) returns (r: int)
  // Bounded nondeterministic choice only, not a probabilistic random source.
  requires 0 <= n
  ensures 0 <= r <= n

method {:axiom} rand2(n: int) returns (r: int)
  // Same spec surface as rand: each call may return any value in range.
  requires 0 <= n
  ensures 0 <= r <= n

method Main()
{
  var x := 2;
  var y := 4;

  var r1 := Random.random(x, y);
  var r2 := Random.random(x, y);

  assert r1 <= 4 && r2 <= 4;

  r1 := rand(y);
  r2 := rand(y);

  assert r1 <= 4 && r2 <= 4;
  // Two calls to a nondeterministic method are intentionally not equal by specification.

  r1 := rand2(y);
  r2 := rand2(y);

  assert r1 <= 4 && r2 <= 4;
  // Wrong:
  //assert r1 == r2;
}
