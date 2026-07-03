module Random {
  method random(a: int, b: int) returns (r: int)
    // Deterministic representative of bounded choice for this experiment.
    requires a <= b
    ensures a <= r <= b
  {
    r := a;
  }
}

method rand(n: int) returns (r: int)
  // Deterministic representative of bounded choice for this experiment.
  requires 0 <= n
  ensures 0 <= r <= n
{
  r := 0;
}

method rand2(n: int) returns (r: int)
  // Same bounded contract as rand, with a different deterministic body.
  requires 0 <= n
  ensures 0 <= r <= n
{
  r := n;
}

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

  r1 := rand2(y);
  r2 := rand2(y);

  assert r1 <= 4 && r2 <= 4;
}