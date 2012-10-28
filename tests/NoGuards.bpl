function fact(int): int;
axiom fact(0) == 1;
axiom (forall n: int :: {fact(n)}  1 <= n ==> fact(n) == n * factaux(n-1));

// The interpreter used to crash if a function definition extracted from an axiom has no guards
function factaux(int): int;
axiom (forall n: int :: {fact(n)} factaux(n) == fact(n));

procedure Test() returns ()
{
  var x: int;
  x := fact(5);
  assert x == 120;
}