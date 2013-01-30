const N: int;
axiom N > 0;

const A, B: int;
axiom A + B == 5;

const m: [int] int;

axiom (forall i: int :: m[i] > 0);

procedure Test() returns ()
{
  assert N > 0;
  
  assert A + B == 5;
  
  assert m[5] > 0 && m[100] > 0 && m[5000] > 0;
}