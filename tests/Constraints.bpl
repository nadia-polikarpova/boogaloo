const N: int;
axiom N > 0;

const M: int;
axiom M == 5;

const A, B: int;
axiom A + B == 5;

const m: [int] int;

axiom (forall i: int :: (i > 0 ==> m[i] == i) && (i <= 0 ==> m[i] != 0));

procedure Test() returns ()
{
  assert N > 0;
  
  assert M == 5;
  
  assert A + B == 5;
  
  assert m[5] == 5 && m[5000] == 5000;
  assert m[-1] != 0 && m[-5000] != 0;
}