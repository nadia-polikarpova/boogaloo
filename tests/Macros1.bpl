function p (a: [int] int, N, x: int) returns (bool)
{ (forall i: int :: 0 <= i && i < N ==> a[i] <= x) }

// if p is plainly substituted as a macro, the bound variable can get captured, then the assertions below fail
function all_p (a: [int] int, N: int) returns (bool)
{ ( forall i: int :: 0 <= i && i < N ==> p(a, N, a[i]) ) }

procedure Test()
{
  var a: [int] int;
  assume all_p(a, 3);
  assert a[0] == a[1];
  assert a[1] == a[2];
}