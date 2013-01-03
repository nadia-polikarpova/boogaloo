var m: [int] int;
var x: int;

procedure p1() returns ()
  modifies x;
{
  var m: [int] int;
  havoc m;
  call p2();
  x := m[5];
}

procedure p2() returns ()
{
  var m: [int] int;
  havoc m;
}

procedure Test() returns ()
  modifies x, m;
{
  havoc m;
  assume (forall i: int :: 0 <= i && i < 5 ==> m[i] == i);
  call p1();
  assert m[4] == 4;
}