var x, y: int;
var m, n: [int] int;

procedure p() returns ()
  modifies x, m;
{
  assume m[0] == 2;
  havoc m;
  havoc m;
  x := old(m[0]);
  assert x == 2;
}

procedure q() returns ()
  modifies y, n;
{
  havoc n;
  y := old(n[0]);
  assert y == 6;
}

procedure Test() returns ()
  modifies x, y, m, n;
{
  call p();
  
  assume n[0] == 5;
  havoc n;
  assume n[0] == 6;
  call q();
  
  x := old(m[0]);
  assert x == 2;
  
  y := old(n[0]);
  assert y == 5;
}