var a, b, x, y, z: int;

procedure p() returns ()
  modifies x, y;
{
  assume old(x) == 2;
}

procedure q() returns ()
  modifies x, y;
{
  call p();
}

procedure Test() returns ()
  modifies a, b, x, y, z;
{
  var res: int;

  assume a == 5;
  havoc a;
  b := old(a);
  assert b == 5; 
  
  call q();
  y := old(x);
  assert y == 2;

  havoc z;
  assume old(old(z)) == 3;
  res := old(z);
  assert res == 3;  
}