var a, b, x, y: int;

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
  modifies a, b, x, y;
{
  assume a == 5;
  havoc a;
  b := old(a);
  assert b == 5; 
  
  call q();
  y := old(x);
  assert y == 2;  
}