var x, y: int;

procedure Test() returns ()
  modifies x, y;
{
  assume x == 5;
  havoc x;
  y := old(x);
  assert y == 5; 
}