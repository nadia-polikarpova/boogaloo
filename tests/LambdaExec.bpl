var a: [int] int;

procedure Test() returns ()
  modifies a;
{
  a := (lambda i: int :: i + 1);
  assert a[5] == 6;
  
  a := (lambda i: int :: i * i);
  assert a[5] == 25;
}



