function f(x: int): int
{ 5 }

procedure Test() returns ()
{
  assert f(1 div 0) == 5; // Expressions in Boogie are total, so this is not an error
}



