function f<a>(x: a, y: a) : bool
{ true }

procedure Proc<a>(z: a) returns (res: a)
{
  // The type checker used to accept this because of a clash in type variables names
  assert f(z, 5);
}