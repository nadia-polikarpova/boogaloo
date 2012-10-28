function sorted(a: [int] int, N: int): bool
{ (forall i: int, j: int :: 0 <= i && i < j && j < N ==> a[i] <= a[j] )}

procedure Test() returns ()
{
  var array: [int] int;
  // The interpreter used to stop once it found an empty domain for j and not propagate it to i;
  // this check caused runtime failure (quantification over infinite domain)
  assert sorted(array, 0);
} 