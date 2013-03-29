const x, y: int;
axiom x > y;

procedure p() returns ()
{
  var a: [int] int where (forall i: int :: a[i] > 2);
  var b: [int] int;
  b := a;
  assert b[1234567890] > 2;
}

var c: [int] int;

procedure q() returns (b: [int] int)
{
  var a: [int] int where (forall i: int :: a[i] >= i);
  assume a == b;
}

procedure Test() returns ()
  modifies c;
{
  var x: bool;
  assume y > 0; // Constraints for y should be executed in the global context, otherwise name x has wrong type. 
  
  call p();
  
  call c := q(); // c inherits a's constraint, even though a is out of scope
  assert c[5] >= 5;
}



