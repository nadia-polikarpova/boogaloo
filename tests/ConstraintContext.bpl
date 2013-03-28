const x, y: int;
axiom x > y;

procedure p() returns ()
{
  var a: [int] int where (forall i: int :: a[i] > 2);
  var b: [int] int;
  b := a;
  assert b[1234567890] > 2;
}

procedure Test() returns ()
{
  var x: bool;
  assume y > 0; // Constraints for y should be executed in the global context, otherwise name x has wrong type. 
  
  call p();
}



