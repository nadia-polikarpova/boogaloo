procedure foo()
{
  var a: [int,int]int;
  var b: [int]bool;
  var c: [int]int;
  a := (lambda y:int :: y + 1); // type mismatch
  b := (lambda y:int :: y + 1); // type mismatch
  c := (lambda y:int :: y + 1);
}

procedure bar()
{
  var a: [int]int;
  a := (lambda<T> y:int :: y + 1); // T must occur among argument types
}

procedure baz()
{
  var a: [bool]int;
  a := (lambda y:bool :: y + 1); // Wrong argument to +
}
