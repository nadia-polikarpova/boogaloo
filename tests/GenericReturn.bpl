function f<T>(): [int] T;

function g<T>(): T;

function h<T>(): <U>[T] U; 

function j<T, U>(): [T] U;

type Set T;
function emptySet<T>(): Set T;

procedure P() returns()
{
  var m1: [int] bool;
  var m2: [int] int;
  var m3: <a>[int] a;
  var m4: <a>[int] (Set a);
  var x: int;
  var y: bool;
  var s: Set int;
  
  x := f()[5];
  y := f()[5];
  s := emptySet();
  x := emptySet(); // Error: cannot match Set T against int
  
  m1 := f()[5 := true];
  m2 := f()[5 := true]; // Error: cannot match [int] int against [int] bool
  
  x := g();
  x := g()[5];
  m1 := g()[5 := true];
  m2 := g()[5 := true]; // Error: cannot match [int] int against [int] bool
  
  m2 := h(); // Error: cannot match <U>[T]U against [int]int
  m3 := h(); // OK: T bound to int, U still universally quantified
  m2 := h()[5 := 5]; // Error: cannot match <U>[int]U against [int]int
  m3 := h()[5 := 5]; // OK: despite the update, the type of rhs is still <U>[int]U
  
  m1 := j();
  m2 := j();
  m3 := j(); // Error: cannot match [T]U against <a>[int]a
  x := j()[5];
  y := j()[5];
  m1 := j()[5 := true];
  m2 := j()[5 := true]; // Error: cannot match [int]bool against [int]int
  
  m4 := m4[5 := emptySet()];
  m4 := m4[5 := true]; // Error: cannot match Set a against bool
}