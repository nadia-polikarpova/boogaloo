// Original example from: https://boogie.codeplex.com/ Test/textbook
// This example demonstrates non-deterministic control flow.

// Run "boogaloo Find.bpl" to to invoke Main

// Declare a function 'f'
function f(x: int) returns (int)
{ x * x + 4 * x + 3 }

// This procedure will find a root of 'f'.  
// It will do that by recursively enlarging the range where no such domain value exists.
procedure Find(a: int, b: int) returns (k: int)
  requires a <= b;
  requires (forall j: int :: a < j && j < b ==> f(j) != 0);
  ensures f(k) == 0;
{
  goto A, B, C;  // nondeterministically choose one of these 3 goto targets

  A:
    assume f(a) == 0;  // assume we get here only if 'f' maps 'a' to 0
    k := a;
    return;

  B:
    assume f(b) == 0;  // assume we get here only if 'f' maps 'b' to 0
    k := b;
    return;

  C:
    assume f(a) != 0 && f(b) != 0;  // neither of the two above
    call k := Find(a-1, b+1);
    return;
}

var root: int;

// This procedure shows one way to call 'Find'
procedure Main() returns ()
  modifies root;
  ensures f(root) == 0;
{
  call root := Find(0, 0);
}
