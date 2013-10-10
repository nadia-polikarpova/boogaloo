// Example inspired by: 1st Verified Software Competition (https://sites.google.com/a/vscomp.org), problem II

// Run "boogaloo Invert.bpl" to invoke Main
// Run "boogaloo test -p Invert Invert.bpl" to find failing executions

// Returns the inverse of a permutation a of numbers [0..N).
// Note that as is the procedure cannot be verified by Boogie.
// The precondition is quite strong, so random testing is unlikely to generate valid inputs, while exhaustive testing does better in this case.
procedure Invert (a: [int] int, N: int) returns (b: [int] int)
	requires 0 < N;
	requires (forall i: int :: 0 <= i && i < N ==> 0 <= a[i] && a[i] < N);
	requires (forall i, j: int :: 0 <= i && i < j && j < N ==> a[i] != a[j]);
	
	ensures (forall i: int :: 0 <= i && i < N ==> b[a[i]] == i);
	ensures (forall i, j: int :: 0 <= i && i < j && j < N ==> b[i] != b[j]);
{
	var k: int;
	k := 0;
	while (k < N)
		invariant (forall i: int :: 0 <= i && i < k ==> b[a[i]] == i);
	{
		b[a[k]] := k;
		k := k + 1;
	}	
}

// Global variables for the initial and the reversed array
var array, array': [int] int;

// One way to call Invert
procedure Main() returns ()
  modifies array, array';
{
  array[0] := 2;
  array[1] := 0;
  array[2] := 3;
  array[3] := 1;
  call array' := Invert(array, 4);
}