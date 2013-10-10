// Example inspired by: 1st Verified Software Competition (https://sites.google.com/a/vscomp.org), problem I

// Run "boogaloo SumMax.bpl" to invoke Main
// Run "boogaloo test -p SumMax SumMax.bpl" to find failing executions

// Sum of N elements of array a
function rec_sum(a: [int] int, N: int) returns (int)
{ if N == 0 then 0 else rec_sum(a, N - 1) + a[N - 1] }

// Iteratively compute the sum and maximum of array elements.
// Note that the existence of max in the array cannot be easily proven by Boogie. 
procedure SumMax(a: [int] int, N: int) returns (sum: int, max: int)
	requires 0 < N; // The array is non-empty
	ensures sum <= N * max; // A property of sum and max
	ensures (forall i: int :: 0 <= i && i < N ==> max >= a[i]); // max is greater or equal than all array elements
	ensures (exists i: int :: 0 <= i && i < N && max == a[i]); // max is present in the array
  ensures rec_sum(a, N) == sum; // sum is the same as the recursively defined sum
{
	var i: int;
	sum, max, i := a[0], a[0], 1;
  // Uncomment the following line to test an erroneous implementation:
  // sum, max, i := 0, 0, 0;
	while (i < N)
		invariant sum <= i*max;
		invariant i <= N;
		invariant (forall j: int :: 0 <= j && j < i ==> max >= a[j]);
    invariant (exists j: int :: 0 <= j && j < i && max == a[j]);
    invariant rec_sum(a, i) == sum;
	{
		if (max < a[i]) {
			max := a[i];
		}
		sum := sum + a[i];
		i := i + 1;
	}
}

// Global variables for the array and the results
var array: [int] int;
var s, m: int;

// One way to call SumMax
procedure Main() returns ()
	modifies array, s, m;
{
	array[0] := 10;
	array[1] := -3;
	array[2] := 1;
	array[3] := 5;
	call s, m := SumMax(array, 4);
}