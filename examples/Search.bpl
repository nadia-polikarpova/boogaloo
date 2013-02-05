// Example inspired by: "Getting Started with Dafny: A Guide" by Jason Koenig and K. Rustan M. Leino

// Run "boogaloo Search.bpl" to invoke Main
// Run "boogaloo test -p LinearSearch -p BinarySearch Search.bpl" to test both search procedures exhaustively within the default range of inputs
// Run "boogaloo rtest -p LinearSearch -p BinarySearch Search.bpl" to test both search procedures on a default number of random inputs

// Search for x in an array a of length N.
procedure LinearSearch<T> (a: [int] T, N: int, key: T) returns (index: int)
  requires 0 <= N;
  ensures 0 <= index && index <= N;
  ensures index < N ==> a[index] == key; // If index is within bounds, key was found
  ensures index == N ==> (forall j: int :: 0 <= j && j < N ==> a[j] != key);  // If index is out of bounds, key does not occur
{
  index := 0;
  while (index < N)
    invariant index <= N;
    invariant (forall j: int :: 0 <= j && j < index ==> a[j] != key);
  {
    if (a[index] == key) { return; }
    index := index + 1;
  }
}

// Is array a of length N sorted?
function sorted(a: [int] int, N: int): bool
{ (forall j, k: int :: 0 <= j && j < k && k < N ==> a[j] <= a[k]) }

// Efficiently search for x in a sorted array a of length N.
// The pre- and postconditions are the same as for LinearSearch, except for the precondition sorted(a).
procedure BinarySearch(a: [int] int, N: int, key: int) returns (index: int)
  requires N >= 0;
  requires sorted(a, N);
  ensures 0 <= index && index <= N;
  ensures index < N ==> a[index] == key; // If index is within bounds, key was found
  ensures index == N ==> (forall j: int :: 0 <= j && j < N ==> a[j] != key);  // If index is out of bounds, key does not occur
{
  var low, high, mid: int;
  low, high := 0, N;
  while (low < high)
    invariant 0 <= low && low <= high && high <= N;
    invariant (forall i: int :: 0 <= i && i < N && !(low <= i && i < high) ==> a[i] != key);
  {
    mid := (low + high) div 2;
    if (a[mid] < key) {
      low := mid + 1;
    } else if (key < a[mid]) {
      high := mid;
    } else {
      index := mid;
      return;
    }
  }
  index := N;
}

// Global variable for the array and results
const N: int;
const array: [int] int;

axiom N == 3;
axiom sorted(array, N);

// One way to call LinearSearch and BinarySearch
procedure Main(value: int) returns (b, l: int)
{
  assume (forall i, j: int :: 0 <= i && i < j && j < N ==> array[i] != array[j]);
  assume (exists i: int :: 0 <= i && i < N ==> array[i] == value);
  call l := LinearSearch(array, N, value);
  call b := BinarySearch(array, N, value);
  assert b == l;
}
