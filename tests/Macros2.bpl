var seq: [int] int;
var count, N: int;

function sorted(a: [int] int, l, h: int): bool
{ (forall i, j: int :: l <= i && i < j && j < h ==> a[i] <= a[j]) }

function all_leq(a: [int] int, l, h, x: int): bool
{ (forall i: int :: l <= i && i < h ==> a[i] <= x) }

procedure MergeSort(low, high: int)
  requires 0 <= low && low <= high && high <= count;
  modifies seq;
  ensures sorted(seq, low, high);
  ensures (forall i: int :: i < low || high <= i ==> seq[i] == old(seq[i]));  
{
  var mid: int;  
  var res, p: [int] int;
	if (high - low > 1) {
		mid := low + (high - low) div 2;
		call MergeSort (low, mid);
		call MergeSort (mid, high);
    call res := Merge (low, mid, high);
    call Subcopy(res, low, high);
  }  
}

procedure Merge(low, mid, high: int) returns (res: [int] int)
  requires 0 <= low && low < mid && mid < high && high <= count;
  requires sorted(seq, low, mid);
  requires sorted(seq, mid, high);
  ensures sorted(res, low, high);
{
  var i, j, k: int;
  i, j, k := low, mid, low;
  while (k < high)
    invariant low <= i && i <= mid;
    invariant mid <= j && j <= high;
    invariant low <= k && k <= high;
    invariant i + j == k + mid;
    invariant sorted(res, low, k);
    invariant i < mid ==> all_leq(res, low, k, seq[i]); // This invariant used to fail because all_leq has a nested variable called `i'
    invariant j < high ==> all_leq(res, low, k, seq[j]);
  {
    if (i >= mid || (j < high && seq[i] > seq[j])) {
      res[k] := seq[j];
      j := j + 1;    
    } else {
      res[k] := seq[i];
      i := i + 1;
    }
    k := k + 1;
  }  
}

procedure Subcopy(a: [int] int, low, high: int)
  requires 0 <= low && low <= high && high <= count;
  modifies seq;
  ensures (forall i: int :: low <= i && i < high ==> seq[i] == a[i]);  
  ensures (forall i: int :: i < low || high <= i ==> seq[i] == old(seq[i]));
{
  var k: int;
  k := low;
  while (k < high)
    invariant low <= k && k <= high;
    invariant (forall i: int :: low <= i && i < k ==> seq[i] == a[i]);
    invariant (forall i: int :: i < low || high <= i ==> seq[i] == old(seq[i]));
  {
    seq[k] := a[k];
    k := k + 1;
  }
}

procedure Test()
  modifies seq;
{
  assume count == 3;
  assume !sorted(seq, 0, count);
  call MergeSort(0, count);
}  