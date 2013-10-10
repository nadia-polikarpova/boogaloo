/*
  Power of a permutation.
  Original example from: Nikolai Kosmatov "All-Paths Test Generation for Programs with Internal Aliases"
  The particularity of this program is that the number of distinct paths is much lower than the number of inputs (which is factorial).
  
  Run "boogaloo -c=False -n 1 -o -1 PermPower.bpl" to enumerate all paths.
*/

const N: int;
axiom N == 5;

type Perm = [int]int;

procedure getOrder(p: Perm) returns (order: int)
  requires (forall i: int :: 0 <= i && i < N ==> 0 <= p[i] && p[i] < N);
  requires (forall i, j: int :: 0 <= i && i < j && j < N ==> p[i] != p[j]);
{
  var i: int;
  var isId: bool;
  var power, tmp: Perm;
  
  i := 0;
  while (i < N) {
    power[i] := p[i];
    i := i + 1;
  }
  
  order := 1;
  while (true) {
    i, isId := 0, true;
    while (i < N && isId) {
      if (power[i] != i) {
        isId := false;
      }
      i := i + 1;
    }
    if (isId) { return; }
    i := 0;
    while (i < N) {
      tmp[i] := power[i];
      i := i + 1;
    }    
    i := 0;
    while (i < N) {
      power[i] := tmp[p[i]];
      i := i + 1;
    }
    order := order + 1;
  }
}