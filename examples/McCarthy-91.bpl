// Original example from: https://boogie.codeplex.com/ Test/textbook

// Run "boogaloo -p F McCarthy-91.bpl" to observe a possible execution
// Run "boogaloo test -p F McCarthy-91.bpl" to test F exhaustively within the default range of inputs
// Run "boogaloo rtest -p F McCarthy-91.bpl" to test F on a default number of random inputs

// McCarthy 91 function
procedure F(n: int) returns (r: int)
  ensures 100 < n ==> r == n - 10;
  ensures n <= 100 ==> r == 91;
{
  if (100 < n) {
    r := n - 10;
  } else {
    call r := F(n + 11);
    call r := F(r);
  }
}
