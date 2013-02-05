// Original example from: https://boogie.codeplex.com/ Test/textbook
// This example demonstrates non-deterministic control flow and extraction of function definitions from axioms.

// A Boogie version of Turing's additive factorial program, from "Checking a large routine"
// published in the "Report of a Conference of High Speed Automatic Calculating Machines",
// pp. 67-69, 1949.

// Run "boogaloo -p ComputeFactorial -o n TuringFactorial.bpl" to observe n possible executions
// Run "boogaloo test -p ComputeFactorial TuringFactorial.bpl" to test ComputeFactorial exhaustively within the default range of inputs
// Run "boogaloo rtest -p ComputeFactorial TuringFactorial.bpl" to test ComputeFactorial on a default number of random inputs

procedure ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
{
  var r, v, s: int;
  r, u := 1, 1;
TOP:  // B
  assert r <= n;
  assert u == Factorial(r);
  v := u;
  if (n <= r) { return; }
  s := 1;
INNER:  // E
  assert s <= r;
  assert v == Factorial(r) && u == s * Factorial(r);
  u := u + v;
  s := s + 1;
  assert s - 1 <= r;
  if (s <= r) { goto INNER; }
  r := r + 1;
  goto TOP;
}

function Factorial(int): int;
axiom Factorial(0) == 1;
axiom (forall n: int :: {Factorial(n)}  1 <= n ==> Factorial(n) == n * Factorial(n-1));