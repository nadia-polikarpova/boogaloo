## What is Boogaloo? ##

Boogaloo is an interpreter and run-time assertion checker for the [Boogie](http://boogie.codeplex.com/) intermediate verification language.
Usually Boogie programs do not get executed:
they are meant to be proven correct by the Boogie verifier.
When a verification attempt fails, however,
it is often hard to understand what went wrong. 
Is the specification inconsistent with the program or just incomplete?
On what inputs does the specification violation occur?

Boogaloo helps you understand failed verification attempts,
debug Boogie programs
and test translations from a source language into Boogie.
It can try out a number of program executions and check if the specification holds in those cases,
even if some loop invariants or intermediate assertions are missing.
If a specification violation occurs, Boogaloo produces a concrete failing test case,
which can help you figure out what the error is and how to fix it.

As an example, consider the following (erroneous) implementation of the Mc-Carthy 91 function:

```boogie
1:  procedure F(n: int) returns (r: int)
2:    ensures n <= 100 ==> r == 91;
3:  {
4:    if (100 <= n) {
5:      r := n - 10;
6:    } else {
7:      call r := F(n + 11);
8:      call r := F(r);
9:    }
10: }
```

The Boogie verifier can only [tell us](http://rise4fun.com/Boogie/OItH) that the postcondition might not hold.
If instead you test this program with Boogaloo, like so:

```
boogaloo test McCarthy-91.bpl
```

it will produce the following output:

```
Execution 0: F(100) failed
Postcondition "n <= 100 ==> r == 91" defined at McCarthy-91.bpl line 2 
violated at McCarthy-91.bpl line 1 with
    n -> 100
    r -> 90
in call to F
```

The failing test case hints us at the problem:
when `F` is invoked with `n = 100`, `r` comes out as 90 instead of 91.
We can fix this by changing the first line of the body into `if (100 < n) {`.
After this change verification [still fails](http://rise4fun.com/Boogie/qKF) but all the tests pass,
which indicates that the program is likely to be correct,
just missing some specification
(in this case, [the second postcondition clause](http://rise4fun.com/Boogie/McCarthy-91)).

To check out what else Boogaloo can do 
try it on sample Boogie programs from the <<file examples>> directory.

## Further Reading ##

* [User Manual](TODO): how to use and build Boogaloo
* [To Run What No One Has Run Before](https://cseweb.ucsd.edu/~npolikarpova/publications/rv13.pdf): our paper about Boogaloo at RV'13; read this if you want to learn what's under the hood.
