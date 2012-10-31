var one: [int]int;
var two: [int, int]int;

procedure Good0(x: int, y: int)
  requires one[x] == two[x,y];
  modifies one, two;
{
  start:
    one[x] := two[x,y];
    two[x,y] := one[x];
    return;
}

procedure Bad0(x: int, y: int)
  requires one[x,y] == 7; // error: wrong selection types
  requires two[x] == 8; // error: wrong selection types
  modifies one, two;
{
}

var A: [int]bool;
var B: [bool, ref]int;

procedure Good1(x: int, b: bool, o: ref)
  requires A[x] && B[b,o] == 18;
  modifies A, B;
{
  start:
    A[x] := true;
    B[b,o] := 19;
    A[100] := false;
    B[false,null] := 70;
    return;
}

procedure Bad1(x: int, b: bool, o: ref)
  requires A[b]; // error: wrong selection type
  requires A[x] == 7; // error: wrong range type
  requires B[x,x] < 12; // error: wrong selection types
  requires B[b,b] == B[o,o]; // error: wrong selection types
  requires B[null,5]; // error: wrong selection types
  requires B[7,7] == A[7]; // error: wrong selection types
  modifies A, B;
{
}

var M: [ [int,int]bool, [name]name ]int;
var Q: [int,int][int]int;
var R: [int][int,int]int;

procedure Good2(k: [int,int]bool, l: [name]name) returns (n: int)
  modifies M, Q, R;
{
  var m: [ [int,int]bool, [name]name ]int;
  var p: [int,int]bool;
  var q: [int]int;
  var qq: [int,int][int]int;
  var r: [int,int]int;

  start:
    n := M[k,l];
    m := M;
    p := k;
    p[5,8] := true;
    m[p,l] := 13;
    M := m;
    goto next;

  next:
    qq := Q;
    q := Q[13,21];
    n := n + Q[34,55][89];
    R[1] := R[2];
    n := n + R[1][2,3];
    Q[144,233] := q;
    goto deepUpdate;

  deepUpdate:
    // To effectively do:
    //     Q[5,8][13] := 21;
    // do:
    q := Q[5,8];
    q[13] := 21;
    Q[5,8] := q;
    return;
}

const Sven: name;
const Mia: name;
const Tryggve: name;
const Gunnel: name;

procedure Bad2(k: [int,int]bool, l: [name]name) returns (n: int)
  modifies M, Q, R;
{
  var m: [ [int,int]bool, [name]name ]int;
  var p: [int,int]bool;
  var q: [int]int;
  var qq: [int,int][int]int;
  var qqx: [int,int][name]int;

  start:
    n := M[Sven,l]; // error: wrong selection types
    m := p; // error: wrong lhs type
    p := l[Mia]; // error: wrong lhs type
    p[5,8] := Tryggve; // error: wrong lhs type
    m[p,Gunnel] := 13; // error: wrong selection types
    M := qq; // error: wrong lhs type
    goto next;

  next:
    qq := Q;  // okay
    q := Q[13]; // error: wrong selection types
    n := n - Q[89][34,55]; // error: wrong selection types
    Q[true,233] := q; // error: wrong selection types
    qqx := qq; // error: wrong lhs type
    Q := qqx; // error: wrong lhs type
    qqx := qqx;  // okay
    Q := Q;  // okay
    n := n + Q[34,55][144,169]; // error: wrong selection types
    R[1,2] := 0; // error: wrong selection types
    R[1] := R[2,3]; // error: wrong selection types
    n := n + R[1][2]; // error: wrong selection types
    n := n + R[1,2]; // error: wrong selection types
    return;
}

type MyType;
var S0: bool;
var S1: [ref]bool;
var S2: [ref,int]bool;
var S3: [[ref,int]bool,MyType]MyType;
var S4: <a>[int,a]bool;
var S5: [int,int]bool;
var S6: [any,any]bool;
var S7: [int,any]any;
var S8: [any]bool;

function Sf(any) returns (bool);

procedure SubtypesGood(a: any)
  modifies S0;
{
  var t: MyType;
  var b: bool;

  start:
    S0 := S1[null];  // bool := bool
    S0 := S2[null,0];  // bool := bool
    t := S3[S2,t];
    goto next;
  next:
    b := S4[4,a];
    b := S4[5,null];  // any := ref
    b := S4[6,S4];  // any := [int,any]bool
    b := Sf(S5); // error: wrong argument type
    return;
}

procedure SubtypesBad()
  modifies S4,S5,S6;
  modifies S8;
{
  start:
    S4 := S4;
    S4 := S5;  // no
    S5 := S4;  // no
    S4 := S6;  // no
    S6 := S4;  // no
    S8 := S1;  // no
    return;
}

// ----------------------------------------------------

var ArrayA: [int]bool;
var ArrayB: <a>[a]bool;

procedure ArrayP(x: int, y: any)
  requires ArrayA[x];
  requires ArrayA[y];  // error
  requires ArrayB[x];
  requires ArrayB[y];
  modifies ArrayA, ArrayB;
{
}

// ----------------------------------------------------

procedure IntMethod(p: any) returns (r: int);
procedure AnyMethod(p: int) returns (r: any);

procedure IntMethodCaller()
{
  var x: any, y: int;
  entry:
    call x := AnyMethod(y);  // types are exact
    call x := IntMethod(y);  // error: type mismatch for out-parameter
    x := y; // error (is this supposed to work?)
    y := x;  // error: cannot assign any to int
    call y := IntMethod(x);  // types are exact
    call y := AnyMethod(x);  // type error on both in-parameter and out-parameter
    return;
}


type ref, any, name;
const null : ref;
