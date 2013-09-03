var a, b, c: [int] int;
var m1, m2: [int] ([int] int);

procedure Test() returns ()
  modifies a, b, c, m1, m2;
{
  havoc a, b;
  assume a[2] == 2;
  assume b[2] == 3;
  assert a != b; // must be non-equal

  havoc a;
  b := a;
  assume a[0] >= 1;
  assume b[0] >= 2;
  assert a[0] == b[0]; // a and b store the same value
  assert a == b; // must be equal
  
  m2 := m1;
  m1[0] := a;
  m2[0] := b;
  assert m1 == m2;
  
  b[5] := 10;
  a[5] := 20;
  assume a[1] >= 1;
  assume b[1] >= 2;
  assert a[1] == b[1]; // still equal on the indexes that were not updated
  assert a != b; // must be non-equal
    
  c := b[10 := 100];
  assume a[2] >= 1;
  assume c[2] >= 2; 
  assert a[2] == c[2]; // c is indirectly derived from a
  assert a != c;
  
  a[5] := 10;
  assert a == b; // must be equal again
  
  m1[1] := a;
  m2[1] := b;
  // assert m1 == m2; // still works when values are maps // ToDo: loops with DFS
}