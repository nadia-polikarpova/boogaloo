var a, b, c, d: [int] int;
var m, n, p, q: [int] ([int] int);

procedure Test () returns ()
  modifies a, b, c, d, m, n, p, q;
{
  havoc a, b;
  assume a[2] == 2;
  assume a[5] == 5;
  assume a[10] == 10;
  assume b[5] == 6;
  assume b[20] == 20;
  c := a[2 := 200][5 := 500];
  d := b[3 := 300][5 := 500];  
  assume c == d;
  // c and d are now equal
  // a is equal to them, except 2 -> 2 and 5 -> 5
  // b is equal to them, except 5 -> 6 and 3 is still undefined
  
  assume b[3] == 3; // so here we are still free to choose b[3]
  
  assert a[2] == 2 && a[3] == 300 && a[5] == 5 && a[10] == 10 && a[20] == 20;
  assert b[2] == 200 && b[3] == 3 && b[5] == 6 && b[10] == 10 && b[20] == 20;
  assert c[2] == 200 && c[3] == 300 && c[5] == 500 && c[10] == 10 && c[20] == 20;
  assert d[2] == 200 && d[3] == 300 && d[5] == 500 && d[10] == 10 && d[20] == 20;
  
  // Maps holding maps:
  havoc a, b, c, d;
  havoc m, n, p, q;
  
  assume a[1] == 1;
  assume b[2] == 2;
  
  m[1] := a;
  n[2] := b;
  
  p := m[5 := c];
  q := n[5 := d];
  
  assume p == q;
  assert c == d;  
}