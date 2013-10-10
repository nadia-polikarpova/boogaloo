// This example is currently unsound due to a recursive function taking a map as argument (distance)

// Reference type
type ref;
// Null-reference
const null: ref;

// Linked-list representation
var Head: ref;
var Next: [ref] ref;
var Len: int;

/* Distance and length */

// How many times n should be applied to reach node' starting from node?
function distance(node, node': ref, next: [ref] ref): int
{ 
  if node == node'
    then 0
    else distance(next[node], node', next) + 1
}

// Distance from node to null 	
function length(node: ref, next: [ref] ref): int
{ distance(node, null, next) }

function reachable(node, node': ref, next: [ref] ref): bool
{ node == node' || (node != null && reachable(next[node], node', next)) }

function inv(head: ref, next: [ref] ref, len: int): bool
{ length(head, next) == len }

procedure Empty() returns ()
  modifies Head, Len;
  ensures inv(Head, Next, Len);
{
  Head := null;
  Len := 0;
}

procedure Cons() returns ()
  modifies Head, Next, Len;
  requires inv(Head, Next, Len);
  ensures inv(Head, Next, Len);
{
  var Head': ref;
  assume !reachable(Head, Head', Next);
  Next[Head'] := Head;
  Head := Head';
  Len := Len + 1;
  assume {: print length(Head, Next), distance(Head, null, Next), null, distance(Next[Head], null, Next), Next[Head], distance(null, null, Next) } true;
}  

