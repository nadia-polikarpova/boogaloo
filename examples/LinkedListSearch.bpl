// Example inspired by: 1st Verified Software Competition (https://sites.google.com/a/vscomp.org), problem III

// Run "boogaloo LinkedListSearch.bpl" to observe a possible execution (use axioms and assumptions to constrain possible executions)

// Reference type
type ref;

// Null-reference
const null: ref;

// Maps a list node to the stored value  
const item: [ref] int;
// Maps a list node to the next node
const next: [ref] ref; 
// Indexes of node (to enforce acyclicity)
const index: [ref] int;
// Head node of the list
const head: ref;

// Is list starting at "node" acyclic?
function acyclic(node: ref): bool
{ node == null || (index[node] < index[next[node]] && acyclic(next[node])) }

// How many times "next" should be applied to reach "node'" starting from "node"?
function distance(node, node': ref): int
{ 
  if node == node'
    then 0
    else distance(next[node], node') + 1
}

// Distance from "node" to "null" 	
function length(node: ref): int
{ distance(node, null) }

// Value at distance "n" from "node"
function at(node: ref, n: int): int
{
  if n == 0
    then item[node]
    else at(next[node], n - 1)
}

// Returns the distance from "head" to the closest cell that contains 0 or (if there is no such cell) to "null"	
procedure search(v: int) returns (i: int)
  requires acyclic(head);
	ensures (forall j: int :: 0 <= j && j < i ==> at(head, j) != v);
	ensures (i < length(head)) ==> at(head, i) == v;
{
	var node: ref;
	i := 0;
	node := head;
 
	while (node != null && item[node] != v) 
		invariant (forall j: int :: 0 <= j && j < i ==> at(head, j) != v);
		invariant i == distance(head, node);
		invariant (node != null) ==> item[node] == at(head, i);
	{
    assert node != null;
		node := next[node];
		i := i + 1;
	}
}

const N: int;
axiom N == 3;

axiom acyclic(head);
axiom length(head) == N;
axiom (forall i, j: int :: 0 <= i && i < j && j < N ==> at(head, i) != at(head, j));

procedure Main() returns (result: int)
{
  call result := search(0);
}