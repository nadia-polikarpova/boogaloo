procedure foo()
{
  var b:bool, i:int;

  b := if i then b else b; // Wrong condition type
  b := if b then b else i; // If- and else-part type mismatch
  b := if b then i else i; // Wrong lhs type
}
