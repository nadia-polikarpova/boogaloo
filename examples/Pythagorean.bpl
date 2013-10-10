// Run "boogaloo -o n -m=False Pythagorean.bpl" to observe n possible executions without solution minimization

var x, y, z: int;

// Find a positive solution to x^2 + y^2 == z^2
procedure Main() returns ()
  modifies x, y, z;
{
  havoc x, y, z;
  assume x > 0;
  assume y > 0;
  assume z > 0;
  assume x*x + y*y == z*z;
}