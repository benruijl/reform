expr F = x;

attrib $a = nonlocal;

{
  $a = 2;
  id x = y + x;
  if (match(x))  $a = 5;
  Multiply f($a);

  // this will produce f(5)*x + (5)*y
}