#-

#ifndef `N'
  #define N "6"
#endif

S x1,...,x7;

#$exp = `N';

#$a = (1 + 3*x1 + 5*x2 + 7*x3 + 9*x4 + 11*x5 + 13*x6 + 15*x7)^$exp - 1;
#$b = (1 - 3*x1 - 5*x2 - 7*x3 + 9*x4 - 11*x5 - 13*x6 + 15*x7)^$exp + 1;
#$g = (1 + 3*x1 + 5*x2 + 7*x3 + 9*x4 + 11*x5 + 13*x6 - 15*x7)^$exp + 3;

#$ag = $a * $g;
#$bg = $b * $g;

#$r = gcd_($ag, $bg) - $g;

* should yield 0
#write "%$", $r
.end
