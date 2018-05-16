#-
S x1,...,x7;

#$exp = 6;

#$a = (1 + 3*x1 + 5*x2 + 7*x3 + 9*x4 + 11*x5 + 13*x6 + 15*x7)^$exp - 1;
#$b = (1 - 3*x1 - 5*x2 - 7*x3 + 9*x4 - 11*x5 - 13*x6 + 15*x7)^$exp + 1;
#$g = (1 + 3*x1 + 5*x2 + 7*x3 + 9*x4 + 11*x5 + 13*x6 - 15*x7)^$exp + 3;

#$ag = $a * $g;
#$bg = $b * $g;

* check the results
#inside $ag, $bg
  #do i=1,7
    id x`i' = 1;
  #enddo
#endinside
#$r = $ag / $bg - 1857283155/203501;
* should yield 0
#write "%$", $r
.end
