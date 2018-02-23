#-
CF g,g1,g2;
I m1,...,m14;
L F = g(m1,...,m14);
id g(?a) = g1()*g2(?a);
repeat;
  repeat id g1(?a)*g2(m1?,m2?,?b)
    = d_(m1,m2)*g1()*g2(?a,?b) - g1(?a,m2)*g2(m1,?b);
  id g2(m1?) = 0;
endrepeat;
id g1()*g2() = 4;

Format 120;
P +s;
.end
