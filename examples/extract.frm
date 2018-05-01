$a = x + x*y + x*y*z + y*z + x^2 + x^2*y + 2;
inside $a {
  extract x, y;
}
print $a;