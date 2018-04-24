$a = x + x*y + y*z + x^2 + x^2*y + 2;
inside $a {
  extract x;
}
print $a;