expr F = f(2);

for $i in 1..4 {
  print;
  apply {
    id f($i) = f($i+1);
  }
}