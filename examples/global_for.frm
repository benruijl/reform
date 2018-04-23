expr F = f(2);

for $i in 1..4;
  print;
  {
    id f($i) = f($i+1);
  }
endfor;