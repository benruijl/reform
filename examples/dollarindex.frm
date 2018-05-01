for $i in 1..3 {
  $a[$i+x,2] = $i;
}

$b = $a[2+x,4] + f(x);

inside $b {
  id f(x?) = $a[1+x?,2];
  id $a[x?,?a,y?] = $a[x?,?a,y?-2];
}

print $b;