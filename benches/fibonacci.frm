#-
CF f;
S n;
L F = f(32);
repeat id f(n?{>=3}) = f(n-1) + f(n-2);
id f(1) = 1;
id f(2) = 1;
P;
.end
