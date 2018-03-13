procedure derivative(x, n);
  for $i in 1..(n+1);
    id x^m? = m? * x^(m? - 1);
  endfor;
endprocedure;

expr F = u^5;

{
	call derivative(u, 2);
}