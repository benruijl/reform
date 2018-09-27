proc derivative(x, n) {
  for $i in 1..(n+1) {
    id x^m? = m? * x^(m? - 1);
  }
}

expr F = u^5;

apply {
	call derivative(u, 2);
}