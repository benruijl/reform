(* Compute the 32th number in the Fibonacci sequence in a stupid way. *)
fib[n_?(# >= 3 &)] := fib[n - 1] + fib[n - 2];
fib[1] = 1;
fib[2] = 1;

fib[32] // Timing // Print;
