/*
A benchmark to test the performance of term generation.
*/
expr F = f(30);

apply {
    repeat id f(x?{>0}) = f(x? - 1) + f(x? - 2);
}
