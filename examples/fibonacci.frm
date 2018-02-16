/*
A benchmark to test the performance of term generation.
*/
IN = f(30);

{
    repeat id f(x?{>0}) = f(x? - 1) + f(x? - 2);
}
