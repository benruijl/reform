expr F = 1;

attrib f = NonCommutative;

{
    Multiply f(2)*f(1)*f(3);

    id f(1)*f(2) = 5; // should not match
    id f(1) = f(2)*f(4);
}