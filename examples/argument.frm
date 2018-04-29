expr F = x*f(x, y, 2*x);

apply {
    argument f {
        id x = y + 5;
    }
    id y = 2;
}