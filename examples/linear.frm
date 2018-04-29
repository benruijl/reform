expr F = f(x, y);

attrib f = Linear;

apply {
    id f(x1?,x2?) = f(x1?+2,x2?+5);
}