$exp = 1;


expr F = r((1 + 3*x1 + 5*x2 + 7*x3 + 9*x4 + 11*x5 + 13*x6 + 15*x7)^$exp - 1,
            (1 - 3*x1 - 5*x2 - 7*x3 + 9*x4 - 11*x5 - 13*x6 + 15*x7)^$exp + 1,
            (1 + 3*x1 + 5*x2 + 7*x3 + 9*x4 + 11*x5 + 13*x6 - 15*x7)^$exp + 3);


{
    id r(x1?,x2?,x3?) = r(x1?,x2?,x3?); // trigger the substitution of dollar variable
    expand;
}
{
    id r(x1?,x2?,x3?) = r(x1?*x3?,x2?*x3?);
    expand;    
}
{
    id r(x1?,x2?) = gcd_(x1?,x2?);
}