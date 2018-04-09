expr F = 1;

$a = f(3);

inside $a;
    id f(x?) = f(x?+1);
endinside;

{
    inside $a;
        id f(x?) = f(x?+1);
    endinside;

    Multiply $a;
}

