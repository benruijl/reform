expr F = 1;

$a = f(3);

inside $a {
    id f(x?) = f(x?+1);
}

apply {
    inside $a {
        id f(x?) = f(x?+1);
    }

    Multiply $a;
}

