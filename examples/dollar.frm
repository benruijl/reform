expr F = f(1)+f(2)+f(3);

$a = 3; // initialize $a
apply {
    maximum $a; // take the maximum of $a at this position for each term
    Multiply g($a);
    $a = $a + 1;
}
