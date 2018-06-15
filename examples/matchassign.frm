expr F = f(x,1,2,3);

$a = 0;
$b = 0;
apply {
    matchassign f(y?,?b) {
        $a = 2*y?*f(?b);
        $b = y?^5;
    }
}
print $a,$b;
