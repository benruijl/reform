// workaround for an inefficiency
attrib $a = nonlocal;
attrib $b = nonlocal;
attrib $g = nonlocal;
attrib $ag = nonlocal;
attrib $bg = nonlocal;

$exp = 6;


$a = (1 + 3*x1 + 5*x2 + 7*x3 + 9*x4 + 11*x5 + 13*x6 + 15*x7)^$exp - 1;
$b = (1 - 3*x1 - 5*x2 - 7*x3 + 9*x4 - 11*x5 - 13*x6 + 15*x7)^$exp + 1;
$g = (1 + 3*x1 + 5*x2 + 7*x3 + 9*x4 + 11*x5 + 13*x6 - 15*x7)^$exp + 3;

inside $a,$b,$g {
    expand;
}

$ag = $a * $g;
$bg = $b * $g;

// workaround for inefficiency with dollar copying
$a = 0;
$b = 0;

inside $ag,$bg {
    expand;
}

$r = gcd_($ag, $bg) - $g;

// work around an inefficiency
$ag = 0;
$bg = 0;
$g = 0;

inside $r {
    expand;
}
print $r; // should yield 0