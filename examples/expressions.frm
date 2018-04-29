expr F1 = x;
expr F2 = y;

apply m1 {
  id x = x + y;
}

apply {
  id y = y + 1;
}

apply m2 for F2 {
  id y = 3;
}

apply m3 exclude F2 {
  id x = 3;
}