expr F1 = x;
expr F2 = y;

mod m1 {
  id x = x + y;
}

{
  id y = y + 1;
}

mod m2 for F2 {
  id y = 3;
}