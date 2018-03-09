(* Compute the trace of 14 Dirac gamma matrices. *)
tracen[expr_] := Module[{expr1, g1, g2},
  expr1 = expr /. g[a___] -> g1[] * g2[a];
  expr1 = FixedPoint[(
    # //. g1[a___] * g2[m1_, m2_, b___] -> d[m1, m2] * g1[] * g2[a, b] -
      g1[a, m2] * g2[m1, b] /. g2[m1_] -> 0 // Expand
  )&, expr1];
  expr1 = expr1 /. g1[] * g2[] -> 4;
  expr1
];
F = g[m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14];
tracen[F] // Length // Timing // Print;
