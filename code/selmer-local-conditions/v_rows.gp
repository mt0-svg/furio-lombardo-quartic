\\ The bit rows of the frozen place-v data of VPlace.lean (VRows.lean): the rows C_v of stage 6 of
\\ selmer_rows_twist<k>_v.out and the columns beta_j of ../selmer-global-bound/selmer_space_new_generators.out, as natural numbers with bit s
\\ equal to entry s (s = 0..81). Run from this directory: gp -q v_rows.gp.

\\ the text after the last ": " of the first line of file f containing the string key (occurrence occ)
field(f, key, occ) = {
  my(L = readstr(f), n = 0, p);
  for (i = 1, #L,
    if (#strsplit(L[i], key) > 1, n++;
      if (n == occ, p = strsplit(L[i], ": "); return(p[#p]))));
  error("no line ", key, " in ", f);
}
tobits(M) = vector(matsize(M)[1], i, sum(s = 1, matsize(M)[2], M[i, s] * 2^(s - 1)));
lst(v) = {
  my(s = "[");
  for (i = 1, #v, s = Str(s, if (i > 1, ", ", ""), v[i]));
  Str(s, "]");
}
{
  my(C = vector(2), B = vector(2));
  for (k = 0, 1,
    C[k + 1] = eval(field(Str("selmer_rows_twist", k, "_v.out"), "C_w rows", 1));
    B[k + 1] = eval(field("../selmer-global-bound/selmer_space_new_generators.out", "beta_j (rows, 82 bits)", k + 1));
    if (matsize(C[k + 1]) != [11, 82] || matsize(B[k + 1]) != [4, 82], error("sizes"));
    printf("twist %d: C_v %s of rank %d, beta %s of rank %d\n", k, matsize(C[k + 1]),
      matrank(C[k + 1] * Mod(1, 2)), matsize(B[k + 1]), matrank(B[k + 1] * Mod(1, 2))));
  print("-- Lean data");
  print("def CvRows : Fin 2 → List ℕ :=");
  print("  ![", lst(tobits(C[1])), ",");
  print("    ", lst(tobits(C[2])), "]");
  print("def βRows : Fin 2 → List ℕ :=");
  print("  ![", lst(tobits(B[1])), ",");
  print("    ", lst(tobits(B[2])), "]");
}
