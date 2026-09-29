\\ lattice_small_unimodular.gp: replace the projection data of data/lattice_int_twist<k>.gp by a small unimodular U (det = +-1, entries below
\\ 2^J0) built from the 2-adic saturation of <log phi_a, log phi_b> (approximations in Lambda coordinates), and recompute
\\ Q, P, Jab, Del, r and the saturation certificates. Writes data/lattice_unimodular_twist<k>.gp. Run from code/covering after
\\ lattice_export.gp: gp -q lattice_small_unimodular.gp
default(parisizemax, 2 * 10^9); default(nbthreads, 1);
chq(c, msg) = if (!c, error("check failed: ", msg));
v2(c) = if (c == 0, oo, valuation(c, 2));
v2vec(v) = vecmin(apply(v2, Vec(v)));
run(k) = {
  read(Str("data/lattice_int_twist", k, ".gp"));
  my(ya = G * l[8] / 4, yb = G * l[9] / 4, J0 = min(q[8], q[9]) - 2, Y, Sg, piv = 0, M, Mi, U, Ui, UG, Pm, Qm, Jab, Del, dl, r, sg, fn = Str("data/lattice_unimodular_twist", k, ".gp"), qab = min(q[8], q[9]));
  chq(denominator(ya) == 1 && denominator(yb) == 1, "in Lambda");
  Y = matconcat([ya, yb]);
  Sg = matrixqz(Y, -2); chq(matsize(Sg) == [6, 2], "saturation of rank 2");
  forsubset([6, 2], s, if (piv == 0 && matdet(vecextract(Sg, Vec(s), [1, 2])) % 2 != 0, piv = Vec(s)));
  chq(piv != 0, "a unit 2 x 2 minor of the saturation");
  M = vecextract(Sg, piv, [1, 2]); Mi = lift(Mod(1, 2^J0) * M^-1);
  my(orow = [i | i <- [1 .. 6], !setsearch(Set(piv), i)]);
  U = matrix(6, 6);
  U[1, piv[1]] = 1; U[2, piv[2]] = 1;
  for (t = 1, 4, my(o = orow[t], c = lift(Mod(Sg[o, ] * Mi, 2^J0))); U[2 + t, o] = 1; U[2 + t, piv[1]] = -c[1]; U[2 + t, piv[2]] = -c[2]);
  chq(abs(matdet(U)) == 1, "U unimodular"); Ui = U^-1; chq(denominator(Ui) == 1, "U^-1 integral");
  UG = U * G; Pm = UG[1 .. 2, ]; Qm = UG[3 .. 6, ];
  Jab = min(v2vec(Qm * l[8]), v2vec(Qm * l[9]));
  my(Pa = Pm * l[8], Pb = Pm * l[9]); Del = Pa[1] * Pb[2] - Pa[2] * Pb[1]; dl = v2(Del);
  chq(dl < qab, "det of the N block within the precision");
  my(J = min(Jab, qab)); r = J - dl; chq(dl <= J + 2 && r >= 12, "r");
  sg = vector(2, j, my(s = H * Ui[, j], best = 0);
    for (e = 0, 8, if (best == 0, my(Mo = 2^(r + e + 2), so = matsolvemod(matconcat([l[8], l[9]]), Mo, 2^e * s));
      if (type(so) == "t_COL", best = [e, lift(Mod(so[1], Mo)), lift(Mod(so[2], Mo))])));
    chq(best != 0, "saturation certificate"); chq((2^best[1] * s - best[2] * l[8] - best[3] * l[9]) % 2^(r + best[1] + 2) == 0, "sigma certificate");
    chq(qab >= r + best[1] + 2, "precision covers the sigma certificate");
    [s, best]);
  for (m = 1, 16, chq((Qm * W[m]) % 4 == 0, "Q w divisible by 4"));
  my(cls = matconcat(vector(16, m, (Qm * W[m] / 4) % 2))); chq(matrank(Mod(cls, 2)) == 1, "dim pr(W) = 1");
  system(Str("rm -f ", fn));
  write(fn, "U = ", U, ";"); write(fn, "Ui = ", Ui, ";"); write(fn, "UG = ", UG, ";"); write(fn, "Jab = ", Jab, ";");
  write(fn, "Del = ", Del, ";"); write(fn, "dl = ", dl, ";"); write(fn, "J = ", J, ";"); write(fn, "r = ", r, ";"); write(fn, "sg = ", sg, ";");
  printf("k = %d: pivot rows %s, max |U| = 2^%d, Jab = %d, v2(Del) = %d, J = %d, r = %d, sigma e = %s\n", k, piv, #binary(vecmax(apply(abs, concat(Vec(U))))), Jab, dl, J, r, [sg[1][2][1], sg[2][2][1]]);
}
run(0); run(1);
quit;
