\\ lattice_export.gp: integer data of the lattice layer at v for the Lean files of M4,
\\ from the certified outputs code/earlier-computations/data/lattice_twist<k>.bin (lattice_cert.gp) and rho_k<k>.bin (selmer_image_v.gp).
\\ Coordinates: V = Q_2^6 on (1, pi, pi^2) twice; a ball [c, m] of K_v has coordinate i (0, 1, 2) known modulo
\\ 2^ceil((m - i)/3), so modulo 2^floor(m/3) for all three.
\\ Writes data/lattice_int_twist<k>.gp (GP readable) with, for twist k:
\\   q[i]    precision (2-adic, V coordinates) of the ball centre l[i] of log D_i (i = 1..7), log phi_a (8), log phi_b (9)
\\   l[i]    the centre reduced to integers in [0, 2^q[i])
\\   H, G    Lambda = H Z_2^6 (HNF of p21_45), G = 4 H^-1 (integer), H G = G H = 4 I
\\   C       Nakayama certificate: C * L == 4 I mod 8 (L = matrix with columns l[1..7])
\\   Cp      H == L * Cp mod 4 (columns of H in span(l_i) + 4 V)
\\   U       6 x 6 integer, det odd, rows 1, 2 the saturation block N, rows 3..6 the block O, entries in [0, 2^J0)
\\   Ut, D   adjugate of U, D = det U (odd): U * Ut = D I
\\   Q       rows 3..6 of U * G (4 x 6), P rows 1, 2 of U * G
\\   Jab     least 2-valuation of the O block of U * G * l[8], U * G * l[9] (entries), Del = det of the N block (integer)
\\   r       the level of QChar: r = min(Jab, q8, q9) - v2(Del)
\\   sig     sigma_j = H * Ut * e_j (j = 1, 2) with certificates (e, a, b): 2^e sigma_j == a l[8] + b l[9] mod 2^(r + e + 2)
\\   SB, W   SB: a basis (7 x 4, entries 0/1) of the span of the columns of SelCoef mod 2 (sigma_v(Sel) in the D basis);
\\           W: the 16 vectors sum_j e_j sum_i SB[i, j] l[i], e in {0, 1}^4 (representatives of W = rho(sigma_v(Sel)))
\\ Run from code/covering: gp -q lattice_export.gp
default(parisizemax, 4 * 10^9); default(nbthreads, 1);
chq(c, msg) = if (!c, error("check failed: ", msg));
v2(c) = if (c == 0, oo, valuation(c, 2));
v2vec(v) = vecmin(apply(v2, Vec(v)));
PBV = variable(Pol(0));
\\ coordinates of a ball [c, m] of K_v: the centre is a polmod in the local field variable
ballco(b) = { my(L = lift(b[1]), m = b[2]); [vector(3, i, polcoef(L, i - 1)), floor(m / 3)]; }
vco(B) = { my(a = ballco(B[1]), c = ballco(B[2])); [concat(a[1], c[1]), min(a[2], c[2])]; }
red(c, q) = { chq(denominator(c) % 2 == 1, "2-integral centre"); lift(Mod(numerator(c), 2^q) / denominator(c)); }
run(k) = {
  my(Lt = read(Str("../earlier-computations/data/lattice_twist", k, ".bin")), lg = mapget(Lt, "logs"), H = mapget(Lt, "H"), S = read(Str("../earlier-computations/data/selmer_image_v_twist", k, ".bin")),
     SC = S[2], q = vector(9), l = vector(9), G, L, C, Cp, U0, U, Ut, D, Q, P, Jab, Del, r, sig, W, fn = Str("data/lattice_int_twist", k, ".gp"), J0);
  chq(#lg == 9, "nine logarithms");
  \\ the variable of the local field
  for (i = 1, 9, my(v = vco(lg[i])); q[i] = v[2]; l[i] = vector(6, j, red(v[1][j], q[i]))~);
  G = 4 * H^-1; chq(denominator(G) == 1, "G integral"); chq(H * G == 4 * matid(6) && G * H == 4 * matid(6), "H G = G H = 4 I");
  L = Mat(vector(7, i, l[i]));
  chq(vecmin(q[1 .. 7]) >= 3, "log D_i known modulo 8 V");
  C = matrix(6, 7); for (j = 1, 6, my(e = vector(6, i, 4 * (i == j))~, s = matsolvemod(L, 8, e)); chq(type(s) == "t_COL", "Nakayama certificate solvable"); for (i = 1, 7, C[j, i] = lift(Mod(s[i], 8))));
  chq((L * C~ - 4 * matid(6)) % 8 == 0, "C: L C^T = 4 I mod 8");
  Cp = matrix(7, 6); for (j = 1, 6, my(s = matsolvemod(L, 4, H[, j])); chq(type(s) == "t_COL", "H in span(l) + 4V"); for (i = 1, 7, Cp[i, j] = lift(Mod(s[i], 4))));
  chq((L * Cp - H) % 4 == 0, "Cp");
  for (i = 1, 7, chq((G * l[i]) % 4 == 0, "G l_i = 0 mod 4"));
  \\ Lambda coordinates of the approximations of log phi_a, log phi_b
  my(ya = G * l[8] / 4, yb = G * l[9] / 4, Y, sn, U1, nzr, orow);
  chq(denominator(ya) == 1 && denominator(yb) == 1, "phi_a, phi_b approximations in Lambda");
  J0 = min(q[8], q[9]) - 2;
  Y = matconcat([ya, yb]); sn = matsnf(Y, 1); U1 = sn[1];
  nzr = [i | i <- [1 .. 6], (sn[3])[i, ] != 0]; orow = [i | i <- [1 .. 6], (sn[3])[i, ] == 0];
  chq(#nzr == 2, "rank 2");
  U = matconcat([U1[nzr[1], ]; U1[nzr[2], ]; U1[orow[1], ]; U1[orow[2], ]; U1[orow[3], ]; U1[orow[4], ]]);
  U = apply(e -> lift(Mod(e, 2^J0)), U);
  D = matdet(U); chq(D % 2 == 1, "det U odd"); Ut = matadjoint(U); chq(U * Ut == D * matid(6), "adjugate");
  my(UG = U * G); P = matconcat([UG[1, ]; UG[2, ]]); Q = matconcat([UG[3, ]; UG[4, ]; UG[5, ]; UG[6, ]]);
  my(Pa = P * l[8], Pb = P * l[9], Qa = Q * l[8], Qb = Q * l[9]);
  Jab = min(v2vec(Qa), v2vec(Qb));
  Del = Pa[1] * Pb[2] - Pa[2] * Pb[1];
  my(qab = min(q[8], q[9]), dl = v2(Del)); chq(dl < qab, "det of the N block within the precision");
  r = min(Jab, qab) - dl;
  chq(r >= 12, "r large enough for every nu + 1 used (nu <= 9, tails)");
  \\ saturation certificates for sigma_j = H Ut e_j, j = 1, 2 (rows N)
  sig = vector(2, j, my(s = H * Ut[, j], best = 0);
    for (e = 0, 8, if (best == 0, my(M = 2^(r + e + 2), so = matsolvemod(matconcat([l[8], l[9]]), M, 2^e * s));
      if (type(so) == "t_COL", best = [e, lift(Mod(so[1], M)), lift(Mod(so[2], M))])));
    chq(best != 0, "saturation certificate"); chq((2^best[1] * s - best[2] * l[8] - best[3] * l[9]) % 2^(r + best[1] + 2) == 0, "sigma certificate");
    chq(qab >= r + best[1] + 2, "precision of phi_a, phi_b covers the sigma certificate");
    [s, best]);
  \\ W: 16 combinations of the Selmer generators (columns of SC, coefficients on D_1..D_7)
  my(SB = lift(matimage(Mod(SC, 2)))); chq(matsize(SB) == [7, 4], "sigma_v(Sel) has dimension 4 in the D basis");
  my(gw = vector(4, j, sum(i = 1, 7, SB[i, j] * l[i])));
  W = vector(16, m, my(b = binary(m - 1 + 16)[2 .. 5]); sum(j = 1, 4, b[j] * gw[j]));
  \\ consistency with p21_45: dim pr(W) = 1 in the classes Q w / 4 mod 2
  my(cls = matconcat(vector(16, m, (Q * W[m] / 4) % 2))); chq(matrank(Mod(cls, 2)) == 1, "dim pr(W) = 1");
  system(Str("rm -f ", fn));
  write(fn, "q = ", q, ";"); write(fn, "l = ", l, ";"); write(fn, "H = ", H, ";"); write(fn, "G = ", G, ";");
  write(fn, "C = ", C, ";"); write(fn, "Cp = ", Cp, ";"); write(fn, "U = ", U, ";"); write(fn, "Ut = ", Ut, ";"); write(fn, "D = ", D, ";");
  write(fn, "P = ", P, ";"); write(fn, "Q = ", Q, ";"); write(fn, "Jab = ", Jab, ";"); write(fn, "Del = ", Del, ";"); write(fn, "r = ", r, ";");
  write(fn, "sig = ", sig, ";"); write(fn, "W = ", W, ";"); write(fn, "SB = ", SB, ";");
  printf("k = %d: q = %s, Jab = %d, v2(Del) = %d, r = %d, sigma certificates e = %s, dim pr(W) = 1; wrote %s\n", k, q, Jab, v2(Del), r, [sig[1][2][1], sig[2][2][1]], fn);
}
run(0); run(1);
quit;
