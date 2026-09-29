\\ text_export.gp: text export of the data of the local group at v and of the covering, for an independent recomputation in another system.
\\ Writes /tmp/k21c/m9export/ (and a copy under code/earlier-computations/export when small): for each twist k,
\\   sextic_twist<k>.txt the sextic f_k(x) (coefficients in K21 = Q[b]/(K21), as PARI strings, lowest degree first)
\\   local_divisors_twist<k>.txt the 7 certified local divisors D_i = [u_i, v_i] at the place above 2 with e = 3 (refined)
\\   phi_known_twist<k>.txt phi(x_a), phi(x_b) = [u, v] (global, exact over K21) with the index i of x_i
\\   selmer_coords_twist<k>.txt SelCoef (7 x 19 over F_2: columns span sigma_v(Sel) in the basis D_1..D_7 of J(K_v)/2J(K_v)),
\\                     KnCoef (7 x 3: T, phi_a, phi_b in that basis)
\\   sample_points_twist<k>.txt sample points of C(Q_2): [disc, X, projective point, [u, v] of phi(x_P) (K21 approximations modulo
\\                     pr^240), index i of the nearby known point or -1, tau]
\\   tiny_integral_c1_twist<k>.txt the linear coefficients c_1 of the tiny integral at x_a, x_b
\\ plus field_and_place.txt: K21, the prime pr above 2 with e = 3 (idealprimedec index and generators), NM.
\\ Run from code/earlier-computations: gp -q text_export.gp
default(parisizemax, 5*10^9); default(nbthreads, 1);
NOQUIT = 1; JOBS = [];
read("leading_class_explore.gp");
OUT = "/tmp/k21c/m9export/";
system(Str("mkdir -p ", OUT));
wr(fn, s) = write(Str(OUT, fn), s);
{
  system(Str("rm -f ", OUT, "*.txt"));
  wr("field_and_place.txt", Str("K21 = ", K21, ";"));
  wr("field_and_place.txt", Str("prgen = ", [pr.p, nfbasistoalg(nfK, pr.gen[2])], ";  \\\\ pr = (2, prgen[2]), e = ", pr.e, ", f = ", pr.f));
  wr("field_and_place.txt", Str("NM = ", NM, ";"));
  my(pts = [[0, 5, X0, -1] | X0 <- [1, 3, 5, 7, 9, 11, 13, 15]], Pk = [[0, 0, 1], [1, 1, 1], [2, 0, 1], [-1, 0, 1]]);
  pts = concat(pts, concat([[0, 1, X0, 0] | X0 <- [2, 4, 8, 16, 6, 10]], [[0, 1, X0, 2] | X0 <- [3, 5, 9, 17]]));
  pts = concat(pts, concat([[1, 3, X0, 1] | X0 <- [4, 8, 12, 16]], [[1, 2, X0, 3] | X0 <- [1, 3, 5, 7, 11, 15]]));
  for (k = 0, 1,
    my(C = ctx(k), f = C[1], R = read(Str("local_images_twist", k, "_e3.bin")), S = read(Str(SEL, "rho_k", k, ".bin")), phis = [ph | ph <- PHI, ph[2] == k]);
    wr(Str("sextic_twist", k, ".txt"), Str("f = ", apply(c -> lift(c), Vec(Polrev(Vecrev(f)))), ";  \\\\ Vecrev: coefficient of x^0 first"));
    wr(Str("sextic_twist", k, ".txt"), Str("fvecrev = ", apply(c -> lift(c), Vecrev(f)), ";"));
    for (i = 1, #R[7], my(D = j2_refine(LV, f, [td2_Kx(nfK, R[7][i][1]), td2_Kx(nfK, R[7][i][2])]));
      wr(Str("local_divisors_twist", k, ".txt"), Str("D", i, " = [", apply(c -> lift(c), Vecrev(D[1])), ", ", apply(c -> lift(c), Vecrev(D[2])), "];")));
    for (j = 1, 2, my(Uu = subst(phis[j][4], t, 'x) * Mod(1, K21), Vv = subst(phis[j][5], t, 'x) * Mod(1, K21), uu = Uu / pollead(Uu), vv = Vv % uu);
      wr(Str("phi_known_twist", k, ".txt"), Str("phi", phis[j][1], " = [", apply(c -> lift(c), Vecrev(uu)), ", ", apply(c -> lift(c), Vecrev(vv)), "];")));
    wr(Str("selmer_coords_twist", k, ".txt"), Str("SelCoef = ", S[2], ";"));
    wr(Str("selmer_coords_twist", k, ".txt"), Str("KnCoef = ", S[3], ";  \\\\ columns T, phi_a, phi_b"));
    foreach (phis, ph, my(TT = [tt | tt <- TINY, tt[1] == ph[1]][1]);
      wr(Str("tiny_integral_c1_twist", k, ".txt"), Str("c1_", ph[1], " = [", lift(Mod(TT[4][1], K21)), ", ", lift(Mod(TT[5][1], K21)), "];  \\\\ lambda(tau) = c1 tau + O(tau^2), tau = x/z - x(P_i)")));
    foreach (pts, jb, if (jb[1] == k,
      my(d = DISCS[jb[2]], P = discpt(d, jb[3]), r = lambda_at(k, P), tau = if (jb[4] >= 0, P[1] / P[3] - Pk[jb[4] + 1][1], 0));
      if (r[1] != "ok", printf("k = %d, disc %d, X = %d: %s\n", k, jb[2], jb[3], r[1]); next);
      wr(Str("sample_points_twist", k, ".txt"), Str("[", jb[2], ", ", jb[3], ", ", P, ", [", apply(c -> lift(c), Vecrev(r[6][1])), ", ", apply(c -> lift(c), Vecrev(r[6][2])), "], ", jb[4], ", ", tau, "]"))));
    printf("k = %d exported\n", k));
  system(Str("cd ", OUT, " && wc -c *.txt"));  \\ names and sizes only
}
quit;
