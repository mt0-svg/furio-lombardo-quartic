\\ prym_two_descent.gp: full 2-descent over K = K21 for the Prym curves F_k : Y^2 = f_k(x) (k = 0, 1), f_k = c_k G1 h,
\\ h = A^2 - d B^2 irreducible over K, G1 irreducible quadratic (code/earlier-computations/richelot_data.gp; f_k = F0, F1 of
\\ bruin_form.gp, checked). Result (both twists): dim Sel^2 = 4, so rank Jac(F_k)(K) <= 3.
\\
\\ Setting. A = K[x]/(f_k) = L x N with L = K[x]/(G1) (degree 42), N = K[x]/(h) (degree 84), identified with the absolute
\\ fields nfL (Lpol) and nfN (PN) through a root of G1 in L and a root of G2 | h in N. The x - T map
\\   mu : J(K)/2J(K) -> A^x/(K^x A^x2),  [P1 + P2 - Dinf] -> (x(P1) - T)(x(P2) - T)
\\ is injective here: its kernel has dimension <= 1 and is nonzero only if no class of K^x/K^x2 other than 1 becomes a
\\ square in every factor (Poonen, Schaefer 1997, and its local version), while d is
\\ a nontrivial class that is a square in L = K(sqrt d) and in N (L is contained in N).
\\ Unramified outside S. Jac(F_k) has good reduction outside the places above 2 and 7; at such a
\\ place v (odd) the image of mu_v is unramified (Schaefer 1996, Stoll 2001), an intrinsic property of A_v (a change of
\\ model multiplies u(T) by an element of K^x A^x2). Since h(K) = 1 and A is unramified outside 2 and 7, every class of
\\ the image has a representative in A(S,2) = L(S,2) x N(S,2) (S = places above 2 and 7), and two such representatives
\\ differ by the image of K(S,2), of dimension 16 - 1 = 15 (the kernel of K(S,2) -> A(S,2) is <d>).
\\ Bases (no GRH): L(S,2): 29 exact S-units (Cl(L)[2] = 0, class_group_l42_two.gp); N(S,2): 53 exact S-units
\\ (Cl(N)[2] = 0, class_group_n84_two.gp; saturated norm relation S-units, p21_25 and p21_28).
\\ Local conditions at v in S and at the real places: mu_v(J(K_v)) is the span of the classes of certified K_v-rational
\\ divisors once that span has dimension D_v = dim J(K_v)[2] + 2 [K_v:Q_2] [v | 2] - eps_v modulo the image of K_v^x
\\ (td2loc.gp stopping rule). 2-adic places: divisors of p21_21_localimages.gp (J side, complete runs), certified again
\\ (td2_certify) and recoordinatized here with the absolute factor fields (an independent code path from the small models
\\ used there). Place above 7 (e = 7, f = 3, v(c) odd, so no K_v-point far from the roots of f): pairs of points near the
\\ four K_v-rational Weierstrass points (root approximations in K by an HNF solve, sel_approx; square roots in the residue
\\ field; each pair checked exactly by nfislocalpower, sel_pairs7). Real places: pairs of real points, D = dim J(R)[2]
\\ - 2 (J(R)/2J(R) = pi_0(J(R)); the kernel of mu at a real place is 0 since -1 is a square in C and a real root gives
\\ a factor of odd degree).
\\ Norm condition: not imposed. It is implied: if alpha in A(S,2) satisfies the local conditions at S and at the real
\\ places, N(alpha) is a local square at S and positive at the real places, and an S-unit class; K(sqrt N(alpha)) is
\\ then unramified at all places, so trivial since h(K) = 1. Dropping it could only enlarge the group anyway.
\\ Bound: X = {x in A(S,2) : local conditions}; Sel_fake = X / im K(S,2); dim J(K)[2] = 1 (factors of degree 2 and 4), so
\\ rank Jac(F_k)(K) <= dim X - 15 - 1.
\\ Known answer tests: the classes of the rational 2-torsion point T and of the known points phi(x_i) (phi_known_lifts.gp) lie in
\\ every local image, and their local vectors lie in loc(X) + sum_v image(K_v^x) (a nontrivial test: loc(X) is small).
\\ Run from code/earlier-computations: gp -q prym_two_descent.gp < /dev/null (resumes from caches)
default(parisizemax, 9*10^9); default(nbthreads, 1); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp"); read("field_l42_polynomial.gp"); read("field_n84_polynomial.gp");
read("../lib/richelot.gp"); read("../lib/td2loc.gp");
read("norm_relation_lib.gp"); read("prym_two_descent_lib.gp");
read("phi_known_lifts.gp");
LOGF = Str(SEL, "selmer.log");
lg(s) = write(LOGF, s);
main() = {
  my(t0 = getabstime(), FF, AA, PL, fin, re, GG, G, stage = getenv("SEL_STAGE"));
  system(Str("mkdir -p ", SEL));
  FF = sel_fields(); lg(Str("fields ", getabstime() - t0));
  AA = [sel_alg(FF, 0), sel_alg(FF, 1)];
  PL = sel_places(AA[1]); fin = PL[1]; re = PL[2]; lg(Str("places ", getabstime() - t0));
  if (stage == "places", print("STAGE places done"); return(0));
  GG = sel_gens(FF, AA[1], fin, re); G = GG[1]; lg(Str("generators ", getabstime() - t0));
  printf("global generators: %d x %d coordinate matrix, rank %d (%d ms)\n", #G~, #G, matrank(Mod(G, 2)), getabstime() - t0);
  if (stage == "gens", print("STAGE gens done"); return(0));
  my(res = vector(2));
  for (k = 0, 1, my(A = AA[k + 1], Q = List(), locs = List(), KMs = List(), ok = 1, offs = List(), off = 0, tvecs = List());
    printf("---- twist k = %d\n", k);
    \\ finite places
    for (pi = 1, #fin, my(P = fin[pi], pr = mapget(P, "pr"), us, li, nv = mapget(P, "N"));
      if (pr.p == 2,
        my(fnli = Str("local_images_twist", k, "_e", pr.e, ".bin"), R);
        R = read(fnli); chk(R[1] == k && R[2] == 1 && R[3] == pr.e && R[6] == 1, Str(fnli, " is a complete J side run"));
        chk(vecmin(apply(dv -> td2_certify(mapget(A, "nfK"), pr, mapget(A, "f"), dv[1], dv[2]), R[7])) == 1, Str("the ", #R[7], " divisors of ", fnli, " are certified again here"));
        us = apply(dv -> dv[1], R[7])
      ,
        my(pp = sel_points7(A, P, 40, 10, 12), sp);
        sp = sel_pairs7(A, P, pp[2]);
        printf("  place above 7: %d root approximations, %d points, %d certified pairs\n", #pp[1], #pp[2], sp[3]);
        us = sp[1]);
      li = sel_locimg(A, P, us);
      printf("  %s: local image %d of D_v = %d (%d divisors, %d coordinates)\n", mapget(P, "name"), li[2], li[3], #us, nv);
      if (li[2] != li[3], ok = 0);
      listput(locs, li[1]); listput(KMs, f2span(mapget(P, "KM"))); listput(offs, [off, nv]); off += nv);
    \\ real places
    for (ri = 1, #re, my(rp = re[ri], m = #rp[2] + #rp[3], D = sel_realD(rp), KM, us, li, W);
      KM = if (m, Mat(vectorv(m, i, 1)), matrix(m, 0));
      if (D > 0,
        my(pts = sel_xpoints(A, (fv -> nfeltsign(mapget(A, "nfK"), fv, rp[1]) > 0), 40), sp);
        sp = sel_pairs(pts, (uu -> sel_realcoord(A, rp, td2_uvals(A, uu))), KM, D); us = sp[1]; W = KM;
        foreach (us, uu, W = matconcat([W, sel_realcoord(A, rp, td2_uvals(A, uu))])); W = f2span(W); li = #W - #f2span(KM)
      , W = f2span(KM); li = 0);
      printf("  real place %d: %d real roots, local image %d of D = %d\n", rp[1], m, li, D);
      if (li != D, ok = 0);
      listput(locs, W); listput(KMs, f2span(KM)); listput(offs, [off, m]); off += m);
    chk(off == #G~, "coordinate layout");
    if (!ok, printf("  local images incomplete for k = %d: no bound\n", k); next);
    \\ the Selmer space X
    my(rowsQ = List());
    for (j = 1, #locs, my(o = offs[j], Qv = f2annih(locs[j], o[2]), Gv = matrix(o[2], #G, r, c2, G[o[1] + r, c2]));
      if (#Qv~, listput(rowsQ, Qv * Gv)));
    my(QG = matconcat(Col(Vec(rowsQ))), Xs = lift(matker(Mod(QG, 2))), dX = #Xs);
    printf("  dim X = %d, dim Sel_fake = dim X - 15 = %d, rank Jac(F_%d)(K21) <= %d (%d ms)\n", dX, dX - 15, k, dX - 16, getabstime() - t0);
    lg(Str("k = ", k, ": dim X = ", dX));
    \\ known answer tests: T and phi(x_i) in every local image, and in loc(X) + sum KM_v
    \\ factor values (L, N components) of mu: T = [W1 + W2 - Dinf] (u = G1; Weierstrass rule -f'(th) u'(th) in the L
    \\ component, that is f'(th1)(th2 - th1)), and phi(x_i) = [U, V] (u = U made monic)
    my(pts = List(), nm = List(), G1x = td2_Kx(mapget(A, "nfK"), subst(RIN[k + 1][2], t, x)));
    listput(pts, [-td2_evalu(A, 1, mapget(A, "fd")) * td2_evalu(A, 1, deriv(G1x, 'x)), td2_evalu(A, 2, G1x)]); listput(nm, "T");
    foreach (PHI, ph, if (ph[2] == k, my(U = td2_Kx(mapget(A, "nfK"), subst(ph[4], t, x))); listput(pts, td2_uvals(A, U / pollead(U))); listput(nm, Str("phi(x_", ph[1], ")"))));
    my(GX = G * Xs, KMbar = matrix(#G~, 0), LV = matrix(#G~, 0));
    for (j = 1, #locs, my(o = offs[j], Kj = KMs[j]); if (#Kj, KMbar = matconcat([KMbar, matconcat([matrix(o[1], #Kj); Kj; matrix(#G~ - o[1] - o[2], #Kj)])])));
    for (q = 1, #pts, my(vals = pts[q], col = List(), inall = 1);
      for (pi = 1, #fin, my(cc = td2_coordvals(A, fin[pi], vals)); listput(col, cc);
        if (matrank(Mod(matconcat([locs[pi], cc]), 2)) > matrank(Mod(locs[pi], 2)), inall = 0));
      for (ri = 1, #re, my(cc = sel_realcoord(A, re[ri], vals), Wr = locs[#fin + ri]); listput(col, cc);
        if (#cc && matrank(Mod(matconcat([Wr, cc]), 2)) > matrank(Mod(Wr, 2)), inall = 0));
      my(cv = concat(Vec(col)), base = matconcat([GX, KMbar]), r0 = matrank(Mod(base, 2)), r1 = matrank(Mod(matconcat([base, cv]), 2)));
      printf("  KAT %s: in every local image %d; in loc(X) + sum K_v^x %d\n", nm[q], inall, r1 == r0);
      if (!inall || r1 != r0, ok = 0);
      LV = matconcat([LV, cv]));
    my(r0 = matrank(Mod(KMbar, 2)), r1 = matrank(Mod(matconcat([KMbar, LV]), 2)));
    printf("  KAT: the %d known classes span %d dimensions modulo sum K_v^x (loc(X) modulo sum K_v^x: %d)\n", #pts, r1 - r0,
           matrank(Mod(matconcat([KMbar, GX]), 2)) - r0);
    res[k + 1] = [dX, ok]);
  printf("RESULT %s (%d ms)\n", res, getabstime() - t0);
}
main();
quit;
