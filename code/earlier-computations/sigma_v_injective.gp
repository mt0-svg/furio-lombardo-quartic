\\ sigma_v_injective.gp: the 2-adic localisation of the 2-Selmer group of Jac(F_k)/K21 (k = 0, 1), for Selmer group
\\ Chabauty at p = 2 (Stoll, Chabauty without the Mordell-Weil group, arXiv:1506.04286, Theorem 2.1).
\\ Reuses prym_two_descent.gp verbatim up to the known answer tests (same caches), then prints:
\\  (a) dim sigma(Sel), sigma : Sel -> sum_{v | 2} J(K_v)/2J(K_v), total and per 2-adic place; ker sigma = 0 iff 4;
\\  (b) the relations among the classes of T, phi(x_a), phi(x_b) in Sel (which combination lies in 2 J(K21));
\\  (c) dim of the image of the known classes under sigma.
\\ Saves [G X, K_v^x images, known classes, offsets, local images, K_v^x spans, place names, dim X] to SEL/selX_k<k>.bin.
\\ Run from code/earlier-computations: gp -q sigma_v_injective.gp < /dev/null
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
    \\ ---- analysis for Selmer group Chabauty at 2
    my(two = [j | j <- [1 .. #fin], mapget(fin[j], "pr").p == 2], rows2 = List(), sel2, KM2, GX2, LV2, r0, dS, dK, kr);
    foreach (two, j, my(o = offs[j]); for (r = 1, o[2], listput(rows2, o[1] + r)));
    rows2 = Vec(rows2);
    sel2 = (M -> matrix(#rows2, #M, i, c, M[rows2[i], c]));
    KM2 = sel2(KMbar); GX2 = sel2(GX); LV2 = sel2(LV);
    r0 = matrank(Mod(KM2, 2));
    dS = matrank(Mod(matconcat([KM2, GX2]), 2)) - r0;
    dK = matrank(Mod(matconcat([KM2, LV2]), 2)) - r0;
    printf("  SIGMA k = %d: dim sigma(Sel) = %d of dim Sel = %d (ker sigma = 0: %d); known classes under sigma: %d\n", k, dS, dX - 15, dS == dX - 15, dK);
    foreach (two, j, my(o = offs[j], rr = vector(o[2], r, o[1] + r), selj, Kj, Gj);
      selj = (M -> matrix(#rr, #M, i, c, M[rr[i], c])); Kj = selj(KMbar); Gj = selj(GX);
      printf("  SIGMA k = %d: at %s, dim of the image of Sel = %d (D_v = %d)\n", k, mapget(fin[j], "name"),
             matrank(Mod(matconcat([Kj, Gj]), 2)) - matrank(Mod(Kj, 2)), mapget(fin[j], "D")));
    kr = lift(matker(Mod(matconcat([KMbar, LV]), 2)));
    printf("  RELATIONS k = %d (coefficients of %s modulo 2J(K21), from the full localisation):\n", k, Vec(nm));
    for (c = 1, #kr, my(vv = vector(#pts, q, kr[#kr~ - #pts + q, c])); if (vv != 0, printf("    %s\n", vv)));
    lg(Str("sigma k = ", k, ": ", dS, " known ", dK));
    wbin(Str(SEL, "selX_k", k, ".bin"), [GX, KMbar, LV, Vec(offs), Vec(locs), Vec(KMs), apply(P -> mapget(P, "name"), Vec(fin)), dX]);
    my(r0 = matrank(Mod(KMbar, 2)), r1 = matrank(Mod(matconcat([KMbar, LV]), 2)));
    printf("  KAT: the %d known classes span %d dimensions modulo sum K_v^x (loc(X) modulo sum K_v^x: %d)\n", #pts, r1 - r0,
           matrank(Mod(matconcat([KMbar, GX]), 2)) - r0);
    res[k + 1] = [dX, ok]);
  printf("RESULT %s (%d ms)\n", res, getabstime() - t0);
}
main();
quit;
