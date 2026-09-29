\\ prym_two_descent_lib.gp: functions of the full 2-descent over K21 for the Prym curves F_k : Y^2 = f_k(x), f_k = c_k G1 h,
\\ h = A^2 - d B^2 (code/earlier-computations/richelot_data.gp), used by prym_two_descent.gp. See the header of that file.
\\ The caller sets parisizemax, nbthreads, realprecision and reads bruin_form.gp, richelot_data.gp, field_l42_polynomial.gp,
\\ field_n84_polynomial.gp, richelot.gp, td2loc.gp, norm_relation_lib.gp first.
SEL = "/tmp/k21c/sel/";
\\ ---------------------------------------------------------------- fields
\\ [nfK, nfL, nfN, aL, thL, aN, thN]: nfK = K21 (variable b, maximal order), nfL = L (Lpol in u, maximal at 2, 7),
\\ nfN = N (PN in y, from p21_25); aL, aN the images of b; thL a root of G1 in L, thN a root of G2 (hence of h) in N.
\\ G1, A, B, d are the same for both twists (checked); only c differs.
sel_fields() = {
  my(fn = Str(SEL, "fields.bin"), nfK, nfL, nfN, PNy, emb, aL, faL, rL = 0, aN, R = RIN[1], G1 = R[2], A = R[3], B = R[4],
     d = R[5], G1L, thL, sdN, G2N, thN, hN, t0 = getabstime());
  if (fexists(fn), return(read(fn)));
  chk(RIN[2][2] == G1 && RIN[2][3] == A && RIN[2][4] == B && RIN[2][5] == d, "G1, A, B, d are the same for both twists");
  nfK = nfinit(K21); nfL = nfinit([Lpol, [2, 7]]); nfN = read(Str(DIR, "nfN.bin")); PNy = nfN.pol;
  emb = nfisincl(K21, Lpol); chk(#emb == 1, "K21 has a unique embedding into L"); aL = Mod(emb[1], Lpol);
  faL = read(Str(DIR, "faL_N.bin"));
  for (j = 1, #faL~, if (poldegree(faL[j, 1]) == 1, rL = Mod(lift(-polcoef(faL[j, 1], 0)), PNy); break));
  aN = subst(emb[1], u, rL);
  chk(subst(K21, b, aL) == 0 && subst(K21, b, aN) == 0, "images of b in L and N are roots of K21");
  G1L = Pol(apply(cf -> subst(lift(Mod(cf, K21)), b, aL), Vec(subst(G1, t, x))), x);
  thL = nfroots(nfL, lift(G1L)); chk(#thL == 2, "G1 splits in L"); thL = Mod(thL[1], Lpol);
  sdN = nfroots(nfN, x^2 - lift(subst(lift(Mod(d, K21)), b, aN))); chk(#sdN == 2, "d is a square in N"); sdN = Mod(sdN[1], PNy);
  G2N = Pol(apply(cf -> subst(lift(Mod(cf, K21)), b, aN), Vec(subst(A, t, x))), x) - sdN * Pol(apply(cf -> subst(lift(Mod(cf, K21)), b, aN), Vec(subst(B, t, x))), x);
  thN = nfroots(nfN, lift(G2N / pollead(G2N))); chk(#thN == 2, "G2 splits in N"); thN = Mod(thN[1], PNy);
  hN = Pol(apply(cf -> subst(lift(Mod(cf, K21)), b, aN), Vec(subst(A^2 - d * B^2, t, x))), x);
  chk(subst(G1L, x, thL) == 0 && subst(hN, x, thN) == 0, "thL is a root of G1, thN a root of h");
  wbin(fn, [nfK, nfL, nfN, aL, thL, aN, thN]);
  printf("fields and embeddings: %d ms\n", getabstime() - t0);
  [nfK, nfL, nfN, aL, thL, aN, thN];
}
\\ the etale algebra of F_k (td2loc format), factor fields L (G1) and N (h)
sel_alg(FF, k) = {
  my(nfK = FF[1], R = RIN[k + 1], c = R[1], G1x = subst(R[2], t, x), hx = subst(R[3]^2 - R[5] * R[4]^2, t, x), f, FL, FN);
  f = td2_Kx(nfK, c * G1x * hx);
  chk(f == td2_Kx(nfK, subst(if (k == 0, F0, F1), t, x)), Str("f_", k, " = c G1 (A^2 - d B^2) is the Prym sextic F", k));
  FL = [td2_Kx(nfK, G1x / pollead(G1x)), FF[2], FF[4], FF[5]];
  FN = [td2_Kx(nfK, hx / pollead(hx)), FF[3], FF[6], FF[7]];
  td2_alg_from(nfK, f, [FL, FN], [2, 7]);
}
\\ ---------------------------------------------------------------- places
\\ finite places: td2_place (twist independent: it only uses the factor fields); real places: [i, jsL, jsN] with jsL,
\\ jsN the real embeddings of L and N above the real embedding i of K21 (compared through the images of b)
\\ indices of the real embeddings of nfG whose image of b (ag) is nearest to the real root rK[i] of K21 (clear margin)
sel_realabove(nfG, ag, rK, i) = {
  my(agv = nfeltembed(nfG, ag), res = List());
  for (j = 1, nfG.r1, my(dd = vector(#rK, i2, abs(agv[j] - rK[i2])), m1 = vecmin(dd), m2 = vecmin(concat(dd[1..i-1], dd[i+1..#dd])));
    if (dd[i] == m1, chk(m1 < 10^-5 * m2, "clear nearest root"); listput(res, j)));
  Vec(res);
}
sel_places(A) = {
  my(fn = Str(SEL, "places.bin"), nfK = mapget(A, "nfK"), flds = mapget(A, "flds"), fin = List(), re = List(), t0 = getabstime());
  if (fexists(fn), fin = List(read(fn)[1]),
  foreach (concat(idealprimedec(nfK, 2), idealprimedec(nfK, 7)), pr,
    my(P = td2_place(A, pr)); listput(fin, P);
    printf("  %s: tors2 %d, eps %d, D_v = %d, coordinates %d, rank of K_v^x image %d (%d ms)\n", mapget(P, "name"), mapget(P, "tors2"),
           mapget(P, "eps"), mapget(P, "D"), mapget(P, "N"), matrank(Mod(mapget(P, "KM"), 2)), getabstime() - t0)));
  \\ real embeddings of nfG above the real embedding i of K: nearest real root of K21 to the image of b
  \\ (nfeltembed), with a clear margin
  my(rK = nfK.roots);
  for (i = 1, nfK.r1,
    my(js = vector(2, fi, sel_realabove(flds[fi][2], flds[fi][3], rK, i)));
    chk(#js[1] % 2 == 0 && #js[2] % 2 == 0, "even numbers of real roots of G1 and h at a real place");
    listput(re, [i, js[1], js[2]]);
    printf("  real place %d: %d real roots of G1, %d of h\n", i, #js[1], #js[2]));
  wbin(fn, [Vec(fin), Vec(re)]);
  [Vec(fin), Vec(re)];
}
\\ signs (1 for negative) of a in nfG at the real embeddings js, from the embedding matrix stored by nfinit (nfeltsign
\\ recomputes the roots of the degree 84 polynomial at each call); nfeltsign when a value is too close to 0
sel_sign(nfG, a, js) = {
  my(c = nfalgtobasis(nfG, a), M = nfG[5][1], res = vector(#js));
  for (i = 1, #js, my(row = M[js[i], ], z = real(row * c), bnd = sum(k = 1, #c, abs(row[k] * c[k])), pr = oo);
    for (k = 1, #row, if (type(row[k]) == "t_REAL" || type(row[k]) == "t_COMPLEX", pr = min(pr, precision(row[k]))));
    if (pr == oo || abs(z) < bnd * 10^(10 - pr), return(apply(e -> e < 0, nfeltsign(nfG, a, js))));
    res[i] = z < 0);
  res;
}
\\ real place data: m real roots, dim J(R)[2] = log2(1 + C(m, 2) + (6 - m)/2), D = dim J(R)[2] - 2 (eps = 0: see header)
sel_realD(rp) = { my(m = #rp[2] + #rp[3], cnt = 1 + m * (m - 1) / 2 + (6 - m) / 2, t2 = valuation(cnt, 2)); chk(cnt == 2^t2, "#J(R)[2] power of 2"); t2 - 2; }
\\ coordinates at a real place of the vector of factor values vals: signs (1 for negative)
sel_realcoord(A, rp, vals) = {
  my(flds = mapget(A, "flds"), v = List());
  for (fi = 1, 2, if (#rp[fi + 1], my(sg = sel_sign(flds[fi][2], vals[fi], rp[fi + 1])); foreach (sg, e, listput(v, e))));
  Col(Vec(v));
}
\\ coordinates at a finite place P of an element a of the factor field fi (the other factor = 1)
sel_fincoord(A, P, fi, a) = {
  my(Ws = mapget(P, "Ws"), sq = mapget(P, "sq"), flds = mapget(A, "flds"));
  concat(vector(#Ws, j, if (Ws[j][1] == fi, td2_sqcoord(flds[fi][2], sq[j], a), vectorv(1 + #sq[j][4]))));
}
\\ ---------------------------------------------------------------- local images
\\ span of the columns of M modulo 2 (as a matrix of independent columns)
f2span(M) = { if (#M == 0, return(M)); my(im = matimage(Mod(M, 2))); lift(im); }
\\ local image at a finite place from divisors (list of u): [W (columns: image of K_v^x and the divisor classes), dim of
\\ the divisor part modulo K_v^x, D_v]
sel_locimg(A, P, us) = {
  my(KM = mapget(P, "KM"), rkK = matrank(Mod(KM, 2)), C = KM, W, dm);
  foreach (us, uu, C = matconcat([C, td2_coord(A, P, uu)]));
  W = f2span(C); dm = #W - rkK;
  [W, dm, mapget(P, "D")];
}
\\ annihilator rows of the span W inside F2^n: Q with Q y = 0 iff y in W
f2annih(W, n) = { if (#W == 0, return(matid(n))); my(Kr = lift(matker(Mod(W~, 2)))); if (#Kr == 0, matrix(0, n), Kr~); }
\\ ---------------------------------------------------------------- global generators of A(S,2) = L(S,2) x N(S,2)
\\ column of local coordinates (finite places in order, then real places) of an element a of the factor field fi
sel_loccol(A, fin, re, fi, a) = {
  my(v = List());
  foreach (fin, P, listput(v, sel_fincoord(A, P, fi, a)));
  foreach (re, rp, my(z = vector(2, j, if (j == fi && #rp[j + 1], sel_sign(mapget(A, "flds")[j][2], a, rp[j + 1]), vector(#rp[j + 1]))));
    listput(v, Col(concat(z[1], z[2]))));
  concat(Vec(v));
}
\\ [G, info]: G = local coordinates of the 29 + 53 generators (columns): the S-units of L (28 in compact form, then -1)
\\ and the saturated basis of N(S,2) (sunits_n84_saturate.gp, compact form over the base elements of p21_25); cached, with
\\ the per base element coordinates cached in SEL/loccache.bin as they are computed
sel_gens(FF, A, fin, re) = {
  my(fn = Str(SEL, "gens.bin"), cn = Str(SEL, "loccache.bin"), cache, su, baseL, NS, TAB, NSAT, bN, cols = List(), t0 = getabstime(), ncomp = 0, getc);
  if (fexists(fn), return(read(fn)));
  cache = if (fexists(cn), read(cn), Map());
  su = sunits_of(subst(Lpol, u, y), "L");
  baseL = apply(g -> Mod(subst(g, x, u), Lpol), su[3]);
  NS = read(Str(DIR, "nsunits.bin")); TAB = NS[2]; NSAT = read(Str(DIR, "nsat.bin")); bN = NSAT[1];
  chk(#su[2] == 28 && #bN == 53, "28 + 1 generators of L(S,2) and 53 of N(S,2)");
  \\ L generators
  for (i = 1, 28, my(fm = su[2][i], c = 0);
    for (l = 1, #fm, if (fm[l][2] % 2, my(kk = Str("L", fm[l][1]), cc);
      if (!mapisdefined(cache, kk, &cc), cc = sel_loccol(A, fin, re, 1, baseL[fm[l][1]]); mapput(cache, kk, cc); ncomp++);
      c += cc));
    listput(cols, c % 2));
  listput(cols, sel_loccol(A, fin, re, 1, Mod(-1, Lpol)) % 2);
  wbin(cn, cache);
  printf("  L generators: %d base coordinates computed (%d ms)\n", ncomp, getabstime() - t0);
  \\ N generators
  for (i = 1, 53, my(el = bN[i], c = if (el[1], sel_loccol(A, fin, re, 2, Mod(-1, FF[3].pol)), 0), M = Mat(el[2]));
    for (l = 1, #M~, if (M[l, 2] % 2, my(kk = Str("N", M[l, 1]), cc, rk2 = eval(Str("[", M[l, 1], "]")));
      if (!mapisdefined(cache, kk, &cc), cc = sel_loccol(A, fin, re, 2, nfbasistoalg(FF[3], TAB[rk2[1]][3][rk2[2]])); mapput(cache, kk, cc); ncomp++;
        if (ncomp % 20 == 0, wbin(cn, cache); write(Str(SEL, "progress.log"), Str(ncomp, " base coordinates, ", getabstime() - t0, " ms"))));
      c += cc));
    for (l = 1, #el[3], if (el[3][l][2] % 2, c += sel_loccol(A, fin, re, 2, nfbasistoalg(FF[3], el[3][l][1]))));
    listput(cols, c % 2));
  wbin(cn, cache);
  printf("  N generators: %d base coordinates computed in all (%d ms)\n", ncomp, getabstime() - t0);
  my(G = matconcat(Vec(cols)));
  wbin(fn, [G, su]);
  [G, su];
}
\\ ---------------------------------------------------------------- sampling at the place above 7 and at real places
\\ x-coordinates x0 in K of points of C over K_v: f(x0) a nonzero square in K_v (exact test nfislocalpower), or for a
\\ real place i, f(x0) > 0 at i (nfeltsign); candidates: small rationals, then small elements of O_K
sel_xpoints(A, test, nwant) = {
  my(nfK = mapget(A, "nfK"), f = mapget(A, "f"), pts = List(), cands = List());
  for (n = 1, 60, foreach ([n, -n, 1/n, -1/n, n/7, -n/7, 7*n, -7*n, n/2, -n/2], c, listput(cands, c)));
  listput(cands, 0);
  foreach (cands, c, if (#pts >= nwant, break);
    my(fv = subst(f, 'x, c)); if (fv != 0 && test(fv), listput(pts, c)));
  my(tries = 0);
  while (#pts < nwant && tries < 20000, tries++;
    my(c = nfbasistoalg(nfK, vectorv(21, i, random(7) - 3)) / (1 + random(3)), fv = subst(f, 'x, c));
    if (fv != 0 && test(fv), listput(pts, c)));
  Vec(pts);
}
\\ divisors P_i + P_j (u = (x - x_i)(x - x_j)) from the points pts; stops when the span modulo the image of K_v^x
\\ reaches D (coordinate function coordf(u), K_v^x image KM)
sel_pairs(pts, coordf, KM, D) = {
  my(C = KM, rkK = if (#KM, matrank(Mod(KM, 2)), 0), rk = rkK, us = List());
  for (i = 1, #pts, for (j = i + 1, #pts, if (rk - rkK >= D, break(2));
    my(uu = ('x - pts[i]) * ('x - pts[j]), cc = coordf(uu), C2 = if (#C, matconcat([C, cc]), Mat(cc)), r2 = matrank(Mod(C2, 2)));
    if (r2 > rk, C = C2; rk = r2; listput(us, uu))));
  [Vec(us), rk - rkK];
}
\\ ---------------------------------------------------------------- the place above 7 (odd, e = 7, f = 3)
\\ a in K with v_W(a - th) >= M - v_W(den) for the root th of the factor field fi at a prime W of degree 1 over v:
\\ O_K + W^M = O_G at W (e = f = 1 over v), solved as an integer linear system [images of zk_K | HNF(W^M)] X = den th
sel_approx(A, fi, W, M) = {
  my(nfK = mapget(A, "nfK"), F = mapget(A, "flds")[fi], nfG = F[2], Z = mapget(A, "pre")[fi][1], n = poldegree(nfK.pol),
     nG = poldegree(nfG.pol), M1, H, tc, den, hn, U, sol, c, q, a, p = W.p);
  M1 = matconcat(vector(n, j, nfalgtobasis(nfG, Z[j])));
  H = idealhnf(nfG, idealpow(nfG, W, M));
  tc = nfalgtobasis(nfG, F[4]); den = denominator(tc); tc *= den;
  [hn, U] = mathnf(matconcat([M1, H]), 1);
  chk(#hn == nG, "O_K + W^M has full rank");
  sol = U[, #U - nG + 1 .. #U] * matsolve(hn, tc);
  chk(denominator(sol) == 1, "den th lies in O_K + W^M");
  q = p^ceil(M / idealval(nfK, p, idealprimedec(nfK, p)[1]));
  c = vectorv(n, i, centerlift(Mod(sol[i], q)));
  a = nfbasistoalg(nfK, c) / den;
  chk(nfeltval(nfG, td2_Kimg(A, fi, a) - F[4], W) >= M - nfeltval(nfG, den, W), "root approximation");
  a;
}
\\ K_v-points near the K_v-rational Weierstrass points: x = a + pi^k w (a a root approximation, 1 <= k <= kmax, w small
\\ in O_K), f(x) of even valuation 2m with a square residue of f(x) / pi^(2m); y = pi^m (lift of the residue square root)
sel_points7(A, P, M, kmax, per) = {
  my(nfK = mapget(A, "nfK"), f = mapget(A, "f"), pr = mapget(P, "pr"), Ws = mapget(P, "Ws"), degs = mapget(P, "degs"),
     pi = mapget(P, "Ksq")[2], modpr = nfmodprinit(nfK, pr), roots = List(), pts = List());
  for (j = 1, #Ws, if (degs[j] == 1, listput(roots, sel_approx(A, Ws[j][1], Ws[j][2], M))));
  foreach (roots, a, my(got = 0, tries = 0);
    while (got < per && tries < 4000, tries++;
      my(k = 1 + random(kmax), w = nfbasistoalg(nfK, vectorv(21, i, random(7) - 3)), xx, fx, vv, m, zz, r, sq);
      xx = a + pi^k * w; fx = subst(f, 'x, xx); if (fx == 0, next);
      vv = nfeltval(nfK, fx, pr); if (vv % 2, next);
      m = vv / 2; zz = fx / pi^(2 * m);
      r = nfmodpr(nfK, zz, modpr); if (r == 0 || !issquare(r, &sq), next);
      listput(pts, [xx, pi^m * nfmodprlift(nfK, sq, modpr)]); got++));
  [Vec(roots), Vec(pts)];
}
\\ divisors P_i + P_j (u = (x - x_i)(x - x_j)) until the span modulo the image of K_v^x reaches D_v. Each x_i is in K and
\\ f(x_i) is a nonzero square in K_v (even valuation and square residue, p odd: Hensel), so P_i = (x_i, sqrt f(x_i)) is a
\\ K_v-point and P_i + P_j - Dinf a K_v-rational class, whatever the signs of the square roots (u does not see them).
\\ td2_certify is not used here: its bound through the line v is too crude when x_i, x_j lie in one residue disc.
sel_pairs7(A, P, pts) = {
  my(nfK = mapget(A, "nfK"), f = mapget(A, "f"), pr = mapget(P, "pr"), KM = mapget(P, "KM"), C = KM, rkK = matrank(Mod(KM, 2)),
     rk = rkK, us = List(), D = mapget(P, "D"), ncert = 0);
  for (i = 1, #pts, for (j = i + 1, #pts, if (rk - rkK >= D, break(2));
    my(p1 = pts[i], p2 = pts[j], uu, vl, cc, r2);
    if (p1[1] == p2[1], next);
    uu = ('x - p1[1]) * ('x - p2[1]); vl = p1[2] + (p2[2] - p1[2]) / (p2[1] - p1[1]) * ('x - p1[1]);
    if (!nfislocalpower(nfK, pr, subst(f, 'x, p1[1]), 2) || !nfislocalpower(nfK, pr, subst(f, 'x, p2[1]), 2), error("a point is not K_v-rational"));
    ncert++;
    cc = td2_coord(A, P, uu); r2 = matrank(Mod(matconcat([C, cc]), 2));
    if (r2 > rk, C = matconcat([C, cc]); rk = r2; listput(us, uu))));
  [Vec(us), rk - rkK, ncert];
}
