\\ selmer_rows.gp: local coordinate certificates at one place of K21 for one twist.
\\ Environment: SB_PLACE in {w6, w12, w7, v} (or X for the final F_2 stage), SB_K in {0, 1}, SB_GENS = the Lean file
\\ lean/FurioLombardo/Discharge/SelmerBasis/SUnitData.lean (the 82 generators Pgen s; unset: stages 5 and 6 are skipped).
\\ Run from code/earlier-computations:
\\   SB_PLACE=w6 SB_K=1 gp -q ../selmer-local-conditions/selmer_rows.gp < /dev/null > ../selmer-local-conditions/selmer_rows_twist1_w6.out
\\ Writes ../selmer-local-conditions/selmer_rows_twist<k>_<place>.gp (certificate data) and prints every check.
\\ Stages: 0 tools and global data; 1 components (models, roots, Hensel); 2 standard basis KAT and negative controls;
\\ 3 kappa; 4 points and mu; 5 generators Pgen s (tau_j); 6 F_2 data at the place (V_w, rows C_w); stage X: X from the
\\ rows of all places (and the real places 5, 6 for twist 0).
default(parisizemax, 1800 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp");
read("../selmer-local-conditions/selmer_rows_lib.gp"); read("../selmer-global-bound/tower_lib.gp");
PLN = getenv("SB_PLACE"); KT = eval(getenv("SB_K")); GENSF = getenv("SB_GENS");
OUTD = "../selmer-local-conditions/";
SBu7 = -1;
T00 = getabstime();
stage(s) = printf("==== stage %s (%d ms)\n", s, getabstime() - T00);
wr(fn, nm, v) = write(fn, nm, " = ", v, ";");
fex(fn) = my(r = 0); iferr(fileclose(fileopen(fn, "r")); r = 1, E, r = 0); r;
zk(z) = nfalgtobasis(nfK, z)~;
\\ ---------------------------------------------------------------- stage 1: components of place pi
\\ spec: list of [g ("q" or "h"), n, A, B, ram]; roots: one per component, distinct K_w-orbits for the same g
build_comps(W, specs) = {
  my(comps = List(), used = List(), gsc = Map());
  foreach (["q", "h"], g, mapput(gsc, g, sb_gscale(W, if (g == "q", SBq, SBh))));
  for (j = 1, #specs, my(sp = specs[j], C = sb_comp(W, sp[2], sp[3], sp[4], sp[5]), gs = mapget(gsc, sp[1]), R, pick = 0);
    R = sb_roots(C, gs[2][4], 400);
    printf("  component %d (%s, n = %d): %d roots of the scaled factor in O_F, [v(gh(t')), v(gh'(t'))] = %s\n", j, sp[1], sp[2], #R, apply(r -> [r[2], r[3]], R));
    for (i = 1, #R, my(r = R[i][1], dl = R[i][2] - R[i][3], cj = sb_conjs(C, r), gen = 1, new = 1);
      for (l = 2, #cj, if (val(C, cj[l] - r) >= dl, gen = 0));
      foreach (used, U, if (U[1] == sp[1] && U[2] == sp[2] && U[3] == sp[3] && U[4] == sp[4], foreach (cj, c1, if (val(C, c1 - U[5]) >= dl, new = 0))));
      if (gen && new, pick = i; break));
    chq(pick, Str("component ", j, ": a root generating F over K_w, not conjugate to a root already used"));
    my(r = R[pick], gh = gs[2][4], dg = vector(#gh - 1, i, i * gh[i + 1]), v1 = val(C, evGh(C, gh, r[1])), v2 = val(C, evGh(C, dg, r[1])));
    chq(v1 == r[2] && v2 == r[3] && v1 > 2 * v2 && val(C, r[1]) >= 0, Str("component ", j, ": Hensel certificate v(gh(t')) = ", v1, " > 2 v(gh'(t')) = ", 2 * v2, ", t' integral; v(tau' - t') >= ", v1 - v2));
    mapput(C, "g", sp[1]); mapput(C, "s", gs[1]); mapput(C, "tp", r[1]); mapput(C, "del", v1 - v2); mapput(C, "gsc", gs[2]); mapput(C, "hv", [v1, v2]);
    listput(used, [sp[1], sp[2], sp[3], sp[4], r[1]]);
    listput(comps, C));
  Vec(comps);
}
comp_record(C) = { [mapget(C, "g"), mapget(C, "n"), mapget(C, "eF"), mapget(C, "fF"), mapget(C, "ej"), mapget(C, "nu"), zk(mapget(C, "A")), zk(mapget(C, "B")),
  mapget(C, "s"), mapget(C, "gsc")[1 .. 3], apply(zk, mapget(C, "gsc")[4]), apply(zk, co(C, mapget(C, "tp"))), mapget(C, "hv"), mapget(C, "del"), mapget(C, "bnames")]; }
place_specs(pi, W) = {
  if (pi == 3, my(ei = sb_eisen(W, poldisc(SBq))); printf("  K_w3(sqrt disc q): unit part at odd depth %d, Eisenstein P1 = Y1^2 - B Y1 - A, v(A) = %d, v(B) = %d\n", ei[3], vw(W, ei[1]), vw(W, ei[2]));
    chq(vw(W, ei[1]) == 1 && vw(W, ei[2]) >= 1, "w3: P1 Eisenstein"); return([["q", 2, ei[1], ei[2], 1], ["h", 2, ei[1], ei[2], 1], ["h", 2, ei[1], ei[2], 1]]));
  if (pi == 2, printf("  w2: P1 = Y1^2 - Y1 + 1 (reduction irreducible over F_2: unramified)\n"); return([["q", 2, -1, 1, 0], ["h", 2, -1, 1, 0], ["h", 2, -1, 1, 0]]));
  if (pi == 1, my(ei = sb_eisen(W, poldisc(SBq))); printf("  K_v(sqrt disc q): unit part at odd depth %d, v(A) = %d, v(B) = %d; h component F1(Y2), Y2^2 - Y2 + 1\n", ei[3], vw(W, ei[1]), vw(W, ei[2]));
    chq(vw(W, ei[1]) == 1 && vw(W, ei[2]) >= 1, "v: P1 Eisenstein"); return([["q", 2, ei[1], ei[2], 1], ["h", 4, ei[1], ei[2], 1]]));
  \\ place above 7: q splits; h = two linear factors and a ramified quadratic K_7(sqrt(delta)), delta = al or -al
  my(al = mapget(W, "al"), del = 0);
  foreach ([al, -al], dd, my(C = sb_comp(W, 2, dd, 0, 1), R = sb_roots(C, sb_gscale(W, SBh)[2][4], 60), ng = [r | r <- R, val(C, sb_conjs(C, r[1])[2] - r[1]) < r[2] - r[3]]);
    printf("  7: delta = %s alpha: %d roots of h in K_7(sqrt delta), %d of them outside K_7\n", if (dd == al, "", "-"), #R, #ng); if (#ng && !del, del = dd));
  chq(del != 0, "7: the ramified quadratic factor field of h found");
  [["q", 1, 0, 0, 0], ["q", 1, 0, 0, 0], ["h", 1, 0, 0, 0], ["h", 2, del, 0, 1], ["h", 1, 0, 0, 0]];
}
\\ ---------------------------------------------------------------- per component certificates of a list of elements
\\ els: list of [name, fi (0 = all components, 1 = q components, 2 = h components), G]; returns [coordinate matrix, records]
cert_list(comps, els, tag) = {
  my(rows = sum(j = 1, #comps, #mapget(comps[j], "bas")), A = matrix(rows, #els), recs = List(), t0 = getabstime());
  for (i = 1, #els, my(off = 0, el = els[i]);
    for (j = 1, #comps, my(C = comps[j], nb = #mapget(C, "bas"));
      if (el[2] == 0 || (el[2] == 1 && mapget(C, "g") == "q") || (el[2] == 2 && mapget(C, "g") == "h"),
        my(ce = sb_cert(C, el[3], el[1])); for (l = 1, nb, A[off + l, i] = ce[7][l]); listput(recs, concat([j], ce[1 .. 10])));
      off += nb));
  if (tag != "", printf("  %s: %d elements, %d certificates, all verified (%d ms)\n", tag, #els, #recs, getabstime() - t0));
  [A, Vec(recs)];
}
\\ the 82 generators Pgen s of lean/FurioLombardo/Discharge/SelmerBasis/SUnitData.lean (pgen_s: 6 zk lists, constant first,
\\ of pgenDen s * Pgen s), read with leandef5 of code/selmer-global-bound/tower_lib.gp; e = Pgen s (tau_j) at every component
gens_from_lean(fn) = {
  my(pg = vector(82, s1, leandef5(fn, Str("pgen_", s1 - 1))), pd = leandef5(fn, "pgenDen"), els = Map(), spec = List());
  chq(#pg == 82 && #pd == 82 && vecmin(apply(v -> #v == 6 && vecmin(apply(c -> #c == 21, v)), pg)), "SUnitData.lean: 82 Pgen, 6 zk lists of length 21 each");
  chq(#Set(pg) == 82, "the 82 Pgen coefficient lists are pairwise different (one def read per s)");
  for (s1 = 1, 82, my(G = sum(i = 1, 6, nfbasistoalg(nfK, Col(pg[s1][i])) * x^(i - 1)) / pd[s1], kk = Str("Pgen", s1 - 1));
    mapput(els, kk, [0, lift(Mod(1, K21) * G)]); listput(spec, [0, [kk]]));
  [els, Vec(spec)];
}
\\ ---------------------------------------------------------------- points
\\ split points on the reversed model: x in K21 small with fRev_k(x) a nonzero square in K_w; greedy pairs U = (X - x_i)(X - x_0)
split_points(W, comps, Akap, D, ncand, tmax) = {
  my(f = SBf[KT + 1], pr = mapget(W, "pr"), al = mapget(W, "al"), pts = List(), cls = List(), C = Akap, rk0 = f2rank(Akap), rk = rk0, us = List(), t0 = getabstime(), ntest = 0, cand, roots1 = List());
  foreach (comps, Cj, if (mapget(Cj, "n") == 1, listput(roots1, al^mapget(Cj, "s") * lift(mapget(Cj, "tp")))));
  setrand(20260928);
  while (rk - rk0 < D && ntest < ncand && getabstime() - t0 < tmax, ntest++;
    if (mapget(W, "p") == 7,
      cand = roots1[1 + random(#roots1)] + al^(1 + random(8)) * nfbasistoalg(nfK, vectorv(21, i, random(7) - 3)),
      my(j = random(17) - 8, dg = vector(6, i, random(3) - 1)); cand = if (ntest <= 60, [ntest \ 2 + 1, -(ntest \ 2 + 1)][1 + ntest % 2], al^j * (1 + sum(i = 1, 6, dg[i] * al^i)) + random(5) - 2));
    cand = Mod(lift(Mod(1, K21) * cand), K21);
    my(fx = subst(f, x, cand)); if (fx == 0 || !nfislocalpower(nfK, pr, lift(fx), 2), next);
    my(cc = cert_list(comps, [["pt", 0, x - lift(cand)]], "")[1]);
    if (#pts == 0, listput(pts, [cand, fx]); listput(cls, cc); next);
    my(pc = (cc + cls[1]) % 2, C2 = matconcat([C, pc]), r2 = f2rank(C2));
    if (r2 > rk, C = C2; rk = r2; listput(pts, [cand, fx]); listput(cls, cc)));
  printf("  split points: %d candidates tested, %d points kept, rank mod kappa %d of D = %d (%d ms)\n", ntest, #pts, rk - rk0, D, getabstime() - t0);
  [Vec(pts), rk - rk0];
}
\\ signs (1 for negative) of Pgen s at the four real roots r1 < r2 < r3 < r4 of fRev_k at the real embedding i of K21
\\ (places 5, 6 = real embeddings 1, 2 of nfK.roots); rows sgn(r1) + sgn(r4), sgn(r2) + sgn(r3) (local-places.md);
\\ numerical with a margin check (each value exceeds 10^-30 times the bound of its terms)
real_rows(k, i, gl) = {
  my(emb = (c -> subst(lift(Mod(c, K21)), b, real(nfK.roots[i]))), f = SBf[k + 1], fr = Pol(apply(emb, Vec(f)), x), rr = vecsort(real(select(z -> abs(imag(z)) < 10^-40, polroots(fr)))), R = matrix(2, 82));
  chq(#rr == 4, Str("fRev_", k, " has 4 real roots at the real embedding ", i));
  for (s1 = 1, 82, my(G = mapget(gl[1], gl[2][s1][2][1])[2], Gr = Pol(apply(emb, Vec(G)), x), sg = vector(4));
    for (l = 1, 4, my(v = subst(Gr, x, rr[l]), bd = subst(Pol(apply(abs, Vec(Gr)), x), x, abs(rr[l])));
      if (abs(v) < 10^-30 * bd, error("real_rows: margin")); sg[l] = v < 0);
    R[1, s1] = (sg[1] + sg[4]) % 2; R[2, s1] = (sg[2] + sg[3]) % 2);
  R;
}
\\ ---------------------------------------------------------------- stage X: X from the rows C_w of the certificate files
\\ twist 1: places v, w2, w3, p7; twist 0: v, w2, w3 and the real places 5, 6. X lives in the coordinates of the generator
\\ list of the certificate files (SB2_GENS[1]); all files must use the same list.
run_X() = {
  default(realprecision, 200);
  for (k = 0, 1, my(R = matrix(0, 82), P = if (k, [1, 2, 3, 4], [1, 2, 3]), src = Set(), Xm, gl = 0);
    foreach (P, j, my(fn = Str(OUTD, "selmer_rows_twist", k, "_", SB_PNAME[j], ".gp"));
      chq(fex(fn), Str("certificate file ", fn)); if (!fex(fn), next);
      SB2_ROWS = 0; read(fn); chq(type(SB2_ROWS) == "t_VEC", Str(fn, " has its rows (stage 6 ran)")); if (type(SB2_ROWS) != "t_VEC", next);
      src = setunion(src, [SB2_GENS[1]]); R = matconcat([R; SB2_ROWS[1]]));
    chq(#src == 1, Str("twist ", k, ": one generator list for all places: ", src));
    if (#src != 1, next);
    if (!k, gl = gens_from_lean(src[1]); foreach ([1, 2], i, R = matconcat([R; real_rows(k, i, gl)])));
    Xm = f2ker(R, 82);
    printf("  twist %d: dim X = %d; basis (columns, generator coordinates): %s\n", k, #Xm, Xm);
    chq(#Xm == 19, Str("(iii) twist ", k, ": dim X = 19 (p21_29's value)"));
    if (k, my(R3 = matrix(0, 82), gl1 = gens_from_lean(src[1]));
      foreach ([1, 2, 3], j, read(Str(OUTD, "selmer_rows_twist1_", SB_PNAME[j], ".gp")); R3 = matconcat([R3; SB2_ROWS[1]]));
      R3 = matconcat([R3; real_rows(1, 1, gl1)]);
      printf("  twist 1, places v, w2, w3 and the real place 5 only: dim %d\n", #f2ker(R3, 82));
      chq(#f2ker(R3, 82) == 20, "twist 1: without the place above 7 (v, w2, w3, real place 5) the dimension is 20, as in selmer_bound_subsets.out")));
}
\\ ---------------------------------------------------------------- main
{
  my(pi = [i | i <- [1 .. 4], SB_PNAME[i] == PLN], fn, W, comps, specs, e, kap = List(), K1, Akap, D, mus = List(), musrc, ptsdat = [], gl, elsL, R, Amu, Agen, Cgen, t0);
  stage("0 (tools, global data)");
  chq(f2eqspan([1, 1; 0, 1; 0, 0], [1, 0; 0, 1; 0, 0]) && !f2eqspan(Mat([1, 0, 0]~), Mat([0, 1, 0]~)), "tool: f2eqspan (positive and negative)");
  chq((f2annih(Mat([1, 1, 0]~), 3) * [1, 1, 0]~) % 2 == [0, 0]~ && (f2annih(Mat([1, 1, 0]~), 3) * [1, 0, 0]~) % 2 != [0, 0]~, "tool: f2annih (kills the span, not a vector outside)");
  sb_init();
  if (PLN == "X", run_X(); printf("DONE, %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00); quit);
  pi = pi[1]; fn = Str(OUTD, "selmer_rows_twist", KT, "_", PLN, ".gp"); system(Str("rm -f ", fn));
  W = sb_place(pi); e = mapget(W, "e");
  wr(fn, "SB2_PLACE", [PLN, KT, mapget(W, "p"), e, zk(mapget(W, "al")), zk(mapget(W, "p") / mapget(W, "al")), getenv("SB_GENS")]);
  stage("1 (components, roots)");
  specs = place_specs(pi, W); comps = build_comps(W, specs);
  wr(fn, "SB2_COMPS", apply(comp_record, comps));
  stage("2 (standard basis KAT, negative controls)");
  setrand(1);
  for (j = 1, #comps, my(C = comps[j], bas = mapget(C, "bas"), ok = 1, ok2 = 1, ok3 = 1, ok4 = 1, ok5 = 1, nb = #bas);
    for (i = 1, nb, if (coords(C, bas[i])[1] != vector(nb, l, l == i), ok = 0));
    chq(ok, Str("component ", j, ": the coordinates of the standard basis (", nb, " elements) are the unit vectors"));
    for (r = 1, 4, my(ev = vector(nb, i, random(2)), P = prod(i = 1, nb, if (ev[i], bas[i], 1)) * mapget(C, "one"), ce);
      if (ev == 0, ev[1] = 1; P *= bas[1]); ce = coords(C, P);
      if (ce[1] != ev, ok2 = 0); if (verC(C, P, [0 * ev, ce[2], ce[3]]), ok2 = 0);
      my(ce2 = ce, ix = 1 + random(nb)); ce2[1][ix] = 1 - ce2[1][ix]; if (verC(C, P, ce2), ok3 = 0));
    chq(ok2, Str("component ", j, ": 4 random products of basis elements: coordinates = exponents, never a square (verC with zero bits fails)"));
    chq(ok3, Str("component ", j, ": negative control, a certificate with one flipped bit fails"));
    for (r = 1, 4, my(z1 = mk(C, vector(mapget(C, "n"), i, nfbasistoalg(nfK, vectorv(21, l, random(9) - 4)))), z2 = mk(C, vector(mapget(C, "n"), i, nfbasistoalg(nfK, vectorv(21, l, random(9) - 4)))), c1, c2, c12);
      if (val(C, z1) == oo || val(C, z2) == oo, next);
      c1 = coords(C, z1)[1]; c2 = coords(C, z2)[1]; c12 = coords(C, red(C, z1 * z2, 2 * val(C, z1 * z2) + 4 * mapget(C, "ej") + 8))[1];
      if ((c1 + c2) % 2 != c12, ok4 = 0); if (coords(C, red(C, z1^2, 2 * val(C, z1^2) + 4 * mapget(C, "ej") + 8))[1] != 0 * c1, ok5 = 0));
    chq(ok4 && ok5, Str("component ", j, ": coordinates additive on 4 random pairs, zero on 4 random squares")));
  stage("3 (kappa)");
  if (mapget(W, "p") == 2, listput(kap, ["alpha", 0, mapget(W, "al")]); for (i = 1, 2 * e, listput(kap, [Str("1+alpha^", i), 0, 1 + mapget(W, "al")^i])),
    chq(!issquare(nfmodpr(nfK, SBu7, mapget(W, "modpr"))), "7: u7 = -1 has a nonsquare residue in F_343"); listput(kap, ["alpha", 0, mapget(W, "al")]); listput(kap, ["u7", 0, SBu7]));
  K1 = cert_list(comps, Vec(kap), "kappa"); Akap = K1[1];
  wr(fn, "SB2_KAPPA", [apply(z -> [z[1], zk(z[3])], Vec(kap)), K1[2]]);
  printf("  dim of the image of K_w^x (kappa) in G/G^2: %d (e_w + 1 = %d); dim G/G^2 = %d\n", f2rank(Akap), e + 1, #Akap~);
  if (mapget(W, "p") == 2, chq(f2rank(Akap) == e + 1, "(ii) dim image of kappa = e_w + 1 (d is a square in every component)"));
  \\ lc(fRev k) on K_w itself (twist dependent): coordinates in K_w^x / K_w^x2 (nonzero: not a square)
  if (pi != 1, my(C0 = sb_comp(W, 1), ce = sb_cert(C0, SBc[KT + 1], "lc"));
    printf("  lc(fRev_%d) in K_w^x/K_w^x2 on [%s]: %s, m = %d\n", KT, strjoin(mapget(C0, "bnames"), ", "), ce[7], ce[8]);
    chq(ce[7] != 0, "lc(fRev_k) is not a square in K_w (nonzero coordinates, verified certificate)");
    wr(fn, "SB2_LC", concat([zk(SBc[KT + 1])], ce[1 .. 10])));
  stage("4 (points, mu)");
  D = SB_D[pi];
  if (pi == 4 && KT == 0, printf("  twist 0 at 7: not needed (the real places replace it); points skipped\n"); D = 0);
  if (D, my(sp = split_points(W, comps, Akap, D, if (pi == 4, 6000, 12000), 150000));
    if (sp[2] == D,
      musrc = "split points"; my(pts = sp[1], C0 = sb_comp(W, 1));
      ptsdat = vector(#pts, i, concat([zk(pts[i][1])], sb_cert(C0, pts[i][2], Str("f(x_", i - 1, ")"))[1 .. 10]));
      chq(vecmin(apply(r -> r[8] == 0, ptsdat)), "every f(x_i) is a square in K_w (verified square certificates, zero coordinates)");
      for (i = 2, #pts, listput(mus, [Str("mu", i - 1), 0, lift((x - pts[i][1]) * (x - pts[1][1]))])),
      musrc = "lane M4 divisors (local_images)";
      if (pi == 4, error("7: split points did not reach D"));
      my(RR = read(Str("local_images_twist", KT, "_e", e, ".bin")));
      chq(RR[1] == KT && RR[3] == e && #RR[7] == D, Str("local_images_twist", KT, "_e", e, ".bin: ", D, " divisors"));
      for (i = 1, D, my(uu = lift(Mod(1, K21) * subst(RR[7][i][1], t, x)), U = lift(Mod(1, K21) * polrecip(uu) / polcoef(uu, 0, x)));
        listput(mus, [Str("mu", i), 0, U])));
    printf("  points used: %s\n", musrc);
    R = cert_list(comps, Vec(mus), "mu"); Amu = R[1];
    wr(fn, "SB2_MU", [musrc, ptsdat, apply(m -> [m[1], apply(zk, Vec(m[3]))], Vec(mus)), R[2]]);
    chq(f2rank(matconcat([Akap, Amu])) == f2rank(Akap) + D && #Amu == D, Str("(i) the ", D, " mu are independent modulo span(kappa)"));
    printf("  dim V_w = dim span(kappa, mu) = %d, dim G/G^2 = %d\n", f2rank(matconcat([Akap, Amu])), #Akap~);
    chq(2 * f2rank(matconcat([Akap, Amu])) == #Akap~, "dim V_w = half of dim G/G^2"),
    Amu = matrix(#Akap~, 0));
  stage("5 (generators)");
  if (GENSF == "" || GENSF == 0, printf("  no generator list (SB_GENS unset): stages 5 and 6 not run\n"); printf("DONE, %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00); quit);
  gl = gens_from_lean(GENSF);
  my(keys = Vec(Mat(gl[1])[, 1]), ix = Map());
  for (i = 1, #keys, mapput(ix, keys[i], i));
  R = cert_list(comps, vector(#keys, i, my(v = mapget(gl[1], keys[i])); [keys[i], v[1], v[2]]), "generators Pgen s (tau_j)");
  Agen = R[1]; Cgen = matrix(#Akap~, 82);
  for (s1 = 1, 82, Cgen[, s1] = Agen[, mapget(ix, gl[2][s1][2][1])]);
  my(rowg = concat(vector(#comps, j, vector(#mapget(comps[j], "bas"), l, mapget(comps[j], "g")))), okf = 1);
  for (s1 = 1, 82, for (r = 1, #rowg, if (Cgen[r, s1] && (rowg[r] == "h") == (s1 <= 29), okf = 0)));
  chq(okf, "Pgen s (tau_j) has zero coordinates at the components of the other factor (Pgen s = 1 there: s < 29 at h, s >= 29 at q)");
  wr(fn, "SB2_GENS", [GENSF, gl[2], keys, R[2]]);
  stage("6 (F_2 checks at the place)");
  my(Vw = matconcat([Akap, Amu]), Q = f2annih(Vw, #Akap~), Rw = Q * Cgen % 2);
  printf("  dim V_w = %d (half of dim G/G^2 = %d), annihilator rows %d; preimage of V_w in F_2^82: dim %d\n", f2rank(Vw), #Akap~ / 2, #Q~, #f2ker(Rw, 82));
  if (D, chq(2 * f2rank(Vw) == #Akap~, "dim V_w = half of dim G/G^2"));
  chq(Rw != 0, "negative control: some generator lies outside V_w (the rows C_w are nonzero)");
  wr(fn, "SB2_ROWS", [Rw, Akap, Amu, Cgen, Q]);
  printf("  C_w rows (annihilator of V_w times generator coordinates), %d x 82: %s\n", #Rw~, Rw);
  printf("DONE, %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00);
}
quit;
