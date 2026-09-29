\\ selmer_bound_subsets.gp: Selmer upper bounds of the Prym twists F_k / K21 (k = 0, 1) from a subset S' of the local conditions,
\\ and their effect on M4's Selmer group Chabauty tests at the place v above 2 with e = 3.
\\ Places (order of p21_29 / selmer_injectivity_places.gp): 1 = v (e = 3), 2 = w2 (e = 12), 3 = w3 (e = 6), 4 = the place above 7,
\\ 5, 6, 7 = the real places.
\\ For each twist k and place set S' (containing v):
\\ (a) X' = {x in A(S,2) : res_w(x) in W_w for w in S'} (82 generator coordinates), dim X'; the Selmer upper bound
\\     X' / im K21(S,2) has dimension dim X' - 15 (im K21(S,2) has dimension 15, p21_29; it lies in X' because every
\\     W_w contains the image KM_w of K_w^x, checked below);
\\ (b) sigma_v injective on X' / im K21(S,2) iff dim {x in X' : res_v(x) in KM_v} = 15 (as selmer_injectivity_places.gp); second
\\     reading: the rank of the D basis coordinates SC' of sigma_v(X') equals dim X' - 15;
\\ (c) SC' = coordinates of res_v(G X') in the basis [c_1..c_7, KM_v] of W_v (c_i the x - T classes of the divisors of
\\     local_images_twist<k>_e3.bin, td2_coord, the code path of selmer_image_v.gp), W' = rho(sigma_v(X')) = span(RhoD SC') in
\\     Lambda/2Lambda (RhoD = rho(D_i) of p21_45, data/lattice_twist<k>.bin), pr(W') with the U, orow of p21_45, and the
\\     test "class not in pr(W')" for the 104 constant box centre classes of p21_46 (data/centres_twist<k>.txt, field 5)
\\     and the tail classes e1 of p21_45 / tails_export.gp (lattice bin, E1). Cross-check in M4's exported basis
\\     (code/covering/data: lattice_k<k>.gp Q, l, SB, W; centres_k<k>.gp; tails_k<k>.gp): classes (Q c / 4) / 2^nu mod 2,
\\     pr_M4(W') spanned by Q w / 4 mod 2 for w = sum_i SC'[i, j] l[i].
\\ Known answer checks: S' = all places gives dim X' = 19, the span of G X of selX_k<k>.bin, injectivity, the SelCoef of
\\ data/selmer_image_v_twist<k>.bin (recomputed from the stored G X), span(SC') = span(SB of M4), W' = W and pr(W') = prW of p21_45.
\\ Known solutions: the classes T, phi(x_a), phi(x_b) (local vectors LV of selX) lie in loc(X') + sum KM_w and their D basis
\\ coordinates (KnownCoef of rho_k) in span(SC'), for every S'. Negative control: S' = {v} (pr(W') must fill F_2^4).
\\ Inputs: code/local-group/selmer_injectivity_places_twist<k>.bin (G, offsets, W_w, KM_w, names), /tmp/k21c/sel/selX_k<k>.bin (G X,
\\ LV), /tmp/k21c/sel/fields.bin, places.bin (for td2_coord), code/earlier-computations/local_images_twist<k>_e3.bin, code/earlier-computations/data
\\ (rho_k, lattice_k, centres_k), code/covering/data.
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-local-conditions/selmer_bound_subsets.gp < /dev/null > ../selmer-local-conditions/selmer_bound_subsets.out 2>&1
default(parisizemax, 1200 * 10^6); default(nbthreads, 1); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp"); read("field_l42_polynomial.gp"); read("field_n84_polynomial.gp");
read("../lib/richelot.gp"); read("../lib/td2loc.gp");
read("norm_relation_lib.gp"); read("prym_two_descent_lib.gp");
NFAIL = 0;
chq(c, msg) = if (!c, NFAIL++; printf("CHECK FAILED: %s\n", msg); error("check failed: ", msg), printf("ok: %s\n", msg));
f2rank(M) = if (#M == 0, 0, matrank(Mod(M, 2)));
f2in(M, v) = f2rank(matconcat([M, v])) == f2rank(M);
f2eqspan(A1, A2) = my(r = f2rank(A1)); r == f2rank(A2) && r == f2rank(matconcat([A1, A2]));
f2img(M) = if (#M == 0, M, lift(matimage(Mod(M, 2))));
f2annih(W, n) = { if (#W == 0, return(matid(n))); my(Kr = lift(matker(Mod(W~, 2)))); if (#Kr == 0, matrix(0, n), Kr~); }
f2solve(M, c) = { my(z = matsolvemod(M, 2, c)); if (type(z) == "t_INT", return(0)); lift(Mod(z, 2)); }
rowsOf(G, offs, j, W) = { my(o = offs[j], Q = f2annih(W, o[2]), Gj = matrix(o[2], #G, r, c, G[o[1] + r, c])); Q * Gj; }
\\ basis (columns, 82 rows) of {x : res_w(G x) in Wsel[w] for w in P}
Xbasis(G, offs, Wsel, P) = {
  my(R = matrix(0, #G));
  foreach (P, j, R = matconcat([R; rowsOf(G, offs, j, Wsel[j])]));
  if (#R~ == 0, return(matid(#G)));
  lift(matker(Mod(R, 2)));
}
v2(c) = if (c == 0, oo, valuation(c, 2));
v2vec(v) = vecmin(apply(v2, Vec(v)));
red2(c, j) = {
  if (type(c) == "t_VEC" || type(c) == "t_COL" || type(c) == "t_MAT", return(apply(e -> red2(e, j), c)));
  if (denominator(c) % 2 == 0, error("red2: not 2-integral"));
  lift(Mod(numerator(c), 2^j) / denominator(c));
}
startswith(s, p) = my(A1 = Vecsmall(s), B1 = Vecsmall(p)); #A1 >= #B1 && A1[1 .. #B1] == B1;
\\ value of "nm = ...;" in a GP data file written by write()
getvar(fn, nm) = {
  my(L = readstr(fn), pre = Str(nm, " = "));
  foreach (L, s, if (startswith(s, pre), my(A1 = Vecsmall(s), e = #A1); while (A1[e] == 59 || A1[e] == 32, e--); return(eval(Strchr(A1[#pre + 1 .. e])))));
  error(Str("no ", nm, " in ", fn));
}
\\ reduced column echelon form over F_2 of the span (canonical: comparable literally)
f2canon(M) = {
  if (f2rank(M) == 0, return(matrix(#M~, 0)));
  my(E = lift(matimage(Mod(M, 2))), H2 = mathnf(matconcat([E, 2 * matid(#E~)])), cols);
  H2 = apply(e -> e % 2, H2); cols = [j | j <- [1 .. #H2], H2[, j] != 0];
  Mat(vector(#cols, i, H2[, cols[i]]));
}

\\ tool tests (known answers and negative controls), run first inside the main block
tooltests() = {
  chq(f2in([1, 0; 0, 1; 0, 0], [1, 1, 0]~) && !f2in([1, 0; 0, 1; 0, 0], [0, 0, 1]~), "tool: f2in (positive and negative)");
  chq(f2eqspan([1, 1; 0, 1; 0, 0], [1, 0; 0, 1; 0, 0]) && !f2eqspan(Mat([1, 0, 0]~), Mat([0, 1, 0]~)), "tool: f2eqspan (positive and negative)");
  chq(f2solve([1, 0; 1, 1; 0, 0], [0, 1, 0]~) == [0, 1]~ && f2solve([1, 0; 1, 1; 0, 0], [0, 0, 1]~) == 0, "tool: f2solve (solution and no solution)");
  my(Xt = Xbasis([1, 1; 1, 0], [[0, 1], [1, 1]], [matrix(1, 0), Mat([1])], [1]));
  chq(#Xt == 1 && Xt == Mat([1, 1]~), "tool: Xbasis on a 2 x 2 example (kernel of x1 + x2 = 0)");
  chq(f2canon([1, 1; 1, 0; 0, 0]) == f2canon([0, 1; 1, 1; 0, 0]) && f2canon([1, 1; 1, 0; 0, 0]) != f2canon([1, 0; 0, 0; 0, 1]), "tool: f2canon is basis free and separates spans");
  chq(red2(3/5, 3) == 7 && v2vec([4, 0, 8]) == 2 && startswith("SB = [1]", "SB = ") && !startswith("SBx", "SB ="), "tool: red2, v2vec, startswith");
}

SETS = [[1, 2, 3, 4, 5, 6, 7], [1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 3, 6], [1, 2, 3, 7], [1, 2, 3, 5, 6, 7], [1, 2, 3, 5, 6], [1, 2, 3, 6, 7], [1, 2, 3, 5, 7], [1, 2, 3], [1]];

run(k, A, fin) = {
  my(t0 = getabstime(), D = read(Str("../local-group/selmer_injectivity_places_twist", k, ".bin")), G = D[1], offs = D[2], locs = D[3], KMs = D[4], nms = D[5],
     S = read(Str(SEL, "selX_k", k, ".bin")), GX = S[1], KMbar = S[2], LV = S[3], RC = read(Str("data/selmer_image_v_twist", k, ".bin")), SC0 = RC[2], KC = RC[3],
     Lt = read(Str("data/lattice_twist", k, ".bin")), RhoD = mapget(Lt, "RhoD"), UL = mapget(Lt, "U"), orow = mapget(Lt, "orow"), prW0 = mapget(Lt, "prW"),
     W0 = mapget(Lt, "W"), E1 = mapget(Lt, "E1"), CEN = readvec(Str("data/centres_twist", k, ".txt")),
     fl = Str("../covering/data/lattice_int_twist", k, ".gp"), SBm = getvar(fl, "SB"), Qm = getvar(fl, "Q"), lm = getvar(fl, "l"), Wm = getvar(fl, "W"),
     CENm = readvec(Str("../covering/data/centres_int_twist", k, ".gp")), TAILm = readvec(Str("../covering/data/tails_int_twist", k, ".gp")),
     R, P, Cv, B, np = #offs, prj, clsA, clsB, prjM, res = List());
  printf("==== twist k = %d\n", k);
  \\ layout
  chq(S[4] == offs && S[5] == locs && S[6] == KMs && S[7] == nms, "selmer_injectivity_places equals the offsets, local images, K_v^x images and names of selX_k");
  chq(#G == 82 && #G~ == 164 && np == 7 && offs[np][1] + offs[np][2] == 164, "G is 164 x 82, seven places");
  for (j = 1, np, printf("  place %d: %s, offset %s, dim W_w = %d, dim KM_w = %d\n", j, if (j <= #nms, nms[j], "real"), offs[j], f2rank(locs[j]), f2rank(KMs[j])));
  chq(offs[1][2] == 22 && nms[1] == mapget(fin[1], "name") && mapget(fin[1], "pr").e == 3 && mapget(fin[2], "pr").e == 12 && mapget(fin[3], "pr").e == 6 && mapget(fin[4], "pr").p == 7,
      "place 1 = v (e = 3), 2 = e 12, 3 = e 6, 4 = above 7");
  for (j = 1, np, chq(f2rank(matconcat([locs[j], KMs[j]])) == f2rank(locs[j]), Str("KM_w is contained in W_w at place ", j)));
  \\ the D basis at v
  P = fin[1];
  R = read(Str("local_images_twist", k, "_e3.bin")); chq(R[1] == k && R[3] == 3 && R[6] == 1 && #R[7] == 7, "complete J side run at e = 3, 7 divisors");
  Cv = Mat(vector(7, i, td2_coord(A, P, R[7][i][1])));
  B = matconcat([Cv, KMs[1]]);
  chq(f2rank(B) == 7 + f2rank(KMs[1]) && #KMs[1] == f2rank(KMs[1]), "c_1..c_7, KM_v independent");
  chq(f2eqspan(B, locs[1]), "span(c_1..c_7, KM_v) = W_v");
  printf("  c_i (x - T coordinates at v of D_1..D_7, columns): %s\n", Cv);
  my(coef = (M -> my(Cf = matrix(7, #M)); for (c = 1, #M, my(zz = f2solve(B, vector(22, r, M[r, c])~)); if (type(zz) == "t_INT", return(0)); for (i = 1, 7, Cf[i, c] = zz[i])); Cf));
  my(SCchk = coef(GX)); chq(type(SCchk) == "t_MAT" && SCchk == SC0, "SelCoef recomputed from the stored G X equals data/selmer_image_v_twist (7 x 19)");
  \\ pr in the basis of p21_45 and in M4's basis
  prj = (vv -> my(c = UL * vv); vector(4, i, c[orow[i]])~);
  chq(f2eqspan(f2img(Mat(vector(#W0, j, prj(W0[, j])))), prW0), "pr(W) of p21_45 recomputed from its W");
  chq(f2eqspan(red2(RhoD * SC0, 1), W0), "W of p21_45 = span(RhoD SelCoef)");
  clsA = List(); foreach (CEN, c, chq(c[6] == 0, Str("stored: centre ", c[1 .. 3], " outside pr(W)")); listput(clsA, [Str("centre ", c[1 .. 3]), c[5]~]));
  foreach (E1, e, chq(e[4] == 0, Str("stored: tail x_", e[1], " outside pr(W)")); listput(clsA, [Str("tail x_", e[1]), e[3]~]));
  chq(#CEN == if (k == 0, 82, 22) && #E1 == 2, "82 + 22 centres and 2 + 2 tails");
  \\ M4's basis: centres [disc, X0, level, nu, vM, c, q], tails [i, c, q, nu]
  prjM = (vv -> Qm * vv / 4);
  clsB = List();
  chq(#CENm == #CEN, "lane M4 has the same number of centres");
  for (i = 1, #CENm, my(cm = CENm[i], yv = prjM(cm[6]~), nu = v2vec(yv), ca = [c | c <- CEN, c[1 .. 3] == cm[1 .. 3]]);
    chq(#ca == 1 && ca[1][4] == cm[4] && nu == cm[4], Str("M4 centre ", cm[1 .. 3], ": nu from Q c / 4 = stored nu = p21_46 nu"));
    listput(clsB, [Str("centre ", cm[1 .. 3]), red2(yv / 2^nu, 1)]));
  foreach (TAILm, tm, my(yv = prjM(tm[2]~), nu = v2vec(yv), ea = [e | e <- E1, e[1] == tm[1]]);
    chq(#ea == 1 && ea[1][2] == tm[4] && nu == tm[4], Str("M4 tail x_", tm[1], ": nu from Q c / 4 = stored nu = p21_45 nu"));
    listput(clsB, [Str("tail x_", tm[1]), red2(yv / 2^nu, 1)]));
  my(prWm = f2img(Mat(vector(#Wm, m, red2(prjM(Wm[m]), 1)))));
  chq(f2rank(prWm) == 1, "lane M4's pr(W) (from its 16 vectors W) has dimension 1");
  foreach (clsB, c, chq(!f2in(prWm, c[2]), Str("M4 basis: ", c[1], " outside lane M4's pr(W)")));
  \\ the place sets
  foreach (SETS, Sp,
    my(Xs = Xbasis(G, offs, locs, Sp), dX = #Xs, GXp = G * Xs % 2, Wk = locs, dK, SCp, rS, Wp, prWp, failA, failB, prWpm, known, knownD, same, Wpm);
    printf("  ---- S' = %s\n", Sp);
    Wk[1] = KMs[1]; dK = #Xbasis(G, offs, Wk, Sp);
    SCp = coef(GXp); chq(type(SCp) == "t_MAT", "res_v(G X') lies in W_v");
    rS = f2rank(SCp);
    known = vecmin(vector(#LV, q, f2in(matconcat([GXp, KMbar]), LV[, q])));
    knownD = vecmin(vector(#KC, q, f2in(SCp, KC[, q])));
    Wp = f2img(red2(RhoD * SCp, 1)); prWp = f2img(Mat(vector(#Wp, j, prj(Wp[, j]))) % 2);
    Wpm = vector(#SCp, j, sum(i = 1, 7, SCp[i, j] * lm[i]));
    prWpm = f2img(Mat(vector(#Wpm, j, red2(prjM(Wpm[j]), 1))));
    failA = [c[1] | c <- Vec(clsA), f2in(prWp, c[2])];
    failB = [c[1] | c <- Vec(clsB), f2in(prWpm, c[2])];
    printf("  (a) dim X' = %d, Selmer upper bound dim X' - 15 = %d\n", dX, dX - 15);
    printf("  (b) dim {x in X' : res_v x in KM_v} = %d (15 means injective); rank of sigma_v(X') in the D basis = %d; injective: %d\n", dK, rS, dK == 15 && rS == dX - 15);
    chq((dK == 15) == (rS == dX - 15) && dX - dK == rS, "the two readings of (b) agree");
    printf("      known classes T, phi_a, phi_b: in loc(X') + sum KM_w %d, D coordinates in span(SC') %d\n", known, knownD);
    chq(known && knownD, "the known global classes survive S'");
    printf("      span of sigma_v(X') in the D basis (reduced echelon columns): %s\n", f2canon(SCp));
    printf("  (c) dim W' (in Lambda/2Lambda) = %d, dim pr(W') = %d, pr(W') basis (p21_45 coordinates) %s; lane M4 basis: dim pr_M4(W') = %d\n",
           f2rank(Wp), f2rank(prWp), f2canon(prWp), f2rank(prWpm));
    printf("      classes in pr(W') (should be outside): p21_45 basis %d of %d, lane M4 basis %d of %d\n", #failA, #clsA, #failB, #clsB);
    chq(Set(failA) == Set(failB), "both bases give the same failing classes");
    if (#failA, printf("      FAILING: %s\n", failA));
    if (Sp == [1 .. 7],
      chq(dX == 19 && f2eqspan(GXp, GX), "KAT: all places give dim X = 19 and the span of the stored G X");
      chq(dK == 15 && rS == 4, "KAT: all places give an injective sigma_v on a 4 dimensional Selmer bound");
      chq(f2eqspan(SCp, SC0) && f2eqspan(SCp, SBm) && f2canon(SCp) == f2canon(SBm), "KAT: span(SC') = span(SelCoef) = span(SB of lane M4)");
      chq(SBm == f2img(SC0), "KAT: lane M4's SB = matimage(SelCoef)");
      my(Wcl = f2img(Mat(vector(#Wm, m, red2(getvar(fl, "G") * Wm[m] / 4, 1)))));
      chq(f2eqspan(Wp, W0) && f2eqspan(Wp, Wcl), "KAT: W' = W of p21_45 = the classes in Lambda/2Lambda of lane M4's 16 vectors W");
      chq(f2eqspan(prWp, prW0) && #failA == 0, "KAT: pr(W') = prW of p21_45, every class outside"));
    if (Sp == [1], chq(#failA > 0, "negative control: with S' = {v} the test reports classes in pr(W')"));
    listput(res, [Sp, dX, dX - 15, dK == 15 && rS == dX - 15, f2rank(Wp), f2rank(prWp), #failA]));
  \\ (d) where the place above 7 acts, for S' = {v, w2, w3, 5, 6, 7}: the class of res_7(X') modulo W_7, and the
  \\ dimension of X' cut by the valuation parity part only, resp. the unit square class part only, of the condition at 7
  \\ (coordinates at 7: per prime of the factor fields above 7, [v mod 2, unit bits], td2_sqcoord)
  my(S6 = [1, 2, 3, 5, 6, 7], X6 = Xbasis(G, offs, locs, S6), Xa = Xbasis(G, offs, locs, [1 .. 7]), o7 = offs[4], sq7 = mapget(fin[4], "sq"), vrow = List(), urow = List(), pos = 0);
  for (j = 1, #sq7, listput(vrow, pos + 1); for (i = 1, #sq7[j][4], listput(urow, pos + 1 + i)); pos += 1 + #sq7[j][4]);
  chq(pos == o7[2], "coordinates at 7: blocks [v mod 2, unit bits] per prime");
  vrow = Vec(vrow); urow = Vec(urow);
  my(res7 = (M, rr) -> matrix(#rr, #M, i, c, M[o7[1] + rr[i], c]), W7 = locs[4], cut, X6v, X6u, extra);
  cut = (rr -> my(Wp7 = matrix(#rr, #W7, i, c, W7[rr[i], c]), Q7 = f2annih(Wp7, #rr)); if (#Q7~ == 0, return(#X6)); my(Rw = Q7 * res7(G * X6 % 2, rr)); #X6 - f2rank(Rw));
  X6v = cut(vrow); X6u = cut(urow);
  printf("  (d) S' = %s: dim X' = %d (all places: %d); X' with the valuation parity part of the condition at 7: %d; with the unit part: %d\n", S6, #X6, #Xa, X6v, X6u);
  printf("      valuation rows at 7 %s, unit rows %s (block sizes %s)\n", vrow, urow, vector(#sq7, j, 1 + #sq7[j][4]));
  extra = [c | c <- [1 .. #X6], !f2in(matconcat([Xa, X6[, 1 .. c - 1]]), X6[, c])];
  printf("      %d basis vectors of X' outside X_all; res_7 of each (10 coordinates): %s; W_7 (columns): %s\n", #extra,
         vector(#extra, i, ((G * X6[, extra[i]]) % 2)[o7[1] + 1 .. o7[1] + o7[2]]~), W7);
  printf("  twist %d summary [S', dim X', bound, injective, dim W', dim pr(W'), classes in pr(W')]:\n", k);
  foreach (res, r1, printf("    %s\n", r1));
  printf("  (%d ms)\n", getabstime() - t0);
}
{
  tooltests();
  my(t0 = getabstime(), FF = sel_fields(), AA = [sel_alg(FF, 0), sel_alg(FF, 1)], PL = sel_places(AA[1]), fin = PL[1]);
  printf("fields, algebras, places loaded (%d ms)\n", getabstime() - t0);
  for (k = 0, 1, run(k, AA[k + 1], fin));
  printf("DONE, %d failed checks (%d ms)\n", NFAIL, getabstime() - t0);
}
quit;
