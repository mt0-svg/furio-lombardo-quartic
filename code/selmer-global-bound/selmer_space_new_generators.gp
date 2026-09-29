\\ selmer_space_new_generators.gp: the Selmer space on the new generators, the vectors
\\ beta_j of RelAtV, kappa_t, and the checks of a_T.
\\ Coordinates: those of p21_29 (td2loc square class coordinates at the 4 finite places of S and signs at the 3 real
\\ places; fields and places rebuilt by field_caches.gp; A_k = K21[x]/(f_k) = nfL x nfN). The algebra of the Lean side
\\ is K21[T]/(fRev k) = L42 x N84 (T -> (alpha, beta)); T -> 1/x and iotaL, iotaN of sb_5a (alpha -> 1/thL,
\\ beta -> 1/thN) identify the two, so an element (y1, y2) of L42 x N84 has the coordinates of (iotaL y1, iotaN y2)
\\ (computed through MTL, MTN of sb_5a).
\\ (1) The place v and M4Cert.sigma: the primes of K21 above 2 have local degrees e f = 3, 12, 6, so an embedding of K21
\\     into the cubic field K_v = Q_2[x]/(E) of M4Cert/Kv.lean has kernel prime pr_v (e = 3), and extends to an
\\     isomorphism of the completion at pr_v onto K_v; checked also numerically: v_pi(sigma(z)) = v_(pr_v)(z) for the
\\     generators of the three primes and other elements, with sigma(theta) ~ theta0 (M4Cert/Data.lean). So a class
\\     relation at sigma is a relation in the coordinates at pr_v (place 1 of p21_29).
\\ (2) The coordinate system is that of p21_29: the offsets and the images KM_w of K_w^x equal those stored in
\\     code/local-group/selmer_injectivity_places_twist<k>.bin (which also holds the old generator matrix G_old and the local images W_w).
\\ (3) G_new (164 x 82): coordinates of the 29 + 53 new generators; rank 82, span(G_new) = span(G_old), G_new = G_old C.
\\ (4) X = {x : res_w(G_new x) in W_w for every place w}, dim 19, and C X = X_old (X_old from G_old): the same Selmer
\\     space under the change of generators.
\\ (5) The D basis at v in the order of Dpt (lean/FurioLombardo/Discharge/SelmerSpan/Dpt.lean): c_i = the coordinates
\\     at v of (U_i(alpha), U_i(beta)), U_i = T^2 + p_i T + r_i with p_i, r_i of DData.lean (Dpt's quad); checked equal
\\     modulo KM_v to the x - T classes of the divisors of local_images_twist<k>_e3.bin (p_i = u1/u0, r_i = 1/u0 checked),
\\     and span(c_0..c_6, KM_v) = W_v. SC = coordinates of res_v(G_new X) in this basis; span(SC) = span(SB),
\\     SB = T_k.data.SB (lean/FurioLombardo/M4/Data.lean). beta_j in X with res_v(G_new beta_j) = sum_i SB_ij c_i
\\     modulo KM_v: the coordinate form of RelAtV at sigma (H = A^x / K^x A^x2 of M3a/XminusT.lean). beta_j is unique
\\     modulo {x in X : res_v(G_new x) in KM_v} = span(kappa) (checked); the one of least weight is taken.
\\ (6) kappa_t (t = 0..15): the classes of (c, c), c = gO t of M1 (-1, 11 units, la, lb, lc, pi7), on the
\\     generators, from the residue characters of sb_5d; checked by exact square roots (c prod gensL^a, c prod gensN^b
\\     squares in L42, N84) and by the local coordinates (G_new kappa_t = loc(c, c)). dim span(kappa) = 15 (the relation
\\     is the class of eps, a square in L42 = K21(sqrt eps), checked exactly), kappa_t in X, kappa_t trivial at every
\\     place modulo KM_w, and span(beta) + span(kappa) = X.
\\ (7) a_T of sb_5t: a_T in X and G_new a_T = loc(x1 / kappa, x2 / kappa). Known classes T, phi(x_i) of p21_29 in
\\     loc(X) + sum KM_w, and T of p21_29 (unreversed model) = loc(x1 / kappa, x2 / kappa) modulo sum KM_w.
\\ Output cache /tmp/sb5/selmer.bin (read by sunit_export.gp). Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/selmer_space_new_generators.gp < /dev/null > ../selmer-global-bound/selmer_space_new_generators.out 2>&1
default(parisizemax, 1700 * 10^6); default(nbthreads, 1); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp"); read("field_l42_polynomial.gp"); read("field_n84_polynomial.gp");
read("../lib/richelot.gp"); read("../lib/td2loc.gp");
read("norm_relation_lib.gp"); read("prym_two_descent_lib.gp");
read("phi_known_lifts.gp");
read("../selmer-global-bound/tower_lib.gp");
DIR = "/tmp/sb5/nr/"; SEL = "/tmp/sb5/sel/";
LEAN = "../../FurioLombardo/";
DATA = "../selmer-global-bound/sunit_generators_data.gp";
OUT = "/tmp/sb5/selmer.bin";

f2rank(M) = if (#M == 0, 0, matrank(Mod(M, 2)));
f2in(M, v) = f2rank(matconcat([M, v])) == f2rank(M);
f2eqspan(A1, A2) = my(r = f2rank(A1)); r == f2rank(A2) && r == f2rank(matconcat([A1, A2]));
f2solve(M, c) = { my(z = matsolvemod(M, 2, c)); if (type(z) == "t_INT", return(0)); lift(Mod(z, 2)); }
rowsOf(G, offs, j, W) = { my(o = offs[j], Q = f2annih(W, o[2]), Gj = matrix(o[2], #G, r, c, G[o[1] + r, c])); Q * Gj; }
Xbasis(G, offs, Wsel, P) = {
  my(R = matrix(0, #G));
  foreach (P, j, R = matconcat([R; rowsOf(G, offs, j, Wsel[j])]));
  if (#R~ == 0, return(matid(#G)));
  lift(matker(Mod(R, 2)));
}
rowblock(M, o) = matrix(o[2], #M, r, c, M[o[1] + r, c]);
\\ pi-adic valuation in K_v = Q_2[x]/(E) (E Eisenstein cubic, pi = x) of g(theta) at theta = th0, for g in Z[b], from
\\ its value modulo 2^Nw: the minimum over the coordinates c_j on 1, pi, pi^2 of 3 v_2(c_j) + j (3 Nw if all vanish)
vpi(g, th0, E, Nw) = { my(v = lift(lift(subst(lift(g), 'b, Mod(Mod(1, 2^Nw) * th0, E)))), m = 3 * Nw); for (j = 0, 2, my(c = polcoef(v, j)); if (c, m = min(m, 3 * valuation(c, 2) + j))); m; }
intK(g) = g * denominator(content(lift(g)));
tooltests() = {
  chk5(f2in([1, 0; 0, 1; 0, 0], [1, 1, 0]~) && !f2in([1, 0; 0, 1; 0, 0], [0, 0, 1]~), "tool: f2in (positive and negative)");
  chk5(f2eqspan([1, 1; 0, 1; 0, 0], [1, 0; 0, 1; 0, 0]) && !f2eqspan(Mat([1, 0, 0]~), Mat([0, 1, 0]~)), "tool: f2eqspan (positive and negative)");
  chk5(f2solve([1, 0; 1, 1; 0, 0], [0, 1, 0]~) == [0, 1]~ && f2solve([1, 0; 1, 1; 0, 0], [0, 0, 1]~) == 0, "tool: f2solve (solution, and no solution)");
  chk5(Xbasis([1, 1; 1, 0], [[0, 1], [1, 1]], [matrix(1, 0), Mat([1])], [1]) == Mat([1, 1]~) && #Xbasis([1, 1; 1, 0], [[0, 1], [1, 1]], [Mat([1]), Mat([1])], [1, 2]) == 2,
       "tool: Xbasis on a 2 x 2 example (kernel of x1 + x2 = 0; no condition when W is everything)");
  chk5(vpi(2, 'x, 'x^3 + 2, 20) == 3 && vpi('b, 'x, 'x^3 + 2, 20) == 1 && vpi('b^2 + 4, 'x, 'x^3 + 2, 20) == 2 && vpi(0, 'x, 'x^3 + 2, 20) == 60, "tool: vpi in Q_2(2^(1/3)) (v(2) = 3, v(pi) = 1, v(pi^2 + 4) = 2, v(0) = 3 Nw)");
}

main() = {
  my(t0 = getabstime(), FF, AA, PL, fin, re, TW, GN, MU, CH, nfL, nfN, MTL, MTN, genL, genN, toL, toN, Gn, Go, Cm, res = vector(2),
     zkNum = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"), Dz = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz"));
  tooltests();
  FF = sel_fields(); AA = [sel_alg(FF, 0), sel_alg(FF, 1)]; PL = sel_places(AA[1]); fin = PL[1]; re = PL[2];
  nfK = FF[1]; nfL = FF[2]; nfN = FF[3];
  TW = read("/tmp/sb5/tower.bin"); GN = sb5_gens(DATA); MU = read("/tmp/sb5/muT.bin"); CH = read("/tmp/sb5/chars.bin");
  EPS = TW[1]; EN = TW[2]; MTL = TW[16]; MTN = TW[18];
  chk5(vector(21, j, Pol(Vecrev(zkNum[j]), 'b) / Dz) == nfK.zk, "nfK of fields.bin has lane M1's integral basis zkNum / Dz");
  genL = apply(g -> g[1], GN[1]); genN = apply(g -> Nunfmt(g[1]), GN[2]);
  toL = (xl -> MTL * concat(xl[1], xl[2]));
  toN = (xn -> MTN * concat(Nfmt(xn)));
  printf("fields, algebras, places, caches loaded (%d ms)\n", getabstime() - t0);
  \\ ---- (1) the place v and sigma
  my(P2 = idealprimedec(nfK, 2), Pv = mapget(fin[1], "pr"), KV = Str(LEAN, "Discharge/M4Cert/Kv.lean"), E, th0, okv = 1, vl = List());
  printf("primes of K21 above 2: [e, f] = %s\n", apply(P -> [P.e, P.f], P2));
  chk5(#P2 == 3 && #[P | P <- P2, P.e * P.f <= 3] == 1 && Pv.p == 2 && Pv.e == 3 && Pv.f == 1, "exactly one prime of K21 above 2 has local degree <= 3 = [K_v : Q_2]: pr_v (e = 3, f = 1), the place 1 of p21_29");
  E = 'x^3 + leandef5(KV, "e2") * 'x^2 + leandef5(KV, "e1") * 'x + leandef5(KV, "e0");
  th0 = leandef5(Str(LEAN, "Discharge/M4Cert/Data.lean"), "θ0", "", 1); th0 = th0[1] + th0[2] * 'x + th0[3] * 'x^2;
  chk5(polisirreducible(E) && valuation(polcoef(E, 0), 2) == 1 && valuation(polcoef(E, 1), 2) >= 1 && valuation(polcoef(E, 2), 2) >= 1, "E of M4Cert/Kv.lean is Eisenstein at 2");
  chk5(vpi(K21, th0, E, 60) >= 120 && vpi(K21, th0 + 1, E, 60) < 120, "v_pi(fL(theta0)) >= 120 (theta0 approximates a root of fL in K_v; negative control theta0 + 1)");
  foreach (concat([concat(apply(P -> nfbasistoalg(nfK, P.gen[2]), P2), [Mod(2, K21), Mod(7, K21)]), vector(6, i, nfbasistoalg(nfK, vectorv(21, j, random(7) - 3)))]), g,
    my(gi = intK(g), vp = vpi(gi, th0, E, 60), vv = nfeltval(nfK, gi, Pv)); listput(vl, vv); if (vp != vv, okv = 0));
  printf("  v_(pr_v) of the test elements: %s\n", Vec(vl));
  chk5(okv && vecmax(Vec(vl)) >= 3, "v_pi(sigma(z)) = v_(pr_v)(z) for the generators of the 3 primes above 2, for 2, 7 and 6 random elements (sigma(theta) ~ theta0): sigma is the embedding at pr_v");
  \\ ---- (2) the coordinate system of ss_1_data
  my(SD = vector(2, k, read(Str("../local-group/selmer_injectivity_places_twist", k - 1, ".bin"))), offs = List(), okc = 1, off = 0);
  foreach (fin, P, listput(offs, [off, mapget(P, "N")]); off += mapget(P, "N"));
  foreach (re, rp, my(m = #rp[2] + #rp[3]); listput(offs, [off, m]); off += m);
  offs = Vec(offs);
  for (k = 1, 2, if (SD[k][2] != offs, okc = 0);
    for (j = 1, #fin, if (!f2eqspan(SD[k][4][j], mapget(fin[j], "KM")), okc = 0)));
  chk5(okc && off == 164 && offs[1] == [0, 22] && SD[1][1] == SD[2][1], "the offsets equal and the images KM_w of K_w^x at the 4 finite places span the same spaces as those of selmer_injectivity_places0, k1 (p21_29); 164 coordinates, place v first (22 coordinates); G_old is the same for both twists");
  Go = SD[1][1];
  \\ ---- (3) G_new
  my(tg = getabstime(), cols = vector(82));
  for (s = 1, 82, cols[s] = if (s <= 29, sel_loccol(AA[1], fin, re, 1, toL(genL[s])), sel_loccol(AA[1], fin, re, 2, toN(genN[s - 29]))) % 2;
    if (s % 20 == 0, printf("  G_new: %d columns (%d ms)\n", s, getabstime() - tg)));
  Gn = matconcat(cols);
  printf("G_new: %d x %d (%d ms)\n", #Gn~, #Gn, getabstime() - tg);
  chk5(matsize(Gn) == [164, 82] && f2rank(Gn) == 82, "G_new is 164 x 82 of rank 82");
  chk5(f2eqspan(Gn, Go), "span(G_new) = span(G_old) (the image of A(S,2) under the local coordinates)");
  Cm = matrix(82, 82); for (s = 1, 82, my(zz = f2solve(Go, Gn[, s])); if (zz == 0, error("G_new column outside span(G_old)")); Cm[, s] = zz);
  chk5((Go * Cm - Gn) % 2 == 0 && f2rank(Cm) == 82, "G_new = G_old C with C invertible over F_2");
  chk5(genL[29] == [Kc(-1), Kc(0)] && Gn[, 29] == Go[, 29], "gL 28 = -1 and its column equals column 28 of G_old (the class of -1 in L of p21_29): a known answer of the coordinate map");
  printf("  columns of C that are unit vectors (generators with the same class as an old one): %d\n", #[s | s <- [1 .. 82], vecsum(Cm[, s]) == 1]);
  \\ ---- (6) kappa_t: M1's generators gO 0..15 and the characters of sb_5d
  my(gO = leandef5(Str(LEAN, "M1/DataGens.lean"), "gensL"), rhozk = ((p, tt) -> vector(21, j, Mod(subst(Pol(Vecrev(zkNum[j]), 'b), 'b, tt), p) / Dz)),
     rhoK = ((rz, c) -> sum(j = 1, 21, c[j] * rz[j])), CL = CH[3][1], CN = CH[3][2], kap = matrix(82, 16), tk = getabstime(), okk = 0, oks = 0);
  chk5(#gO == 18 && gO[1] == concat([-1], vector(20)), "M1's gensL: 18 generators, the first is -1");
  chk5(CL[3] == matrix(29, 29, j, s, bittest(CL[1][j], s - 1)) && CN[3] == matrix(53, 53, j, s, bittest(CN[1][j], s - 1)) && f2rank(CL[3]) == 29 && f2rank(CN[3]) == 53,
       "the character matrices of sb_5d agree with the rows RL, RN and are invertible");
  for (tt = 1, 16, my(c = KofList(gO[tt]), bl, bn, aL, aN, prL = [Kc(1), Kc(0)], prN = NofK(1), lc);
    bl = vectorv(29, j, my(d = CL[2][j], v = rhoK(rhozk(d[1], d[2]), c)); if (v == 0, error("zero residue")); kronecker(lift(v), d[1]) == -1);
    bn = vectorv(53, j, my(d = CN[2][j], v = rhoK(rhozk(d[1], d[2]), c)); if (v == 0, error("zero residue")); kronecker(lift(v), d[1]) == -1);
    aL = lift(Mod(CL[3], 2)^(-1) * Mod(bl, 2)); aN = lift(Mod(CN[3], 2)^(-1) * Mod(bn, 2));
    for (s = 1, 29, if (aL[s], prL = Lmul(prL, genL[s]))); for (s = 1, 53, if (aN[s], prN = Nmul(prN, genN[s])));
    if (Lsqrt(Lsc(c, prL)) != 0 && Nsqrt(Nsc(c, prN)) != 0, oks++);
    kap[, tt] = concat(aL, aN);
    lc = (sel_loccol(AA[1], fin, re, 1, toL([c, Kc(0)])) + sel_loccol(AA[1], fin, re, 2, toN(NofK(c)))) % 2;
    if ((Gn * kap[, tt] - lc) % 2 == 0, okk++));
  chk5(oks == 16, "kappa_t (t = 0..15): c prod gensL^a and c prod gensN^b are squares in L42, N84 (exact square roots)");
  chk5(okk == 16, "kappa_t (t = 0..15): G_new kappa_t = loc(c, c)");
  my(kb = kap[, 2]); kb[1] = 1 - kb[1];
  my(prb = [Kc(1), Kc(0)]); for (s = 1, 29, if (kb[s], prb = Lmul(prb, genL[s])));
  chk5(Lsqrt(Lsc(KofList(gO[2]), prb)) == 0, "negative control: kappa_1 with bit 0 flipped leaves no square root in L42");
  printf("  kappa: %d ms\n", getabstime() - tk);
  my(rk = f2rank(kap), rel = lift(matker(Mod(kap, 2))), pe = Kc(1));
  chk5(rk == 15 && #rel == 1, "dim span(kappa_0..kappa_15) = 15, one relation");
  printf("  the relation among the kappa_t: %s\n", rel[, 1]~);
  for (tt = 1, 16, if (rel[tt, 1], pe = Km(pe, KofList(gO[tt]))));
  chk5(#Ksqrts(Km(EPS, pe)) == 2 && #Ksqrts(pe) == 0, "the relation is the class of eps: eps prod gO^rel is a square in K21, prod gO^rel is not");
  \\ ---- (4) X, per twist; (5) D basis and beta; (7) a_T and the known classes
  my(DD = Str(LEAN, "Discharge/SelmerSpan/DData.lean"), pD = leandef5(DD, "pData"), rD = leandef5(DD, "rData"), pM = leandef5(DD, "pDen"), rM = leandef5(DD, "rDen"),
     al = TW[7], be = TW[8], P = fin[1], ov = offs[1], KMbar = vector(2));
  chk5(#pD == 2 && #pD[1] == 7 && #pD[2] == 7 && #rD[1] == 7 && #pM[2] == 7 && #rM[2] == 7, "DData.lean: 2 x 7 entries of pData, rData, pDen, rDen");
  for (k = 1, 2,
    my(A = AA[k], D = SD[k], locs = D[3], KMs = D[4], Xn, Xo, R, Cv, Cd, B, SBk, SC, bet, okb = 1, fnli = Str("local_images_twist", k - 1, "_e3.bin"), aT, GX, Rv = rowblock(Gn, ov), okr = 1);
    printf("---- twist k = %d\n", k - 1);
    Xn = Xbasis(Gn, offs, locs, [1 .. #offs]); Xo = Xbasis(Go, offs, locs, [1 .. #offs]);
    chk5(#Xn == 19 && #Xo == 19, "dim X = 19 on the new and on the old generators");
    chk5(f2eqspan(Gn * Xn % 2, Go * Xo % 2) && f2eqspan(Cm * Xn % 2, Xo), "C X_new = X_old: the Selmer space of p21_29 under the change of generators");
    \\ D basis at v
    R = read(fnli); chk5(R[1] == k - 1 && R[2] == 1 && R[3] == 3 && R[6] == 1 && #R[7] == 7, Str(fnli, ": complete J side run at e = 3, 7 divisors"));
    for (i = 1, 7, my(uu = td2_Kx(nfK, R[7][i][1]), u0 = polcoef(uu, 0, 'x), u1 = polcoef(uu, 1, 'x));
      if (pollead(uu) != 1 || poldegree(uu, 'x) != 2 || u0 == 0, okr = 0; next);
      if (nfalgtobasis(nfK, u1 / u0) != KofList(pD[k][i]) / pM[k][i] || nfalgtobasis(nfK, 1 / u0) != KofList(rD[k][i]) / rM[k][i], okr = 0));
    chk5(okr, "DData.lean: p_i = u1 / u0, r_i = 1 / u0 for the monic u_i = x^2 + u1 x + u0 of the 7 divisors, in the order of Dpt (i = 0..6)");
    Cv = matconcat(vector(7, i, td2_coord(A, P, R[7][i][1])));
    Cd = matrix(22, 7); my(nz = 1);
    for (i = 1, 7, my(p = KofList(pD[k][i]) / pM[k][i], r = KofList(rD[k][i]) / rM[k][i], UL = Ladd(Ladd(Lmul(al, al), Lsc(p, al)), [r, Kc(0)]), UN = Nadd(Nadd(Nmul(be, be), Nsc(p, be)), NofK(r)));
      if (Lis0(UL) || Nis0(UN), nz = 0; next);
      Cd[, i] = td2_coordvals(A, P, [toL(UL), toN(UN)]));
    chk5(nz && vecmin(vector(7, i, f2in(KMs[1], (Cd[, i] - Cv[, i]) % 2))), "U_i(alpha), U_i(beta) are nonzero, and their coordinates at v (DData.lean, reversed model) equal those of the divisors of p21_21 modulo KM_v (i = 0..6)");
    chk5(!f2in(KMs[1], (Cd[, 1] - Cv[, 2]) % 2), "negative control: c_0 differs from the class of divisor 1 modulo KM_v");
    B = matconcat([Cd, KMs[1]]);
    chk5(f2rank(B) == 7 + f2rank(KMs[1]) && f2eqspan(B, locs[1]), "c_0..c_6 (Dpt order) and KM_v are independent and span W_v");
    SBk = leandef5(Str(LEAN, "M4/Data.lean"), "SB", Str("namespace T", k - 1));
    chk5(matsize(SBk) == [7, 4] && vecmin(apply(e -> e == 0 || e == 1, concat(Vec(SBk)))), Str("T", k - 1, ".data.SB of M4/Data.lean: 7 x 4, entries 0, 1"));
    printf("  SB = %s\n", SBk);
    GX = Gn * Xn % 2;
    SC = matrix(7, 19); for (c = 1, 19, my(zz = f2solve(B, rowblock(GX, ov)[, c])); if (zz == 0, error("res_v outside W_v")); for (i = 1, 7, SC[i, c] = zz[i]));
    chk5(f2rank(SC) == 4 && f2eqspan(SC, SBk), "the images at v of X in the D basis (7 x 19, rank 4) span the columns of SB");
    bet = matrix(82, 4);
    for (j = 1, 4, my(zz = f2solve(SC, SBk[, j])); if (zz == 0, error("SB column not attainable")); bet[, j] = Xn * zz % 2);
    \\ beta_j is determined modulo {x in X : res_v(G_new x) in KM_v}; this space is span(kappa) (dim 15, checked);
    \\ take the element of least weight of beta_j + span(kappa) (Gray code over a basis of span(kappa))
    my(KB = f2span(kap), w0 = vector(4, j, vecsum(bet[, j])));
    chk5(#KB == 15 && f2eqspan(Xn * lift(matker(Mod(matconcat([rowblock(GX, ov), KMs[1]]), 2)))[1 .. 19, ] % 2, KB), "{x in X : res_v(G_new x) in KM_v} = span(kappa) (dim 15)");
    for (j = 1, 4, my(cur = bet[, j], best = bet[, j], bw = vecsum(bet[, j]));
      for (i = 1, 2^15 - 1, cur = (cur + KB[, valuation(i, 2) + 1]) % 2; my(wc = vecsum(cur)); if (wc < bw, bw = wc; best = cur));
      bet[, j] = best);
    printf("  weights of beta_j: %s before, %s after the reduction by span(kappa)\n", w0, vector(4, j, vecsum(bet[, j])));
    for (j = 1, 4, if (!f2in(KMs[1], (Rv * bet[, j] - Cd * SBk[, j]) % 2) || !f2in(Xn, bet[, j]), okb = 0));
    chk5(okb, "beta_j (j = 0..3) in X with res_v(G_new beta_j) = sum_i SB_ij c_i modulo KM_v: the coordinate form of RelAtV at sigma");
    chk5(!f2in(KMs[1], (Rv * ((bet[, 1] + bet[, 2]) % 2) - Cd * SBk[, 1]) % 2), "negative control: beta_0 + beta_1 fails the relation of column 0");
    KMbar[k] = matrix(164, 0);
    for (j = 1, #offs, my(o = offs[j], Kj = KMs[j]); if (#Kj, KMbar[k] = matconcat([KMbar[k], matconcat([matrix(o[1], #Kj); Kj; matrix(164 - o[1] - o[2], #Kj)])])));
    chk5(vecmin(vector(16, tt, f2in(Xn, kap[, tt]))) && f2eqspan(matconcat([bet, kap]), Xn), "kappa_t in X, and span(beta_0..beta_3, kappa_0..kappa_15) = X (dim 4 + 15 = 19)");
    chk5(vecmin(vector(16, tt, f2in(KMbar[k], Gn * kap[, tt] % 2))), "the kappa_t are trivial at every place modulo KM_w");
    \\ a_T
    aT = MU[k][3]~;
    my(x1 = Lsc(-TW[5][k], Lev(TW[4], al)), x2 = Nev(TW[3], be), kp = KofList(MU[k][1]) / MU[k][2], lt);
    lt = (sel_loccol(A, fin, re, 1, toL(Lsc(Kd(1, kp), x1))) + sel_loccol(A, fin, re, 2, toN(Nsc(Kd(1, kp), x2)))) % 2;
    chk5((Gn * aT - lt) % 2 == 0, "G_new a_T = loc(x1 / kappa, x2 / kappa) (a_T, kappa of sb_5t)");
    chk5(f2in(Xn, aT), "a_T lies in X (mu(T) is a Selmer class)");
    printf("  mu(T) modulo sum KM_w: %s\n", if (f2in(KMbar[k], lt), "trivial", "nontrivial"));
    \\ known classes of p21_29 (T and phi(x_i), unreversed model) in loc(X) + sum KM_w
    my(pts = List(), nm = List(), G1x = td2_Kx(nfK, subst(RIN[k][2], t, x)), kn = 1);
    listput(pts, [-td2_evalu(A, 1, mapget(A, "fd")) * td2_evalu(A, 1, deriv(G1x, 'x)), td2_evalu(A, 2, G1x)]); listput(nm, "T");
    foreach (PHI, ph, if (ph[2] == k - 1, my(U = td2_Kx(nfK, subst(ph[4], t, x))); listput(pts, td2_uvals(A, U / pollead(U))); listput(nm, Str("phi(x_", ph[1], ")"))));
    for (qq = 1, #pts, my(vals = pts[qq], col = List(), cv);
      foreach (fin, Pw, listput(col, td2_coordvals(A, Pw, vals)));
      foreach (re, rp, listput(col, sel_realcoord(A, rp, vals)));
      cv = concat(Vec(col));
      if (!f2in(matconcat([GX, KMbar[k]]), cv), kn = 0; printf("  known class %s NOT in loc(X) + sum KM_w\n", nm[qq]));
      if (qq == 1 && !f2in(KMbar[k], (cv - lt) % 2), kn = 0; printf("  T of p21_29 differs from mu(T) of sb_5t modulo sum KM_w\n")));
    chk5(kn && #pts >= 2, Str("known classes ", Vec(nm), " lie in loc(X) + sum KM_w; T of p21_29 = loc(x1 / kappa, x2 / kappa) modulo sum KM_w"));
    printf("  beta_j (rows, 82 bits): %s\n", bet~);
    res[k] = [Xn, bet, SC, SBk, Cd, aT]);
  printf("kappa_t (rows, 82 bits): %s\n", kap~);
  system(Str("rm -f ", OUT));
  writebin(OUT, [Gn, Cm, kap, rel, res]);
  chk5(read(OUT)[1] == Gn && read(OUT)[5] == res, "cache /tmp/sb5/selmer.bin written and read back");
  printf("DONE selmer_space_new_generators: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
