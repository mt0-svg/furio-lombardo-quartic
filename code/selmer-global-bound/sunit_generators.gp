\\ sunit_generators.gp: small generators of L42(S,2) and N84(S,2), S = the primes above 2 and 7, in the formats of SUnitData.lean.
\\ Method: the S-unit generators of p21_29 (L: the 28 compact S-units of
\\ gens.bin plus -1; N: the 53 saturated generators of nsat.bin, the first one -1) are compact products with exponents
\\ up to 3 10^11. LLL on their S-log lattice (archimedean logs weighted 1 or 2, valuations at the primes of S weighted
\\ by -log N(P)) gives a unimodular change T; each reduced element x_k = prod_i g_i^(T[i,k]) is recovered EXACTLY
\\ on nf.zk from its complex log-embeddings (rounded solution of the real n x n embedding system), after scaling by
\\ the least power 2^A 7^B that makes it integral; then converted to the tower (MTL^-1, MTN^-1 of sb_5a) and scaled
\\ by 2^B2 7^B7 (B of any sign): the least multiple with integral format coordinates, times 2 or 7 once more when
\\ needed to make the total exponents A + B even (so x_k keeps the square class of prod g_i^T). Exact checks per element:
\\ norm +-2^a 7^b and the predicted valuations at S (in nfL / nfN); in the tower, format coordinates integral, and a
\\ cofactor w with integral format coordinates and x w = 2^a 7^b (a, b >= 0 least), which makes x an S-unit
\\ (the membership certificate of the Lean proof). Independence modulo squares: F2 rank 29, 53 of the quadratic
\\ characters at 80 degree one primes of nfL, nfN (norm_relation_lib's charprimes; the Lean characters are
\\ computed separately in the tower by sb_5d).
\\ Order: L: the 28 reduced elements, then -1 (as p21_29); N: -1, then the 52 reduced elements (as p21_29).
\\ Cache entries per generator: [coordinates (L: [a0, a1]; N: the Lean format [a0, a1, b0, b1], b = c / 2), nf.zk
\\ coordinates, [E2, E7], cofactor w (same format), [a, b], column of T].
\\ Output cache /tmp/sb5/gens.bin. Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/sunit_generators.gp < /dev/null > ../selmer-global-bound/sunit_generators.out 2>&1
default(parisizemax, 900 * 10^6); default(nbthreads, 1); default(realprecision, 300);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("field_l42_polynomial.gp"); read("field_n84_polynomial.gp");
read("norm_relation_lib.gp");
read("../selmer-global-bound/tower_lib.gp");
OUT = "/tmp/sb5/gens.bin";

\\ complex log-embeddings (r1 + r2 values, principal branch) and the valuations at SP of the element with nf.zk
\\ coordinates col
cl_col(nf, col, SP) = { my(em = nf[5][1] * col); [vector(#em, j, log(em[j])), vector(#SP, j, nfeltval(nf, col, SP[j]))]; }

\\ LLL reduction and exact recovery. CL[i] = [complex logs, valuations] of the m old generators; MT, MTi the format
\\ matrix of sb_5a and its inverse; kind 1 (L, 2 blocks) or 2 (N, 4 blocks).
recover(nf, CL, SP, MT, MTi, kind) = {
  my(m = #CL, r1 = nf.sign[1], r2 = nf.sign[2], n = poldegree(nf.pol), Lam, T, Mr, Mri, res = List(), t0 = getabstime());
  Lam = matrix(r1 + r2 + #SP, m, j, i, if (j <= r1 + r2, real(CL[i][1][j]) * if (j <= r1, 1, 2), -CL[i][2][j - r1 - r2] * log(SP[j - r1 - r2].p) * SP[j - r1 - r2].f));
  chk5(vecmax(apply(i -> abs(vecsum(Lam[, i])), [1 .. m])) < 10^-30, "product formula: every S-log vector sums to 0");
  T = qflll(Lam);
  chk5(matsize(T) == [m, m] && abs(matdet(T)) == 1, Str("LLL transform T is ", m, " x ", m, " unimodular"));
  my(R = Lam * T, mx = vector(m, k, vecmax(apply(abs, Vec(R[, k])))));
  printf("  S-log vectors after LLL: max |entry| min %.2f median %.2f max %.2f (before: max %.3e)\n", vecmin(mx), vecsort(mx)[m \ 2 + 1], vecmax(mx), vecmax(apply(abs, concat(Vec(Lam)))));
  Mr = matconcat([real(nf[5][1][1 .. r1, ]); real(nf[5][1][r1 + 1 .. r1 + r2, ]); imag(nf[5][1][r1 + 1 .. r1 + r2, ])]);
  Mri = Mr^(-1);
  for (k = 1, m,
    my(Lk = sum(i = 1, m, T[i, k] * CL[i][1]), Vk = sum(i = 1, m, T[i, k] * CL[i][2]), A2 = -oo, A7 = -oo, sig, rhs, c, cr, err, nm, vv, yv, B2, B7, yf, xt, cf, xi, fi, ea, eb, wv, wt, one, cnt = 0);
    for (j = 1, #SP, my(P = SP[j], need = ceil(-Vk[j] / P.e)); if (P.p == 2, A2 = max(A2, need), A7 = max(A7, need)));
    sig = vector(r1 + r2, j, exp(Lk[j] + A2 * log(2) + A7 * log(7)));
    rhs = concat([real(sig[1 .. r1]), real(sig[r1 + 1 .. r1 + r2]), imag(sig[r1 + 1 .. r1 + r2])])~;
    c = Mri * rhs; cr = round(c); err = vecmax(abs(c - cr));
    chk5(err < 10^-20 && cr != 0, Str("element ", k, ": coordinates on nf.zk recovered, rounding error ", Strprintf("%.1e", err), " < 10^-20"));
    nm = nfeltnorm(nf, cr);
    chk5(nm != 0 && abs(nm) == 2^valuation(nm, 2) * 7^valuation(nm, 7), Str("element ", k, ": norm +-2^", valuation(nm, 2), " 7^", valuation(nm, 7)));
    vv = vector(#SP, j, nfeltval(nf, cr, SP[j]));
    chk5(vv == Vk + vector(#SP, j, if (SP[j].p == 2, A2, A7) * SP[j].e) && vecmin(vv) >= 0, Str("element ", k, ": valuations at S = the lattice prediction, integral"));
    \\ tower format coordinates
    yv = MTi * cr;
    chk5(denominator(yv) == 2^valuation(denominator(yv), 2) * 7^valuation(denominator(yv), 7), "format coordinates have 2, 7 denominators only");
    B2 = -vecmin([valuation(e, 2) | e <- Vec(yv), e != 0]); B7 = -vecmin([valuation(e, 7) | e <- Vec(yv), e != 0]);
    \\ keep the total exponents A + B even, so that the class modulo squares is that of prod old^T
    chk5(denominator(2^B2 * 7^B7 * yv) == 1 && content(2^B2 * 7^B7 * yv) % 2 && content(2^B2 * 7^B7 * yv) % 7, Str("element ", k, ": 2^", B2, " 7^", B7, " x is the least 2, 7 multiple with integral format coordinates"));
    if ((A2 + B2) % 2, B2++); if ((A7 + B7) % 2, B7++);
    yf = 2^B2 * 7^B7 * yv;
    chk5(denominator(yf) == 1 && (A2 + B2) % 2 == 0 && (A7 + B7) % 2 == 0, Str("element ", k, ": scaled by 2^", B2, " 7^", B7, ": integral format coordinates, total exponents ", [A2 + B2, A7 + B7], " even (same square class as prod old^T)"));
    cf = 2^B2 * 7^B7 * cr;
    chk5(MT * yf == cf, "format coordinates map back to the nf.zk coordinates");
    if (kind == 1, xt = [yf[1 .. 21], yf[22 .. 42]]; xi = Linv(xt), fi = [yf[1 .. 21], yf[22 .. 42], yf[43 .. 63], yf[64 .. 84]]; xt = Nunfmt(fi); xi = Nfmt(Ninv(xt)));
    \\ cofactor w = 2^a 7^b / x, least a, b >= 0 with integral format coordinates
    ea = max(0, -vecmin([valuation(e, 2) | e <- concat(apply(Vec, xi)), e != 0])); eb = max(0, -vecmin([valuation(e, 7) | e <- concat(apply(Vec, xi)), e != 0]));
    wv = apply(v -> 2^ea * 7^eb * v, xi);
    chk5(den5(wv) == 1, Str("element ", k, ": cofactor w = 2^", ea, " 7^", eb, " / x has integral format coordinates"));
    if (kind == 1, one = Lmul(xt, wv); chk5(one == [Kc(2^ea * 7^eb), Kc(0)], Str("element ", k, ": x w = 2^", ea, " 7^", eb, " in L42 (exact)")),
      one = Nmul(xt, Nunfmt(wv)); chk5(one == NofK(2^ea * 7^eb), Str("element ", k, ": x w = 2^", ea, " 7^", eb, " in N84 (exact)")));
    listput(res, [if (kind == 1, xt, fi), cf, [A2 + B2, A7 + B7], wv, [ea, eb], T[, k]]));
  printf("  recovery of %d elements: %d ms\n", m, getabstime() - t0);
  [Vec(res), T];
}

\\ F2 rank of the quadratic characters at np degree one primes of nf on the columns cols (nf.zk coordinates)
charrank(nf, cols, np) = { my(P = charprimes(nf, np, 100), Mc = matrix(np, #cols, i, j, chi(P[i], cols[j]))); [matrank(Mod(Mc, 2)), P[np][1]]; }

main() = {
  my(t0 = getabstime(), TW = read("/tmp/sb5/tower.bin"), FF, nfL, nfN, SL, SN, GG, su, baseL, CLL, NS, TAB, SAT, bN, CLN, cache = Map(), RL, RN, genL, genN, nc = 0);
  nfK = nfinit(K21);
  EPS = TW[1]; EN = TW[2];
  FF = read("/tmp/k21c/sel/fields.bin"); nfL = FF[2]; nfN = FF[3];
  chk5(FF[1].zk == nfK.zk, "the nfK of fields.bin has the zk of nfinit(K21)");
  \\ ---- L
  SL = concat(idealprimedec(nfL, 2), idealprimedec(nfL, 7));
  chk5(#SL == 5 && nfL.sign == [6, 18], "L: 5 primes above 2 and 7, signature [6, 18] (r1 + r2 + #S - 1 = 28)");
  GG = read("/tmp/k21c/sel/gens.bin"); su = GG[2];
  chk5(#su[2] == 28 && su[4] == Mat([-1, 1]), "p21_29's L generators: 28 compact S-units and -1");
  baseL = apply(g -> nfalgtobasis(nfL, Mod(subst(g, 'x, 'u), Lpol)), su[3]);
  my(clB = vector(#baseL, i, cl_col(nfL, baseL[i], SL)));
  CLL = vector(28, i, my(fm = su[2][i], L0 = vector(nfL.sign[1] + nfL.sign[2]), V0 = vector(5)); for (l = 1, #fm, L0 += fm[l][2] * clB[fm[l][1]][1]; V0 += fm[l][2] * clB[fm[l][1]][2]); [L0, V0]);
  printf("L: complex logs of the 28 generators (%d ms)\n", getabstime() - t0);
  RL = recover(nfL, CLL, SL, TW[16], TW[17], 1);
  genL = concat(RL[1], [[[Kc(-1), Kc(0)], nfalgtobasis(nfL, -1), [0, 0], [Kc(-1), Kc(0)], [0, 0], vectorv(28)]]);
  my(crL = charrank(nfL, apply(g -> g[2], genL), 80));
  chk5(crL[1] == 29, Str("L: the 29 generators are independent modulo squares (F2 rank 29 of the characters at 80 degree one primes of nfL, p <= ", crL[2], ")"));
  \\ ---- N
  SN = concat(idealprimedec(nfN, 2), idealprimedec(nfN, 7));
  chk5(#SN == 8 && nfN.sign == [6, 39], "N: 8 primes above 2 and 7, signature [6, 39] (r1 + r2 + #S - 1 = 52)");
  NS = read("/tmp/k21c/nr/nsunits.bin"); TAB = NS[2]; SAT = read("/tmp/k21c/nr/nsat.bin"); bN = SAT[1];
  chk5(#bN == 53 && bN[1][1] == 1 && #Mat(bN[1][2])~ == 0 && #bN[1][3] == 0, "p21_28's N generators: 53, the first one -1");
  my(clb = (kk -> my(v, rk2); if (mapisdefined(cache, kk, &v), return(v)); rk2 = eval(Str("[", kk, "]")); v = cl_col(nfN, TAB[rk2[1]][3][rk2[2]], SN); mapput(cache, kk, v); nc++; v));
  CLN = vector(52, i, my(A = bN[i + 1], L0 = vector(45), V0 = vector(8), M = Mat(A[2]));
    if (A[1], L0 += vector(45, j, Pi * I));
    for (l = 1, #M~, my(c = clb(M[l, 1])); L0 += M[l, 2] * c[1]; V0 += M[l, 2] * c[2]);
    for (l = 1, #A[3], my(c = cl_col(nfN, A[3][l][1], SN)); L0 += A[3][l][2] * c[1]; V0 += A[3][l][2] * c[2]);
    [L0, V0]);
  printf("N: complex logs of the 52 generators, %d base elements (%d ms)\n", nc, getabstime() - t0);
  RN = recover(nfN, CLN, SN, TW[18], TW[19], 2);
  genN = concat([[[Kc(-1), Kc(0), Kc(0), Kc(0)], nfalgtobasis(nfN, -1), [0, 0], [Kc(-1), Kc(0), Kc(0), Kc(0)], [0, 0], vectorv(52)]], RN[1]);
  my(crN = charrank(nfN, apply(g -> g[2], genN), 80));
  chk5(crN[1] == 53, Str("N: the 53 generators are independent modulo squares (F2 rank 53 of the characters at 80 degree one primes of nfN, p <= ", crN[2], ")"));
  \\ ---- summary
  printf("L: format coordinate bits per generator %s\n", apply(g -> bits5(g[1]), genL));
  printf("L: cofactor bits %s\n", apply(g -> bits5(g[4]), genL));
  printf("L: (a, b) of x w = 2^a 7^b: %s\n", apply(g -> g[5], genL));
  printf("L: scaling exponents E (x = 2^E2 7^E7 prod old^T): %s\n", apply(g -> g[3], genL));
  printf("N: format coordinate bits per generator %s\n", apply(g -> bits5(g[1]), genN));
  printf("N: cofactor bits %s\n", apply(g -> bits5(g[4]), genN));
  printf("N: (a, b) of x w = 2^a 7^b: %s\n", apply(g -> g[5], genN));
  printf("N: scaling exponents E: %s\n", apply(g -> g[3], genN));
  chk5(#genL == 29 && #genN == 53 && vecmin(apply(g -> #g[1] == 2 && #g[1][1] == 21 && #g[1][2] == 21, genL)) && vecmin(apply(g -> #g[1] == 4 && vecmin(apply(v -> #v == 21, g[1])), genN)), "29 L generators, 53 N generators, every zk list of length 21");
  system(Str("rm -f ", OUT));
  writebin(OUT, [genL, genN, RL[2], RN[2]]);
  chk5(#read(OUT)[2] == 53, "cache /tmp/sb5/gens.bin written and read back");
  printf("DONE sunit_generators: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
