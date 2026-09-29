\\ mu_t_cert.gp: the certificate for mu(T) of GlobalCRT.lean's muT_components, per
\\ twist k = 0, 1. mu(T) = [(q - C c_k h)(T)] has the components x1 = -c_k h(alpha) in L42, x2 = q(beta) in N84
\\ (alpha, beta, q, h of sb_5a; c_k = FnData[k][0] / 4). Wanted: kappa in K21^x, bits a_s (s < 82), y1, y2 with
\\   x1 prod_{s < 29} gensL_s^(a_s) = kappa y1^2,   x2 prod_{s >= 29} gensN_(s - 29)^(a_s) = kappa y2^2.
\\ Method. (1) kappa: the primes of K21 outside S = {2, 7} where x1 or x2 has an odd valuation. L42 / K21 and N84 / K21
\\ are unramified outside 2 (checked: e = 1 above every such prime), so a common kappa exists iff for every prime P0
\\ of K21 outside S the valuations of x1 at the primes of L above P0 and of x2 at the primes of N above P0 all have the
\\ same parity e(P0); then kappa generates prod P0^e(P0) (h(K21) = 1; bnfisprincipal of a bnfinit of K21, and the
\\ generator is checked by its valuations, so the GRH of bnfinit plays no role). (2) The exponents: x1 / kappa and
\\ x2 / kappa have even valuations outside S, hence lie in L42(S,2), N84(S,2) modulo squares (Cl(L)[2] = Cl(N)[2] = 0,
\\ p21_16, p21_24); their classes on the 29 + 53 generators come from 29, 53 residue characters (chosen as in sb_5d,
\\ nonzero on the generators and on x1 / kappa, x2 / kappa for both twists), full rank on the generators, so a class
\\ with trivial characters is a square. (3) y1, y2: exact square roots in the tower (Lsqrt, Nsqrt of tower_lib.gp);
\\ their existence is the certificate. Checks, exact on the exported integers, in the form of the Lean checks
\\ (A = alphaDen alpha, B = betaPowDen beta, D_L = alphaDen, D_N = betaPowDen, hL, qL the numerators of h, q with
\\ leading hDen, qDen):
\\   -(FE k 0) [sum_i hL_i A^i D_L^(4-i)] prodLT kapTDen y1TDen^2 = 4 hDen D_L^4 kapT y1T^2,
\\   [sum_i qL_i B^i D_N^(2-i)] prodNT kapTDen y2TDen^2 = qDen D_N^2 kapT y2T^2,
\\ with prodLT = prod_{s < 29, a_s = 1} gensL_s (gL format), prodNT = prod_{s >= 29, a_s = 1} gensN_(s - 29) (gN format).
\\ Negative controls: a flipped bit of a, and kappa replaced by -kappa, leave no square root.
\\ Output cache /tmp/sb5/muT.bin (read by sunit_data_lean.gp). Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/mu_t_cert.gp < /dev/null > ../selmer-global-bound/mu_t_cert.out 2>&1
default(parisizemax, 1700 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
DATA = "../selmer-global-bound/sunit_generators_data.gp";
OUT = "/tmp/sb5/muT.bin";

rhozk(zkNum, Dz, p, t) = vector(21, j, Mod(subst(Pol(Vecrev(zkNum[j]), 'b), 'b, t), p) / Dz);
rhoK(rz, a) = sum(j = 1, 21, a[j] * rz[j]);
\\ greedy choice of m characters (as sb_5d) on the generators gens (gL or gN format lists), with every generator and
\\ every target (same format, rational coordinates) nonzero modulo p; kind 1 (L) or 2 (N). Returns [data, M]
choose2(gens, targets, kind, zkNum, Dz, DB, fL, epsL, eaL, ebL) = {
  my(m = #gens, data = List(), rk = 0, p = 2, M = matrix(0, m), dT = den5(targets));
  while (rk < m, p = nextprime(p + 1);
    if (p == 7 || Dz % p == 0 || DB % p == 0 || dT % p == 0, next);
    my(ts = polrootsmod(Pol(Vecrev(fL), 'X), p), done = 0);
    foreach (ts, tt, if (done, break);
      my(rz = rhozk(zkNum, Dz, p, lift(tt)), re = rhoK(rz, epsL), ss);
      if (re == 0 || !issquare(re, &ss), next);
      foreach ([ss, -ss], sv, if (done, break);
        my(t2s = [0]);
        if (kind == 2, my(te = 2 * (rhoK(rz, eaL) + sv * rhoK(rz, ebL)), t2); if (te == 0 || !issquare(te, &t2), next); t2s = [t2, -t2]);
        foreach (t2s, tv, if (done, break);
          my(val = (g -> if (kind == 1, rhoK(rz, g[1]) + sv * rhoK(rz, g[2]), rhoK(rz, g[1]) + sv * rhoK(rz, g[2]) + (rhoK(rz, g[3]) + sv * rhoK(rz, g[4])) * tv)),
             vals = apply(val, gens), tv2 = apply(val, targets));
          if (vecmin(apply(v -> v != 0, concat(vals, tv2))) == 0, next);
          my(bits = vector(m, s, kronecker(lift(vals[s]), p) == -1), M2 = matconcat([M; bits]), r2 = matrank(Mod(M2, 2)));
          if (r2 > rk, M = M2; rk = r2; done = 1; listput(data, [p, lift(tt), lift(sv), lift(tv), val]))))));
  [Vec(data), M];
}
\\ class of a target on the generators: a with chars(prod gens^a) = chars(target)
classof(CH, x) = { my(D = CH[1], M = CH[2], bits = vectorv(#D, j, my(v = D[j][5](x), p = D[j][1]); if (v == 0, error("classof: zero residue")); kronecker(lift(v), p) == -1)); lift(Mod(M, 2)^(-1) * Mod(bits, 2)); }
\\ images of K21 in nfL, nfN (tower.bin) and the primes of nfG above a prime P0 of K21
imgK(Z, c) = my(cc = Kc(c)); sum(j = 1, 21, cc[j] * Z[j]);
above(nfG, Z, P0) = { my(g2 = imgK(Z, P0.gen[2])); [P | P <- idealprimedec(nfG, P0.p), nfeltval(nfG, g2, P) > 0]; }

main() = {
  my(t0 = getabstime(), TW = read("/tmp/sb5/tower.bin"), FF = read("/tmp/sb5/sel/fields.bin"), GN = sb5_gens(DATA), q, h, cK, al, be, nfL, nfN, ZL, ZN, MTL, MTN,
     zkNum = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"), Dz = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz"), DB = leandef5(Str(LEAN, "M1/DataBezout.lean"), "DB"),
     fL = leandef5(Str(LEAN, "M1/Basic.lean"), "fL"), epsL = leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL"), eaL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL"),
     ebL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL"), Fn = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "FnData"),
     qD = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qData"), hD = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hData"),
     qDen = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qDen"), hDen = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hDen"),
     genL, genN, bnfK, X1 = vector(2), X2 = vector(2), KAP = vector(2), res = vector(2));
  nfK = nfinit(K21); EPS = TW[1]; EN = TW[2]; q = TW[3]; h = TW[4]; cK = TW[5]; al = TW[7]; be = TW[8];
  nfL = FF[2]; nfN = FF[3]; ZL = TW[9]; ZN = TW[12]; MTL = TW[16]; MTN = TW[18];
  genL = apply(g -> g[1], GN[1]); genN = apply(g -> Nunfmt(g[1]), GN[2]);
  chk5(nfK.zk == FF[1].zk, "nfK of fields.bin (sb_5f) = nfinit(K21)");
  my(toL = (xl -> MTL * concat(xl[1], xl[2])), toN = (xn -> MTN * concat(Nfmt(xn))));
  chk5(nfalgtobasis(nfL, nfeltmul(nfL, toL(genL[3]), toL(genL[5]))) == toL(Lmul(genL[3], genL[5])) && nfalgtobasis(nfN, nfeltmul(nfN, toN(genN[4]), toN(genN[9]))) == toN(Nmul(genN[4], genN[9])),
       "tool: the maps L42 -> nfL, N84 -> nfN of sb_5a (MTL, MTN) are multiplicative on two products of generators");
  bnfK = bnfinit(nfK, 1);
  printf("bnfinit(K21): class number %d (%d ms)\n", bnfK.no, getabstime() - t0);
  chk5(bnfK.no == 1, "h(K21) = 1 in bnfinit (lane M1 proves it; here it only guides the search, the generator is checked)");
  for (k = 1, 2,
    my(x1 = Lsc(-cK[k], Lev(h, al)), x2 = Nev(q, be), c1 = toL(x1), c2 = toN(x2), n1, n2, ps, par = Map(), I = 1, kap, bad = 0);
    printf("---- twist k = %d\n", k - 1);
    chk5(cK[k] == KofList(Fn[k][1]) / 4 && !Lis0(x1) && !Nis0(x2), "x1 = -c_k h(alpha), x2 = q(beta) nonzero, c_k = FnData[k][0] / 4");
    n1 = nfeltnorm(nfL, c1); n2 = nfeltnorm(nfN, c2);
    chk5(n1 == nfeltnorm(nfK, Lnorm(x1)) && n2 == nfeltnorm(nfK, NnormK(x2)), "N(x1), N(x2) agree in the tower and in nfL, nfN");
    ps = setminus(Set(concat(factor(abs(numerator(n1) * denominator(n1)))[, 1]~, factor(abs(numerator(n2) * denominator(n2)))[, 1]~)), Set([2, 7]));
    printf("  rational primes outside 2, 7 dividing N(x1) N(x2): %s\n", ps);
    foreach (ps, p, foreach (idealprimedec(nfK, p), P0,
      my(AL = above(nfL, ZL, P0), AN = above(nfN, ZN, P0), vl = apply(P -> nfeltval(nfL, c1, P), AL), vn = apply(P -> nfeltval(nfN, c2, P), AN));
      chk5(vecsum(apply(P -> P.e * P.f, AL)) == 2 * P0.e * P0.f && vecsum(apply(P -> P.e * P.f, AN)) == 4 * P0.e * P0.f && vecmax(apply(P -> P.e, concat(AL, AN))) == P0.e,
           Str("p = ", p, ", prime of K21 of degree ", P0.f, ": the primes of L42, N84 above it (degrees ", apply(P -> P.f / P0.f, AL), ", ", apply(P -> P.f / P0.f, AN), "), unramified"));
      my(pv = Set(apply(v -> v % 2, concat(vl, vn))));
      if (#pv != 1, bad++; printf("  NO COMMON PARITY at p = %d, f = %d: v(x1) %s, v(x2) %s\n", p, P0.f, vl, vn));
      if (#pv == 1 && pv[1] == 1, I = idealmul(nfK, I, P0));
      if (vecmax(apply(abs, concat(vl, vn))) > 0, printf("  p = %d, f = %d: v(x1) at the primes of L above %s, v(x2) at the primes of N above %s\n", p, P0.f, vl, vn))));
    chk5(bad == 0, "at every prime of K21 outside 2, 7 the valuations of x1 (primes of L above) and x2 (primes of N above) have one parity");
    kap = bnfisprincipal(bnfK, I, 1);
    chk5(#kap[1] == 0 || kap[1] == 0, "the ideal prod P0^e(P0) is principal");
    kap = kap[2];
    \\ the generator: valuations checked at every prime above ps (and it is an S-integer generator: v = e(P0) there)
    my(okk = 1);
    foreach (ps, p, foreach (idealprimedec(nfK, p), P0, if (nfeltval(nfK, kap, P0) != idealval(nfK, I, P0), okk = 0)));
    chk5(okk && abs(nfeltnorm(nfK, kap)) == idealnorm(nfK, I), "kappa generates prod P0^e(P0) (valuations and norm)");
    printf("  kappa: norm %s, %d bits\n", factor(nfeltnorm(nfK, kap)), bits5(kap));
    X1[k] = Lsc(Kd(1, kap), x1); X2[k] = Nsc(Kd(1, kap), x2); KAP[k] = kap;
    \\ evenness outside S after division
    my(ev = 1); foreach (ps, p, foreach (idealprimedec(nfL, p), P, if (nfeltval(nfL, toL(X1[k]), P) % 2, ev = 0)); foreach (idealprimedec(nfN, p), P, if (nfeltval(nfN, toN(X2[k]), P) % 2, ev = 0)));
    chk5(ev, "x1 / kappa, x2 / kappa have even valuations at every prime of L42, N84 above the primes of ps"));
  \\ characters, one set for both twists
  my(chl = choose2(apply(g -> [Vec(g[1]), Vec(g[2])], genL), [X1[1], X1[2]], 1, zkNum, Dz, DB, fL, epsL, eaL, ebL),
     chn = choose2(apply(g -> Nfmt(g), genN), [Nfmt(X2[1]), Nfmt(X2[2])], 2, zkNum, Dz, DB, fL, epsL, eaL, ebL));
  chk5(matrank(Mod(chl[2], 2)) == 29 && matrank(Mod(chn[2], 2)) == 53, Str("29, 53 characters of full rank on the generators, nonzero on x1 / kappa, x2 / kappa (primes ", chl[1][1][1], " to ", chl[1][29][1], ", ", chn[1][1][1], " to ", chn[1][53][1], ")"));
  my(sqL = (xx, aL) -> my(pr = [Kc(1), Kc(0)]); for (s = 1, 29, if (aL[s], pr = Lmul(pr, genL[s]))); [pr, Lsqrt(Lmul(xx, pr))],
     sqN = (xx, aN) -> my(pr = NofK(1)); for (s = 1, 53, if (aN[s], pr = Nmul(pr, genN[s]))); [pr, Nsqrt(Nmul(xx, pr))]);
  for (k = 1, 2,
    my(aL = classof(chl, X1[k]), aN = classof(chn, Nfmt(X2[k])), rl, rn, t1 = getabstime());
    printf("---- twist k = %d: a_T (L part) %s, (N part) %s\n", k - 1, aL~, aN~);
    rl = sqL(X1[k], aL); rn = sqN(X2[k], aN);
    chk5(rl[2] != 0 && Lmul(rl[2], rl[2]) == Lmul(X1[k], rl[1]), "x1 prod gensL^a = kappa y1^2 with y1 in L42 (exact square root)");
    chk5(rn[2] != 0 && Nmul(rn[2], rn[2]) == Nmul(X2[k], rn[1]), "x2 prod gensN^a = kappa y2^2 with y2 in N84 (exact square root)");
    printf("  square roots: %d ms\n", getabstime() - t1);
    \\ negative controls
    my(aLb = aL, aNb = aN); aLb[1] = 1 - aLb[1]; aNb[2] = 1 - aNb[2];
    chk5(sqL(X1[k], aLb)[2] == 0 && sqN(X2[k], aNb)[2] == 0, "negative control: a with one bit flipped (L bit 0, N bit 1) leaves no square root");
    chk5(sqL(Lneg(X1[k]), aL)[2] == 0 || sqN(Nneg(X2[k]), aN)[2] == 0, "negative control: -kappa in place of kappa leaves no square root in L42 or in N84");
    res[k] = [KAP[k], concat(aL~, aN~), rl[1], rl[2], rn[1], rn[2]]);
  \\ export formats and the Lean form of the checks on the integers
  my(aD = TW[20], aI = [KofList(TW[21][1]), KofList(TW[21][2])], bD = 2 * TW[22], bI = Nsc(2, vector(4, i, KofList(TW[23][i]))), exp = vector(2));
  for (k = 1, 2,
    my(kap = res[k][1], aT = res[k][2], pL = res[k][3], y1 = res[k][4], pN = res[k][5], y2 = res[k][6], kD = den5(kap), y1D = den5(y1), y2D = den5(Nfmt(y2)),
       kapT = Klist(kD * kap), y1T = [Klist(y1D * y1[1]), Klist(y1D * y1[2])], y2T = vector(4, i, Klist(y2D * Nfmt(y2)[i])),
       prodLT = [Klist(pL[1]), Klist(pL[2])], prodNT = vector(4, i, Klist(Nfmt(pN)[i])), hL, qL, sL, sN, lhs, rhs, FE0 = KofList(Fn[k][1]));
    hL = concat(vector(4, i, KofList(hD[k][i])), [Kc(hDen[k])]); qL = concat(vector(2, i, KofList(qD[k][i])), [Kc(qDen[k])]);
    sL = [Kc(0), Kc(0)]; my(Ai = [Kc(1), Kc(0)]); for (i = 0, 4, sL = Ladd(sL, Lsc(Km(hL[i + 1], aD^(4 - i)), Ai)); Ai = Lmul(Ai, aI));
    sN = NofK(0); my(Bi = NofK(1)); for (i = 0, 2, sN = Nadd(sN, Nsc(Km(qL[i + 1], bD^(2 - i)), Bi)); Bi = Nmul(Bi, bI));
    my(KT = KofList(kapT), Y1 = [KofList(y1T[1]), KofList(y1T[2])], Y2 = Nunfmt(vector(4, i, KofList(y2T[i]))), PL = [KofList(prodLT[1]), KofList(prodLT[2])], PN = Nunfmt(vector(4, i, KofList(prodNT[i]))));
    lhs = Lsc(Km(-FE0, kD * y1D^2), Lmul(sL, PL)); rhs = Lsc(Km(4 * hDen[k] * aD^4, KT), Lmul(Y1, Y1));
    chk5(lhs == rhs, Str("k = ", k - 1, ": -(FE k 0) [sum_i hL_i A^i D_L^(4-i)] prodLT kapTDen y1TDen^2 = 4 hDen D_L^4 kapT y1T^2 (exact, on the exported integers)"));
    lhs = Nsc(kD * y2D^2, Nmul(sN, PN)); rhs = Nsc(Km(qDen[k] * bD^2, KT), Nmul(Y2, Y2));
    chk5(lhs == rhs, Str("k = ", k - 1, ": [sum_i qL_i B^i D_N^(2-i)] prodNT kapTDen y2TDen^2 = qDen D_N^2 kapT y2T^2 (exact, on the exported integers)"));
    printf("  k = %d sizes: kapT %d bits (kapTDen %d), y1T %d bits (y1TDen %d), y2T %d bits (y2TDen %d), prodLT %d bits, prodNT %d bits; %d + %d bits of a_T set\n", k - 1,
      bits5(kapT), kD, bits5(y1T), y1D, bits5(y2T), y2D, bits5(prodLT), bits5(prodNT), vecsum(aT[1 .. 29]), vecsum(aT[30 .. 82]));
    exp[k] = [kapT, kD, aT, y1T, y1D, y2T, y2D, prodLT, prodNT]);
  system(Str("rm -f ", OUT));
  writebin(OUT, exp);
  chk5(read(OUT) == exp, "cache /tmp/sb5/muT.bin written and read back");
  printf("DONE mu_t_cert: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
