\\ tower.gp: the field K21, the tower L42 < N84 and their identifications with the fields of p21_29.
\\ (1) K21 = nfinit of M1's polynomial fL (lean/FurioLombardo/M1/Basic.lean); PARI's nf.zk equals M1's zkNum / Dz
\\     (DataField.lean) and the zk of fields.bin. The tower L42 = K21(om), N84 = L42(on) of M3b with eps = epsL
\\     (K21Defs.lean), eN = (eaL + ebL om) / 2 (DataL.lean), in the coordinates of SUnitDefs.lean (tower_lib.gp).
\\ (2) The roots alpha of q in L42, beta of h in N84 (q, h of M3a's DataBruin.lean, the same for k = 0, 1), checked
\\     exactly; formats alphaL, alphaDen, betaN (plain on coordinates), betaDen of SUnitData.lean.
\\ (3) The identifications iotaL : L42 -> nfL (theta -> aL, alpha -> 1/thL), iotaN : N84 -> nfN (theta -> aN,
\\     beta -> 1/thN) with the fields of p21_29 (sel_fields, rebuilt by field_caches.gp in /tmp/sb5/sel/fields.bin):
\\     q(1/thL) = 0, h(1/thN) = 0, the images
\\     of om, on satisfy the defining relations, ring homomorphism tests; the matrices MTL (42 x 42), MTN (84 x 84) of
\\     the format bases (L: zk, zk om; N: zk, zk om, 2 zk on, 2 zk om on) on nfL.zk, nfN.zk, their determinants (the
\\     indices of the format orders in the maximal orders) and inverses (conversion nfL, nfN -> tower).
\\ Output cache /tmp/sb5/tower.bin (read by the later sb_5 scripts). Every claim is printed by an ok: line.
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/tower.gp < /dev/null > ../selmer-global-bound/tower.out 2>&1
default(parisizemax, 900 * 10^6); default(nbthreads, 1); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
system("mkdir -p /tmp/sb5");
OUT = "/tmp/sb5/tower.bin";

tooltests() = {
  chk5(strrepl5("!![1, 0; 0, 1]", "!![", "[") == "[1, 0; 0, 1]" && strrepl5("ab", "x", "y") == "ab", "tool: strrepl5 (replacement and no match)");
  chk5(strtrim5("  a b  ") == "a b" && strtrim5("   ") == "", "tool: strtrim5");
  chk5(leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qDen") == [46, 46], "tool: leandef5 reads qDen = [46, 46] of DataBruin.lean");
  chk5(iferr(leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "noSuchDef"); 0, E, 1), "tool: leandef5 raises an error on a missing def (negative control)");
  chk5(leandef5(Str(LEAN, "M4/Data.lean"), "SB", "namespace T1") == [0, 1, 0, 0; 0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 0; 1, 1, 0, 0; 1, 0, 1, 1; 0, 0, 0, 1], "tool: leandef5 reads the matrix SB of namespace T1 of M4/Data.lean (!![ syntax)");
}

main() = {
  my(t0 = getabstime(), fL, zkNum, Dz, FF, nfL, nfN, aL, thL, aN, thN, epsL, epsInvL, eaL, ebL, mL, qD, hD, qDen, hDen, Fn, q, h, cK, fR);
  tooltests();
  \\ ---- (1) K21 and M1's zk
  fL = leandef5(Str(LEAN, "M1/Basic.lean"), "fL");
  chk5(#fL == 22 && fL[22] == 1, "M1's fL has 22 coefficients, monic");
  chk5(Pol(Vecrev(fL), 'b) == K21, "M1's fL (constant first) is the polynomial K21 of bruin_form.gp");
  nfK = nfinit(Pol(Vecrev(fL), 'b));
  zkNum = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"); Dz = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz");
  chk5(#zkNum == 21 && vecmin(apply(v -> #v == 21, zkNum)), "M1's zkNum: 21 lists of 21 numerators");
  chk5(vector(21, j, Pol(Vecrev(zkNum[j]), 'b) / Dz) == nfK.zk, "PARI's nfK.zk equals M1's zkNum / Dz (the same integral basis, the same order)");
  FF = read("/tmp/sb5/sel/fields.bin");
  chk5(FF[1].pol == nfK.pol && FF[1].zk == nfK.zk, "the nfK of fields.bin (p21_29) has the same polynomial and zk");
  nfL = FF[2]; nfN = FF[3]; aL = FF[4]; thL = FF[5]; aN = FF[6]; thN = FF[7];
  chk5(abs(nfL.disc) == 2^48 * 7^54 && abs(nfN.disc) == 2^96 * 7^111, "nfL, nfN of fields.bin: |disc| = 2^48 7^54, 2^96 7^111 (only 2, 7 divide the discriminant of the order, which nfinit made maximal at 2, 7: the maximal orders)");
  \\ ---- the tower
  epsL = leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL"); epsInvL = leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsInvL");
  eaL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL"); ebL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL");
  mL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "mL");
  EPS = KofList(epsL); EN = [KofList(eaL) / 2, KofList(ebL) / 2];
  chk5(Km(EPS, KofList(epsInvL)) == Kc(1), "eps epsInv = 1 (eps is a unit)");
  chk5(Lnorm(EN) == KofList(mL), "N_{L/K21}(eN) = mL (DataL.lean)");
  chk5(#Ksqrts(EPS) == 0 && Lsqrt(EN) == 0, "eps is not a square in K21 and eN is not a square in L42 (Lsqrt returns 0)");
  \\ tool tests of the tower arithmetic
  my(rK = () -> Col(vector(21, i, random(7) - 3)), rLt = () -> [rK(), rK()], rNt = () -> [rK(), rK(), rK(), rK()], x1 = rNt(), x2 = rNt(), x3 = rNt(), l1 = rLt(), l2 = rLt());
  chk5(Lmul([Kc(0), Kc(1)], [Kc(0), Kc(1)]) == [EPS, Kc(0)] && Nmul([Kc(0), Kc(0), Kc(1), Kc(0)], [Kc(0), Kc(0), Kc(1), Kc(0)]) == NofL(EN), "tool: om^2 = eps, on^2 = eN");
  chk5(Nmul(Nmul(x1, x2), x3) == Nmul(x1, Nmul(x2, x3)) && Nmul(x1, x2) == Nmul(x2, x1) && Nmul(x1, Nadd(x2, x3)) == Nadd(Nmul(x1, x2), Nmul(x1, x3)), "tool: Nmul associative, commutative, distributive (random elements)");
  chk5(Nmul(x1, Ninv(x1)) == NofK(1) && Lmul(l1, Linv(l1)) == [Kc(1), Kc(0)], "tool: inverses in L42, N84");
  chk5(Lsqrt(Lmul(l1, l1)) != 0 && Nsqrt(Nmul(x1, x1)) != 0 && Lmul(Lsqrt(Lmul(l1, l1)), Lsqrt(Lmul(l1, l1))) == Lmul(l1, l1), "tool: Lsqrt, Nsqrt find square roots of squares");
  chk5(Nsqrt(Nmul(NofL(EN), Nmul(x1, x1))) != 0 && Nsqrt(Nmul([Kc(0), Kc(0), Kc(1), Kc(0)], Nmul(x1, x1))) == 0, "tool: eN is a square in N84, on is not (negative control of Nsqrt)");
  \\ ---- q, h, c_k, fRev
  qD = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qData"); hD = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hData");
  qDen = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qDen"); hDen = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hDen");
  Fn = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "FnData");
  chk5(qD[1] == qD[2] && hD[1] == hD[2] && qDen[1] == qDen[2] && hDen[1] == hDen[2], "q and h are the same for k = 0, 1 (DataBruin.lean)");
  q = [KofList(qD[1][1]) / qDen[1], KofList(qD[1][2]) / qDen[1], Kc(1)];
  h = [KofList(hD[1][1]) / hDen[1], KofList(hD[1][2]) / hDen[1], KofList(hD[1][3]) / hDen[1], KofList(hD[1][4]) / hDen[1], Kc(1)];
  cK = vector(2, k, KofList(Fn[k][1]) / 4);
  fR = vector(2, k, vector(7, j, KofList(Fn[k][8 - j]) / 4));
  for (k = 1, 2, chk5(Kpol(fR[k]) == nfbasistoalg(nfK, cK[k]) * Kpol(q) * Kpol(h), Str("fRev ", k - 1, " = c_", k - 1, " q h (c_k = FnData[k][0] / 4, fRev_j = FnData[k][6 - j] / 4)")));
  chk5(#nffactor(nfK, Kpol(q))[, 1] == 1 && #nffactor(nfK, Kpol(h))[, 1] == 1, "q and h are irreducible over K21");
  \\ ---- (2) alpha in L42
  my(dq = Km(q[2], q[2]) - 4 * q[1], zr = Ksqrts(Kd(dq, EPS)), al, alt);
  chk5(#zr == 2, "disc(q) / eps is a square in K21 (so q splits in L42)");
  al = [-q[2] / 2, zr[1] / 2];
  chk5(Lis0(Lev(q, al)), "q(alpha) = 0 in L42, alpha = (-q1 + z om) / 2 with z^2 = disc(q) / eps");
  alt = [-q[2] / 2 + Kc(1), zr[1] / 2];
  chk5(!Lis0(Lev(q, alt)), "negative control: q(alpha + 1) != 0");
  \\ ---- iotaL
  my(nL = poldegree(nfL.pol), aLc = nfalgtobasis(nfL, aL), pwL, ZL, thLc = nfalgtobasis(nfL, thL), thLi, KtoL, OML, iotaL, MTL, dTL, MTLi);
  pwL = vector(21); pwL[1] = nfalgtobasis(nfL, 1); for (i = 2, 21, pwL[i] = nfalgtobasis(nfL, nfeltmul(nfL, pwL[i - 1], aLc)));
  ZL = vector(21, j, sum(i = 0, 20, polcoef(nfK.zk[j], i, 'b) * pwL[i + 1]));
  KtoL = (c -> my(cc = Kc(c)); sum(j = 1, 21, cc[j] * ZL[j]));
  chk5(nfalgtobasis(nfL, nfeltmul(nfL, ZL[2], ZL[2])) == KtoL(Km(nfK.zk[2], nfK.zk[2])), "tool: KtoL is multiplicative on zk_2^2 (images of the zk basis in nfL)");
  thLi = nfalgtobasis(nfL, nfeltdiv(nfL, 1, thLc));
  my(evL = (P, tt) -> my(r = 0 * tt); forstep (i = #P, 1, -1, r = nfalgtobasis(nfL, nfeltmul(nfL, r, tt)) + KtoL(P[i])); r);
  chk5(evL(q, thLi) == 0, "q(1/thL) = 0 in nfL (thL the root of G1 of p21_29)");
  OML = nfalgtobasis(nfL, nfeltdiv(nfL, thLi - KtoL(al[1]), KtoL(al[2])));
  chk5(nfalgtobasis(nfL, nfeltmul(nfL, OML, OML)) == KtoL(EPS), "iotaL(om)^2 = eps in nfL");
  iotaL = (xx -> KtoL(xx[1]) + nfalgtobasis(nfL, nfeltmul(nfL, OML, KtoL(xx[2]))));
  chk5(iotaL(al) == thLi, "iotaL(alpha) = 1/thL");
  chk5(iotaL(Lmul(l1, l2)) == nfalgtobasis(nfL, nfeltmul(nfL, iotaL(l1), iotaL(l2))) && iotaL(Ladd(l1, l2)) == iotaL(l1) + iotaL(l2), "iotaL is multiplicative and additive (random elements)");
  MTL = matconcat(concat(vector(21, k, ZL[k]), vector(21, k, nfalgtobasis(nfL, nfeltmul(nfL, OML, ZL[k])))));
  chk5(matsize(MTL) == [42, 42] && denominator(MTL) == 1, "MTL (42 x 42): the format basis zk, zk om of L42 lies in O_L (integral coordinates on nfL.zk)");
  dTL = abs(matdet(MTL));
  chk5(dTL == 2^valuation(dTL, 2) * 7^valuation(dTL, 7), Str("index [O_L : O_K21 + O_K21 om] = |det MTL| = 2^", valuation(dTL, 2), " 7^", valuation(dTL, 7)));
  MTLi = MTL^(-1);
  my(cL = vectorv(42, i, random(11) - 5), lx = MTLi * cL);
  chk5(iotaL([lx[1 .. 21], lx[22 .. 42]]) == cL && MTLi * iotaL(l1) == concat(l1[1], l1[2]), "conversion nfL -> L42 by MTL^-1 inverts iotaL (random elements both ways)");
  \\ ---- h over L42 and beta in N84
  my(hLpol = Pol(apply(c -> nfbasistoalg(nfL, KtoL(c)), Vecrev(h)), 'X), fa = nffactor(nfL, hLpol), G2s = List(), be = 0, G2 = 0, yv, nsq = 0);
  chk5(#fa[, 1] == 2 && poldegree(fa[1, 1]) == 2 && poldegree(fa[2, 1]) == 2, "h splits over nfL into two quadratics");
  for (i = 1, 2, my(G = fa[i, 1], cs = vector(3, j, nfalgtobasis(nfL, polcoef(G, j - 1, 'X))), gt = vector(3, j, my(v = MTLi * cs[j]); [v[1 .. 21], v[22 .. 42]]));
    chk5(gt[3] == [Kc(1), Kc(0)], "the factor is monic");
    listput(G2s, gt));
  \\ the product of the two factors (in L42[X]) is h
  my(G2a = G2s[1], G2b = G2s[2], pr = vector(5, j, [Kc(0), Kc(0)]));
  for (i = 1, 3, for (j = 1, 3, pr[i + j - 1] = Ladd(pr[i + j - 1], Lmul(G2a[i], G2b[j]))));
  chk5(pr == vector(5, j, [h[j], Kc(0)]), "the two quadratic factors (converted to L42) multiply to h");
  chk5(G2b == apply(c -> [c[1], -c[2]], G2a), "the two factors are conjugate under om -> -om");
  for (i = 1, 2, my(G = G2s[i], dG = Lsub(Lmul(G[2], G[2]), Lsc(4, G[1])), yy = Lsqrt(Lmul(dG, Linv(EN))));
    printf("  factor %d of h over L42: disc / eN is %sa square in L42\n", i, if (yy == 0, "not ", ""));
    if (yy != 0, nsq++; if (G2 == 0, G2 = G; yv = yy)));
  chk5(nsq == 1, "exactly one quadratic factor G2 of h over L42 has disc(G2) / eN a square in L42");
  be = Nof(Lsc(-1/2, G2[2]), Lsc(1/2, yv));
  chk5(Nis0(Nev(h, be)), "h(beta) = 0 in N84, beta = (-g1 + y on) / 2 with y^2 = disc(G2) / eN");
  chk5(!Nis0(Nev(h, Nadd(be, NofK(1)))), "negative control: h(beta + 1) != 0");
  \\ ---- iotaN
  my(nN = poldegree(nfN.pol), aNc = nfalgtobasis(nfN, aN), pwN, ZN, thNc = nfalgtobasis(nfN, thN), thNi, KtoN, evN, Bp, cw, cn, OMN, ONN, iotaN, MTN, dTN, MTNi, tN = getabstime());
  pwN = vector(21); pwN[1] = nfalgtobasis(nfN, 1); for (i = 2, 21, pwN[i] = nfalgtobasis(nfN, nfeltmul(nfN, pwN[i - 1], aNc)));
  ZN = vector(21, j, sum(i = 0, 20, polcoef(nfK.zk[j], i, 'b) * pwN[i + 1]));
  KtoN = (c -> my(cc = Kc(c)); sum(j = 1, 21, cc[j] * ZN[j]));
  chk5(nfalgtobasis(nfN, nfeltmul(nfN, ZN[3], ZN[5])) == KtoN(Km(nfK.zk[3], nfK.zk[5])), "tool: KtoN is multiplicative on zk_3 zk_5");
  thNi = nfalgtobasis(nfN, nfeltdiv(nfN, 1, thNc));
  evN = ((P, tt) -> my(r = 0 * tt); forstep (i = #P, 1, -1, r = nfalgtobasis(nfN, nfeltmul(nfN, r, tt)) + KtoN(P[i])); r);
  chk5(evN(h, thNi) == 0, "h(1/thN) = 0 in nfN (thN the root of h_unrev of p21_29)");
  Bp = vector(4, i, Npow(be, i - 1));
  cw = Ksolve(Bp, [Kc(0), Kc(1), Kc(0), Kc(0)]); cn = Ksolve(Bp, [Kc(0), Kc(0), Kc(1), Kc(0)]);
  chk5(Nadd(Nadd(Nsc(cw[1], Bp[1]), Nsc(cw[2], Bp[2])), Nadd(Nsc(cw[3], Bp[3]), Nsc(cw[4], Bp[4]))) == [Kc(0), Kc(1), Kc(0), Kc(0)], "om = sum c_i beta^i over K21 (4 x 4 solve)");
  my(pT = vector(4)); pT[1] = nfalgtobasis(nfN, 1); for (i = 2, 4, pT[i] = nfalgtobasis(nfN, nfeltmul(nfN, pT[i - 1], thNi)));
  OMN = sum(i = 1, 4, nfalgtobasis(nfN, nfeltmul(nfN, KtoN(cw[i]), pT[i])));
  ONN = sum(i = 1, 4, nfalgtobasis(nfN, nfeltmul(nfN, KtoN(cn[i]), pT[i])));
  chk5(nfalgtobasis(nfN, nfeltmul(nfN, OMN, OMN)) == KtoN(EPS), "iotaN(om)^2 = eps in nfN");
  chk5(nfalgtobasis(nfN, nfeltmul(nfN, ONN, ONN)) == KtoN(EN[1]) + nfalgtobasis(nfN, nfeltmul(nfN, OMN, KtoN(EN[2]))), "iotaN(on)^2 = iotaN(eN) in nfN");
  iotaN = (xx -> KtoN(xx[1]) + nfalgtobasis(nfN, nfeltmul(nfN, OMN, KtoN(xx[2]))) + nfalgtobasis(nfN, nfeltmul(nfN, ONN, KtoN(xx[3]) + nfalgtobasis(nfN, nfeltmul(nfN, OMN, KtoN(xx[4]))))));
  chk5(iotaN(be) == thNi, "iotaN(beta) = 1/thN");
  chk5(iotaN(Nmul(x1, x2)) == nfalgtobasis(nfN, nfeltmul(nfN, iotaN(x1), iotaN(x2))) && iotaN(Nadd(x1, x3)) == iotaN(x1) + iotaN(x3), "iotaN is multiplicative and additive (random elements)");
  MTN = matconcat(concat([vector(21, k, ZN[k]), vector(21, k, nfalgtobasis(nfN, nfeltmul(nfN, OMN, ZN[k]))),
    vector(21, k, 2 * nfalgtobasis(nfN, nfeltmul(nfN, ONN, ZN[k]))), vector(21, k, 2 * nfalgtobasis(nfN, nfeltmul(nfN, nfeltmul(nfN, OMN, ONN), ZN[k])))]));
  chk5(matsize(MTN) == [84, 84] && denominator(MTN) == 1, "MTN (84 x 84): the format basis zk, zk om, 2 zk on, 2 zk om on of N84 lies in O_N");
  dTN = abs(matdet(MTN));
  chk5(dTN == 2^valuation(dTN, 2) * 7^valuation(dTN, 7), Str("index [O_N : format order] = |det MTN| = 2^", valuation(dTN, 2), " 7^", valuation(dTN, 7)));
  MTNi = MTN^(-1);
  my(cN = vectorv(84, i, random(11) - 5), nx = MTNi * cN);
  chk5(iotaN(Nunfmt([nx[1 .. 21], nx[22 .. 42], nx[43 .. 63], nx[64 .. 84]])) == cN && MTNi * iotaN(Nunfmt(x1)) == concat(x1), "conversion nfN -> N84 by MTN^-1 inverts iotaN (random elements both ways)");
  printf("  iotaN and MTN: %d ms\n", getabstime() - tN);
  \\ ---- formats of SUnitData.lean
  my(aDen = den5(al), bDen = den5(be), alphaL = [Klist(aDen * al[1]), Klist(aDen * al[2])], betaN = vector(4, i, Klist(bDen * be[i])));
  printf("alphaDen = %d, alphaL = %s\n", aDen, alphaL);
  printf("betaDen = %d, betaN (plain on coordinates) = %s\n", bDen, betaN);
  chk5(Lis0(Lev(q, [KofList(alphaL[1]) / aDen, KofList(alphaL[2]) / aDen])) && Nis0(Nev(h, vector(4, i, KofList(betaN[i]) / bDen))), "the exported alphaL / alphaDen, betaN / betaDen are roots of q, h");
  printf("sizes: alpha %d bits, beta %d bits (largest numerator coordinate)\n", bits5(alphaL), bits5(betaN));
  system(Str("rm -f ", OUT));
  writebin(OUT, [EPS, EN, q, h, cK, fR, al, be, ZL, OML, thLi, ZN, OMN, ONN, thNi, MTL, MTLi, MTN, MTNi, aDen, alphaL, bDen, betaN, G2]);
  chk5(read(OUT)[8] == be, "cache /tmp/sb5/tower.bin written and read back");
  printf("DONE tower: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
