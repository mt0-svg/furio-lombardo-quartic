\\ w6_kernel_emulation_lib.gp: an exact emulation of the Lean kernel checks used by the
\\ w-place certificates, and the Lean mirrors that build their expressions.
\\ * KE expressions (lean/FurioLombardo/M1/Kron.lean): [0, a] = lin a (a a vector of integers, zk coordinates),
\\   [1, m] = int m, [2, e, f] = add, [3, e, f] = sub, [4, e, f] = mul. kedeg, kelen, kebnd, kevalN mirror
\\   KE.deg, KE.len 21, KE.bnd Dz 21 zkWb, KE.valN Dz; kecheck(e, k) is KE.check zkNum Dz fL 21 zkWb k e, i.e. checkK k e;
\\   keprec(e) is the least k (from the bound upward) with checkK k e = true.
\\ * Mirrors of PlaceWCert.lean: selJ, dpTab (dpStep, addT, addR, shiftD), truncT, combo, eRows, lcE, lhsAux, lhsL, rhsL
\\   and the three checks of certOK; of PlaceWModel.lean: LModel.ok, SqrtData.ok.
\\ The caller sets KZN (zkNum, 21 vectors, lowest coefficient first), KDZ (Dz), KFL (fL, constant first).
KWB = 10^25;
KLIN(a) = [0, a];
KINT(m) = [1, m];
KADD(e, f) = [2, e, f];
KSUB(e, f) = [3, e, f];
KMUL(e, f) = [4, e, f];
kesum(L) = if (#L == 0, KINT(0), #L == 1, L[1], KADD(L[1], kesum(L[2 .. #L])));
sumabs(a) = sum(i = 1, #a, abs(a[i]));
maxabs(a) = if (#a == 0, 0, vecmax(apply(abs, a)));
kedeg(e) = { my(t = e[1]); if (t == 0, 1, t == 1, 0, t == 4, kedeg(e[2]) + kedeg(e[3]), max(kedeg(e[2]), kedeg(e[3]))); }
kelen(e) = { my(t = e[1]); if (t == 0, 21, t == 1, 1, t == 4, kelen(e[2]) + kelen(e[3]) - 1, max(kelen(e[2]), kelen(e[3]))); }
kebnd(e) = {
  my(t = e[1]);
  if (t == 0, return(sumabs(e[2]) * KWB));
  if (t == 1, return(abs(e[2])));
  if (t == 4, return(kelen(e[2]) * kebnd(e[2]) * kebnd(e[3])));
  my(d1 = kedeg(e[2]), d2 = kedeg(e[3]), d = max(d1, d2));
  KDZ^(d - d1) * kebnd(e[2]) + KDZ^(d - d2) * kebnd(e[3]);
}
kevalN(e, WN) = {
  my(t = e[1]);
  if (t == 0, my(a = e[2]); return(sum(i = 1, min(#a, #WN), a[i] * WN[i])));
  if (t == 1, return(e[2]));
  if (t == 4, return(kevalN(e[2], WN) * kevalN(e[3], WN)));
  my(d1 = kedeg(e[2]), d2 = kedeg(e[3]), d = max(d1, d2), v1 = KDZ^(d - d1) * kevalN(e[2], WN), v2 = KDZ^(d - d2) * kevalN(e[3], WN));
  if (t == 2, v1 + v2, v1 - v2);
}
evalLN(N, l) = { my(r = 0); forstep (i = #l, 1, -1, r = r * N + l[i]); r; }
\\ balanced digits in base 2^k, lowest first (M1.Kron.digits)
kedigits(k, n, x) = { my(D = vector(n), B = 2^k); for (i = 1, n, my(r = x % B); if (2 * r > B, r -= B); D[i] = r; x = (x - r) / B); D; }
kecheck(e, k) = {
  my(N = 2^k, WN = apply(l -> evalLN(N, l), KZN), v = kevalN(e, WN), gN = evalLN(N, KFL), q, Q);
  if (v % gN != 0, return(0));
  q = v / gN; Q = kedigits(k, kelen(e), q);
  evalLN(N, Q) == q && 2 * (kebnd(e) + #KFL * maxabs(KFL) * maxabs(Q)) < 2^k;
}
keprec(e) = {
  my(b = kebnd(e), k = max(8, #binary(2 * b)));
  for (i = 0, 400, if (kecheck(e, k + i), return(k + i)));
  error("keprec: no precision found");
}
\\ ---------------------------------------------------------------- mirrors of PlaceWCert.lean
bitt(a, i) = bittest(a, i);
selJ(e, a) = [j | j <- [0 .. 2 * e - 1], bitt(a, j + 1)];
addR(r, s) = { my(n = max(#r, #s), o = vector(n)); for (i = 1, n, o[i] = if (i <= #r, r[i], 0) + if (i <= #s, s[i], 0)); o; }
addT(c, d) = { my(n = max(#c, #d), o = vector(n)); for (i = 1, n, o[i] = if (i > #c, d[i], i > #d, c[i], addR(c[i], d[i]))); o; }
shiftD(j, r) = concat(vector(j), r);
dpStep(j, c) = addT(c, concat([[]], apply(r -> shiftD(j, r), c)));
dpTab(S) = { my(c = [[1]]); forstep (i = #S, 1, -1, c = dpStep(S[i], c)); c; }
truncT(D, c) = apply(r -> r[1 .. min(D, #r)], c);
\\ combo r Ws: sum of r_d Ws_d over d < min(#r, #Ws) (zk vectors of length 21)
combo(r, Ws) = { my(n = min(#r, #Ws), o = vector(21)); if (n == 0, return([])); for (d = 1, n, o += r[d] * Ws[d]); o; }
\\ EisData as a Map: "e", "al", "A", "B", "cA", "bB", "alPow" (vector of zk vectors), "Ypow" (vector of pairs), "prec"
EalP(E, d) = my(P = mapget(E, "alPow")); if (d < #P, P[d + 1], []);
EYp(E, n) = my(P = mapget(E, "Ypow")); if (n < #P, P[n + 1], [[], []]);
eRows(E, D, a) = apply(r -> combo(r, mapget(E, "alPow")), truncT(D, dpTab(selJ(mapget(E, "e"), a))));
lcE(E, i, L) = kesum(apply(p -> KMUL(p[1], KLIN(EYp(E, p[2])[i + 1])), L));
lhsAux(f5, X0, X1, a0, n, rs) = { my(o = List()); for (k = 1, #rs, listput(o, [KMUL(f5, KMUL(KLIN(rs[k]), X0)), n + k - 1 + a0]); listput(o, [KMUL(f5, KMUL(KLIN(rs[k]), X1)), n + k - 1 + a0 + 1])); Vec(o); }
lhsL(E, D, X0, X1, a) = lhsAux(KINT(if (bitt(a, 2 * mapget(E, "e") + 1), 5, 1)), X0, X1, if (bitt(a, 0), 1, 0), 0, eRows(E, D, a));
\\ WCert as a vector [a, mh, ep, u0, c0, s1, n0, n1, R0, R1, prec]
rhsL(E, c) = { [[KMUL(KLIN(EalP(E, 2 * c[2])), KMUL(KLIN(c[4]), KLIN(c[4]))), 2 * c[3]],
  [KMUL(KLIN(EalP(E, 2 * c[2])), KMUL(KINT(2), KMUL(KLIN(c[4]), KLIN(c[6])))), 2 * c[3] + 1],
  [KMUL(KLIN(EalP(E, 2 * c[2])), KMUL(KLIN(c[6]), KLIN(c[6]))), 2 * c[3] + 2],
  [KMUL(KLIN(EalP(E, c[7])), KLIN(c[9])), 0], [KMUL(KLIN(EalP(E, c[8])), KLIN(c[10])), 1]]; }
certExprs(E, D, X0, X1, c) = { [KSUB(KLIN(c[4]), KADD(KINT(1), KMUL(KLIN(mapget(E, "al")), KLIN(c[5])))),
  KSUB(lcE(E, 0, lhsL(E, D, X0, X1, c[1])), lcE(E, 0, rhsL(E, c))),
  KSUB(lcE(E, 1, lhsL(E, D, X0, X1, c[1])), lcE(E, 1, rhsL(E, c)))]; }
certDecides(E, D, c) = { my(e = mapget(E, "e"), nP = #mapget(E, "alPow"), nY = #mapget(E, "Ypow"));
  2 * c[2] + c[3] + 2 * e < c[7] && 2 * c[2] + c[3] + 2 * e <= c[8] && c[7] <= D && D <= nP && 2 * c[2] < nP &&
  c[7] < nP && c[8] < nP && 2 * c[3] + 2 < nY && #eRows(E, D, c[1]) + 1 < nY; }
\\ certOK E D X0 X1 c with c[11] = prec
certOK(E, D, X0, X1, c) = certDecides(E, D, c) && vecmin(apply(x -> kecheck(x, c[11]), certExprs(E, D, X0, X1, c)));
\\ EisData.ok
eisExprs(E) = { my(o = List(), al = KLIN(mapget(E, "al")), nP = #mapget(E, "alPow"), nY = #mapget(E, "Ypow"));
  listput(o, KSUB(KLIN(mapget(E, "A")), KMUL(al, KADD(KINT(1), KMUL(al, KLIN(mapget(E, "cA")))))));
  listput(o, KSUB(KLIN(mapget(E, "B")), KMUL(al, KLIN(mapget(E, "bB")))));
  listput(o, KSUB(KLIN(EalP(E, 0)), KINT(1)));
  for (d = 0, nP - 2, listput(o, KSUB(KLIN(EalP(E, d + 1)), KMUL(KLIN(EalP(E, d)), al))));
  listput(o, KSUB(KLIN(EYp(E, 0)[1]), KINT(1))); listput(o, KLIN(EYp(E, 0)[2]));
  for (n = 0, nY - 2, listput(o, KSUB(KLIN(EYp(E, n + 1)[1]), KMUL(KLIN(mapget(E, "A")), KLIN(EYp(E, n)[2]))));
    listput(o, KSUB(KLIN(EYp(E, n + 1)[2]), KADD(KLIN(EYp(E, n)[1]), KMUL(KLIN(mapget(E, "B")), KLIN(EYp(E, n)[2]))))));
  Vec(o); }
