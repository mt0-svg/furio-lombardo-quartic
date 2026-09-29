\\ local_data_v.gp: the data of the place v (e = 3) for the Lean files
\\ Discharge/SelmerBasis/VData*.lean, in the formats of PlaceWCert.lean (WCert, EisData), PlaceWModel.lean (LModel),
\\ PlaceUCert.lean (UCert, SqrtV) and PointGen.lean (PtData, only the value fields), with every kernel check emulated
\\ exactly (../selmer-local-conditions/w6_kernel_emulation_lib.gp and the UCert mirrors below) and its precision chosen.
\\ Model: F1 = K_v[Y]/(Y^2 - B Y - A) Eisenstein, omega = y + c Y (c = alpha^((t - 1)/2), t the odd depth of eps),
\\ A = alpha (1 + alpha cA), B = alpha bB; basis of F1^x/F1^x2: Y, 1 + alpha^j Y (j = 0 .. 5), 5 (bits 0 .. 7).
\\ F2 = F1[zeta]/(zeta^2 - zeta + 1), unramified over F1; basis bU of PlaceUGen.lean: Y, 1 + Y^(2 (j/2) + 1) w_(j mod 2)
\\ (w = 1, zeta; j = 0 .. 11), 1 + 4 zeta (bits 0 .. 13). omega_N -> (2 zeta - 1) rho / 2 with 3 rho^2 = -iL(4 eN), rho in F1.
\\ K_v[T]/(fRev_k) = F1 x F2, T -> (iL(alphaR), iNv(betaR)); rows of G/G^2 have 22 bits: F1 at 0 .. 7, F2 at 8 .. 21.
\\ Elements certified: kappa (7, dyGen alpha i) at both components, the 29 gensL at F1, the 53 gensN at F2, and per
\\ twist the 7 points Dpt k i of SelmerSpan (exact U = X^2 + p X + r, p = pL/pM, r = rL/rM from DData.lean),
\\ through Lambda^2 U(alphaR) at F1 and Lambda^2 U(betaR) at F2.
\\ F_2 data per twist: the rows of kappa, mu, the 82 generators; forms QC annihilating kappa and mu with
\\ dotRow(Cg, QC_i) = the rows Cv of VPlace.lean; the coefficients cB of relAtV (sum of beta_j generator rows plus the
\\ SB_ij mu rows = the kappa rows selected by cB_j).
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-local-conditions/local_data_v.gp < /dev/null > ../selmer-local-conditions/local_data_v.out 2>&1
\\ Output: the Lean data files in /tmp/sv1/lean/ (copied into Discharge/SelmerBasis/, split by split_lean_data.sh, then compiled).
default(parisizemax, 3000 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp");
read("../selmer-local-conditions/selmer_rows_lib.gp"); read("../selmer-global-bound/tower_lib.gp"); read("../selmer-local-conditions/w6_kernel_emulation_lib.gp");
LEAN = "../../FurioLombardo/";
SUD = Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean");
OUTD = "/tmp/sv1/lean/";
SBu7 = -1;
T00 = getabstime();
\\ keprec of w6_kernel_emulation_lib.gp, faster on large expressions: after a few steps from the bound, the quotient
\\ digits at a safe precision give the needed precision directly (any passing k is valid for the check)
keprec(e) = {
  my(b = kebnd(e), k = max(8, #binary(2 * b)), k2, N, WN, v, gN, q, Q, k1);
  for (i = 0, 8, if (kecheck(e, k + i), return(k + i)));
  k2 = 2 * k + 64;
  for (r = 1, 6,
    N = 2^k2; WN = apply(l -> evalLN(N, l), KZN); v = kevalN(e, WN); gN = evalLN(N, KFL);
    if (v % gN != 0, error("keprec: not divisible"));
    q = v / gN; Q = kedigits(k2, kelen(e), q);
    if (evalLN(N, Q) == q && 4 * maxabs(Q) < 2^k2,
      k1 = #binary(2 * (b + #KFL * maxabs(KFL) * maxabs(Q)));
      for (i = 0, 40, if (kecheck(e, k1 + i), return(k1 + i))));
    k2 *= 2);
  error("keprec: no precision found");
}
zkc(z) = nfalgtobasis(nfK, z);
isint(z) = denominator(zkc(z)) == 1;
zkl(z) = { my(v = zkc(z)); if (denominator(v) != 1, error("zkl: not integral")); v~; }
lstr(v) = Str(v);
KL(l) = nfbasistoalg(nfK, KofList(l));
keval(e) = { my(tt = e[1]); if (tt == 0, if (#e[2] == 0, Mod(0, K21), nfbasistoalg(nfK, e[2]~)), tt == 1, Mod(e[2], K21), tt == 2, keval(e[2]) + keval(e[3]), tt == 3, keval(e[2]) - keval(e[3]), keval(e[2]) * keval(e[3])); }
sqclass(W, u) = {
  my(C0 = sb_comp(W, 1), al = mapget(W, "al"), e = mapget(W, "e"), NP = 2 * e + 8, z, rr, d, s = Mod(1, K21), tt = 0);
  z = redK(W, u, NP); rr = liftres(C0, ksqrt(C0, res(C0, z))); z = redK(W, z / rr^2, NP); s = s * rr;
  for (s1 = 1, 2 * e - 1, d = res(C0, redK(W, (z - 1) / al^s1, NP)); if (d == 0, next);
    if (s1 % 2, tt = s1; break); rr = 1 + al^(s1 / 2) * liftres(C0, ksqrt(C0, d)); z = redK(W, z / rr^2, NP); s = redK(W, s * rr, NP));
  if (!tt, my(d4 = res(C0, redK(W, (z - 1) / 4, NP))); tt = if (d4 == 0, 2 * e + 1, 2 * e));
  [tt, redK(W, s, NP)];
}
\\ ---------------------------------------------------------------- mirrors of PlaceUCert.lean
zmulU(p, q) = [p[1] * q[1] - p[2] * q[2], p[1] * q[2] + p[2] * q[1] + p[2] * q[2]];
addZL(P, Q) = { my(n = max(#P, #Q), o = vector(n)); for (i = 1, n, o[i] = if (i > #P, Q[i], i > #Q, P[i], P[i] + Q[i])); o; }
stepU(f, P) = addZL(P, concat(vector(f[1], i, [0, 0]), apply(z -> zmulU(f[2], z), P)));
dpU(F) = { my(P = [[1, 0]]); forstep (i = #F, 1, -1, P = stepU(F[i], P)); P; }
facU(ee, a) = concat([[2 * (j \ 2) + 1, if (j % 2 == 0, [1, 0], [0, 1])] | j <- [0 .. 2 * ee - 1], bittest(a, j + 1)], if (bittest(a, 2 * ee + 1), [[0, [0, 4]]], []));
\\ lhsUAux X0 X1 X2 X3 a0 n P: [terms on 1, terms on zeta]
lhsUAux(Xs, a0, n, P) = {
  my(L1 = List(), L2 = List());
  for (k = 1, #P, my(p1 = P[k][1], p2 = P[k][2], ix = n + k - 1 + a0);
    listput(L1, [KMUL(KINT(p1), Xs[1]), ix]); listput(L1, [KMUL(KINT(p1), Xs[2]), ix + 1]);
    listput(L1, [KMUL(KINT(-p2), Xs[3]), ix]); listput(L1, [KMUL(KINT(-p2), Xs[4]), ix + 1]);
    listput(L2, [KMUL(KINT(p2), Xs[1]), ix]); listput(L2, [KMUL(KINT(p2), Xs[2]), ix + 1]);
    listput(L2, [KMUL(KINT(p1 + p2), Xs[3]), ix]); listput(L2, [KMUL(KINT(p1 + p2), Xs[4]), ix + 1]));
  [Vec(L1), Vec(L2)];
}
lhsU(E, D, Xs, a) = { my(P = dpU(facU(2 * mapget(E, "e"), a))); lhsUAux(Xs, if (bittest(a, 0), 1, 0), 0, P[1 .. min(D, #P)]); }
\\ UCert as a vector [a, mh, ub, u0, u1, s0, s1, c0, n, R00, R01, R10, R11, prec]
rhsU(E, c) = {
  my(u0 = KLIN(c[4]), u1 = KLIN(c[5]), s0 = KLIN(c[6]), s1 = KLIN(c[7]), m = 2 * c[2], al = KLIN(EalP(E, c[9])));
  [[[KSUB(KMUL(u0, u0), KMUL(s0, s0)), m], [KMUL(KINT(2), KSUB(KMUL(u0, u1), KMUL(s0, s1))), m + 1],
     [KSUB(KMUL(u1, u1), KMUL(s1, s1)), m + 2], [KMUL(al, KLIN(c[10])), 0], [KMUL(al, KLIN(c[11])), 1]],
   [[KADD(KMUL(KINT(2), KMUL(u0, s0)), KMUL(s0, s0)), m],
     [KADD(KMUL(KINT(2), KADD(KMUL(u0, s1), KMUL(u1, s0))), KMUL(KINT(2), KMUL(s0, s1))), m + 1],
     [KADD(KMUL(KINT(2), KMUL(u1, s1)), KMUL(s1, s1)), m + 2], [KMUL(al, KLIN(c[12])), 0], [KMUL(al, KLIN(c[13])), 1]]];
}
certExprsU(E, D, Xs, c) = {
  my(L = lhsU(E, D, Xs, c[1]), R = rhsU(E, c));
  [KSUB(KLIN(if (c[3], c[6], c[4])), KADD(KINT(1), KMUL(KLIN(mapget(E, "al")), KLIN(c[8])))),
   KSUB(lcE(E, 0, L[1]), lcE(E, 0, R[1])), KSUB(lcE(E, 1, L[1]), lcE(E, 1, R[1])),
   KSUB(lcE(E, 0, L[2]), lcE(E, 0, R[2])), KSUB(lcE(E, 1, L[2]), lcE(E, 1, R[2]))];
}
certDecidesU(E, D, c) = { my(ee = mapget(E, "e"), nP = #mapget(E, "alPow"), nY = #mapget(E, "Ypow"));
  2 * c[2] + 4 * ee < 2 * c[9] && 2 * c[9] <= D && c[9] < nP && D + 1 < nY && 2 * c[2] + 2 < nY; }
certOKU(E, D, Xs, c) = certDecidesU(E, D, c) && vecmin(apply(q -> kecheck(q, c[14]), certExprsU(E, D, Xs, c)));
\\ ---------------------------------------------------------------- stage 0: global data
sb_init();
KZN = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"); KDZ = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz");
KFL = leandef5(Str(LEAN, "M1/Basic.lean"), "fL");
chq(vector(21, j, Pol(Vecrev(KZN[j]), 'b) / KDZ) == nfK.zk, "nfK.zk = M1's zkNum / Dz");
chq(Pol(Vecrev(KFL), 'b) == K21, "M1's fL = K21");
EPSa = KL(leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL"));
EAL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL"); EBL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL");
EA = KL(EAL); EB = KL(EBL);
ALs = leandef5(SUD, "alphaL"); ADn = leandef5(SUD, "alphaDen"); BNs = leandef5(SUD, "betaN"); BDn = leandef5(SUD, "betaDen");
BPD = leandef5(SUD, "betaPowDen");
tabA = vector(6, i, leandef5(SUD, Str("alphaPow_", i - 1))); tabB = vector(6, i, leandef5(SUD, Str("betaPow_", i - 1)));
gLs = vector(29, s1, leandef5(SUD, Str("gL_", s1 - 1))); gNs = vector(53, s1, leandef5(SUD, Str("gN_", s1 - 1)));
Lmul(x, y) = [x[1] * y[1] + EPSa * x[2] * y[2], x[1] * y[2] + x[2] * y[1]];
Ladd(x, y) = [x[1] + y[1], x[2] + y[2]];
Lsc(c, x) = [c * x[1], c * x[2]];
EN = [EA / 2, EB / 2];
Nmul(x, y) = [Ladd(Lmul(x[1], y[1]), Lmul(EN, Lmul(x[2], y[2]))), Ladd(Lmul(x[1], y[2]), Lmul(x[2], y[1]))];
Nadd(x, y) = [Ladd(x[1], y[1]), Ladd(x[2], y[2])];
Nsc(c, x) = [Lsc(c, x[1]), Lsc(c, x[2])];
alR = [KL(ALs[1]) / ADn, KL(ALs[2]) / ADn];
beR = [[KL(BNs[1]) / BDn, KL(BNs[2]) / BDn], [KL(BNs[3]) / BDn, KL(BNs[4]) / BDn]];
chq(Lmul(alR, alR) != 0 && subst(SBq, x, 'Z) != 0, "alphaR read");
\\ ---------------------------------------------------------------- stage 1: the model at v
W = sb_place(1); e = mapget(W, "e"); al = mapget(W, "al");
chq(e == 3 && zkl(al) == leandef5(Str(LEAN, "M2/SpecialData.lean"), "al1"), "v: e = 3, al = Lean's al1");
sc = sqclass(W, EPSa); TE = sc[1];
chq(vw(W, EPSa) == 0 && TE % 2 == 1 && TE < 2 * e, Str("v: eps is a unit of odd depth ", TE));
yy = Mod(lift(sc[2]), K21); cc = al^((TE - 1) / 2); A = (EPSa - yy^2) / cc^2; B = -2 * yy / cc;
cA = (A / al - 1) / al; bB = B / al;
chq(isint(yy) && isint(A) && isint(B) && isint(cA) && isint(bB) && vw(W, A) == 1, "v: y, A, B, cA = (A/al - 1)/al, bB = B/al in O_K21, A of valuation 1");
C1 = sb_comp(W, 2, A, B, 1); one1 = mapget(C1, "one");
mybas = concat([[Y1 * one1], vector(2 * e, j, one1 * (1 + al^(j - 1) * Y1)), [5 * one1]]);
mapput(C1, "bas", mybas);
chq(vector(2 * e + 2, i, coords(C1, mybas[i])[1]) == vector(2 * e + 2, i, vector(2 * e + 2, l, l == i)), "F1: the coordinates of the basis bF are the unit vectors");
C2 = sb_comp(W, 4, A, B, 1); one2 = mapget(C2, "one");
bUl(i) = if (i == 0, Y1 * one2, i == 4 * e + 1, one2 * (1 + 4 * Y2), one2 * (1 + Y1^(2 * ((i - 1) \ 2) + 1) * if ((i - 1) % 2 == 0, 1, Y2)));
chq(mapget(C2, "bas") == vector(4 * e + 2, i, bUl(i - 1)), "F2: the standard basis of selmer_rows_lib is bU of PlaceUGen.lean (pi = Y, e = 6)");
chq(vector(4 * e + 2, i, coords(C2, bUl(i - 1))[1]) == vector(4 * e + 2, i, vector(4 * e + 2, l, l == i)), "F2: the coordinates of the basis bU are the unit vectors");
toFv(u, v) = one1 * (u + v * Y1);
toUv(v) = one2 * (v[1] + v[2] * Y1 + (v[3] + v[4] * Y1) * Y2);
iLv(z) = one1 * (z[1] + z[2] * (yy + cc * Y1));
iL2(z) = one2 * (z[1] + z[2] * (yy + cc * Y1));
chq(iLv([0, 1])^2 == EPSa * one1, "v: (y + c Y)^2 = eps in K21[Y]/(P1)");
NPF = 800;
z4 = toFv(2 * EA + 2 * EB * yy, 2 * EB * cc);
chq(iLv([2 * EA, 2 * EB]) == z4, "iL(4 eN) = toF(2 ea + 2 eb y, 2 eb c)");
z3 = -z4 / 3;
ce = coords(C1, red(C1, z3, 60)); chq(ce[1] == 0 * ce[1] && ce[2] % 2 == 0, Str("-iL(4 eN)/3 is a square in F1 (valuation ", 2 * ce[2], ")"));
rho = red(C1, Y1^ce[2] * one1 * ce[3], NPF);
for (it = 1, 12, rho = red(C1, (rho + z3 / rho) / 2, NPF));
chq(val(C1, rho^2 - z3) >= NPF / 2, Str("rho^2 = -iL(4 eN)/3 to F1-valuation ", val(C1, rho^2 - z3)));
ivN(z) = iL2(z[1]) + iL2(z[2]) * (2 * Y2 - 1) * rho / 2;
chq(ivN([[0, 0], [1, 0]])^2 == iL2(EN) * one2 || val(C2, ivN([[0, 0], [1, 0]])^2 - iL2(EN)) >= NPF / 2, "iNv(w_N)^2 = iL(eN) to high precision");
taus = [iLv(alR), ivN(beR)];
chq(subst(SBq, x, taus[1]) == 0 && val(C2, subst(SBh, x, taus[2])) >= NPF / 4, "q(tau1) = 0 exactly, h(tau2) = 0 to high precision");
\\ ---------------------------------------------------------------- stage 2: certificates
LM = Map(); mapput(LM, "y", zkl(yy)); mapput(LM, "c", zkl(cc));
X0L(t) = KADD(t[1], KMUL(t[2], KLIN(mapget(LM, "y"))));
X1L(t) = KMUL(t[2], KLIN(mapget(LM, "c")));
\\ XNv E M S t: the coordinates on 1, Y, zeta, Y zeta of iL(t1) + iL(t2) (2 zeta - 1) s0
XNv(t) = { my(P0, P1, Q0 = X0L(t[2]), Q1 = X1L(t[2]));
  P0 = KADD(KMUL(Q0, KLIN(SV[3])), KMUL(KMUL(Q1, KLIN(SV[4])), KLIN(zkl(A))));
  P1 = KADD(KADD(KMUL(Q0, KLIN(SV[4])), KMUL(Q1, KLIN(SV[3]))), KMUL(KMUL(Q1, KLIN(SV[4])), KLIN(zkl(B))));
  [KSUB(X0L(t[1]), P0), KSUB(X1L(t[1]), P1), KMUL(KINT(2), P0), KMUL(KINT(2), P1)]; }
NCERT = 0; NCERTU = 0; MAXN0 = 0; MAXNU = 0; MAXPREC = 0; MAXD = 0;
STG = 0; NSTG = 5;
\\ one certificate at F1 for the exact element toF(keval X0e, keval X1e); returns [cert, bitvector, m]
mkcert(X0e, X1e, name) = {
  my(X = toFv(keval(X0e), keval(X1e)), ce, av, m, S, ep, mh, S2, cS, c0, s1, u0, n0, n1, D, aa, rows, Btr, f5, a0, R, cR, R0, R1, cert, pr);
  if (val(C1, X) < 0, error("mkcert: not integral: ", name));
  ce = coords(C1, X); if (!verC(C1, X, ce), error("mkcert: verC failed for ", name));
  av = ce[1]; m = ce[2]; S = ce[3]; ep = m % 2; mh = (m - ep) / 2;
  S2 = red(C1, (Y1^2 * one1 / al)^mh * S, 2 * m + 60);
  cS = co(C1, S2); u0 = cS[1]; c0 = (u0 - 1) / al; s1 = cS[2];
  if (!isint(c0) || !isint(s1), error("mkcert: S'' not (1 + al c0) + s1 Y for ", name));
  n0 = 2 * mh + ep + 2 * e + 1; n1 = n0 - 1; D = n0;
  aa = sum(i = 1, #av, av[i] * 2^(i - 1));
  rows = eRows(EE, D, aa);
  f5 = if (bitt(aa, 2 * e + 1), 5, 1); a0 = if (bitt(aa, 0), 1, 0);
  Btr = f5 * (Y1 * one1)^a0 * sum(k = 1, #rows, (if (#rows[k] == 0, 0, nfbasistoalg(nfK, rows[k]~))) * (Y1 * one1)^(k - 1));
  R = X * Btr - al^(2 * mh) * (Y1 * one1)^(2 * ep) * (u0 + s1 * Y1)^2;
  cR = co(C1, R); R0 = cR[1] / al^n0; R1 = cR[2] / al^n1;
  if (!isint(R0) || !isint(R1), error("mkcert: remainder not integral for ", name, ": v = ", vw(W, cR[1]), ", ", vw(W, cR[2]), ", n0 = ", n0));
  cert = [aa, mh, ep, zkl(u0), zkl(c0), zkl(s1), n0, n1, zkl(R0), zkl(R1), 0];
  if (!certDecides(EE, D, cert), error("mkcert: the tables of E are too short for ", name, " (n0 = ", n0, ", D = ", D, ")"));
  pr = vecmax(apply(keprec, certExprs(EE, D, X0e, X1e, cert))); cert[11] = pr;
  if (!certOK(EE, D, X0e, X1e, cert), error("mkcert: certOK fails for ", name));
  NCERT++; MAXN0 = max(MAXN0, n0); MAXPREC = max(MAXPREC, pr);
  [cert, av, m];
}
certstr(c) = Str("⟨", c[1], ", ", c[2], ", ", c[3], ", ", lstr(c[4]), ", ", lstr(c[5]), ", ", lstr(c[6]), ", ", c[7], ", ", c[8], ", ", lstr(c[9]), ", ", lstr(c[10]), ", ", c[11], "⟩");
\\ one certificate at F2 for the exact element toU(keval Xe[1..4]), truncation D = 2 n; returns [cert, bitvector, m]
mkcertU(Xe, name) = {
  my(X = toUv(apply(keval, Xe)), ce, av, m, S, n, D, aa, a0, P, Btr, Z, cS, ub, c0, R, cR, RR, cert, pr, Yo = Y1 * one2);
  if (val(C2, X) < 0, error("mkcertU: not integral: ", name));
  ce = coords(C2, X); if (!verC(C2, X, ce), error("mkcertU: verC failed for ", name));
  av = ce[1]; m = ce[2]; S = ce[3];
  n = m + 2 * e + 1; D = 2 * n;
  aa = sum(i = 1, #av, av[i] * 2^(i - 1)); a0 = av[1];
  P = dpU(facU(2 * e, aa)); P = P[1 .. min(D, #P)];
  Btr = Yo^a0 * sum(k = 1, #P, (P[k][1] + P[k][2] * Y2) * Yo^(k - 1));
  Z = red(C2, X * Btr / Yo^(2 * m), D + 20);
  for (it = 1, 4, S = red(C2, (S + Z / S) / 2, D + 20));
  if (val(C2, S) != 0 || val(C2, Z - S^2) < D - 2 * m + 2, error("mkcertU: Newton for ", name));
  cS = co(C2, S);
  if (vw(W, cS[1]) == 0, ub = 0; c0 = (cS[1] - 1) / al, ub = 1; c0 = (cS[3] - 1) / al; if (vw(W, cS[3]) != 0, error("mkcertU: no unit coordinate for ", name)));
  if (!isint(c0) || !vecmin(apply(isint, cS)), error("mkcertU: S not integral or unit coordinate not 1 + al c0 for ", name));
  R = X * Btr - Yo^(2 * m) * S^2;
  cR = co(C2, R); RR = apply(r -> r / al^n, cR);
  if (!vecmin(apply(isint, RR)), error("mkcertU: remainder not integral for ", name, ": v = ", apply(r -> vw(W, r), cR), ", n = ", n));
  cert = [aa, m, ub, zkl(cS[1]), zkl(cS[2]), zkl(cS[3]), zkl(cS[4]), zkl(c0), n, zkl(RR[1]), zkl(RR[2]), zkl(RR[3]), zkl(RR[4]), 0];
  if (!certDecidesU(EE, D, cert), error("mkcertU: the tables of E are too short for ", name, " (m = ", m, ", n = ", n, ", D = ", D, ")"));
  pr = vecmax(apply(keprec, certExprsU(EE, D, Xe, cert))); cert[14] = pr;
  if (!certOKU(EE, D, Xe, cert), error("mkcertU: certOKU fails for ", name));
  NCERTU++; MAXNU = max(MAXNU, n); MAXPREC = max(MAXPREC, pr); MAXD = max(MAXD, D);
  [cert, av, m];
}
certstrU(c) = Str("⟨", c[1], ", ", c[2], ", ", if (c[3], "true", "false"), ", ", lstr(c[4]), ", ", lstr(c[5]), ", ", lstr(c[6]), ", ", lstr(c[7]), ", ", lstr(c[8]), ", ", c[9], ", ", lstr(c[10]), ", ", lstr(c[11]), ", ", lstr(c[12]), ", ", lstr(c[13]), ", ", c[14], "⟩");
\\ EisData (alPow up to DP, Ypow up to NYP)
DP = 160; NYP = 160;
EE = Map(); mapput(EE, "e", e); mapput(EE, "al", zkl(al)); mapput(EE, "A", zkl(A)); mapput(EE, "B", zkl(B));
mapput(EE, "cA", zkl(cA)); mapput(EE, "bB", zkl(bB));
mapput(EE, "alPow", vector(DP + 1, d, zkl(al^(d - 1))));
mapput(EE, "Ypow", vector(NYP + 1, n, my(v = co(C1, (Y1 * one1)^(n - 1))); [zkl(v[1]), zkl(v[2])]));
EPREC = vecmax(apply(keprec, eisExprs(EE))); mapput(EE, "prec", EPREC);
chq(vecmin(apply(q -> kecheck(q, EPREC), eisExprs(EE))), Str("EisData.ok at precision ", EPREC));
{LMX = [KSUB(KADD(KMUL(KLIN(zkl(yy)), KLIN(zkl(yy))), KMUL(KMUL(KLIN(zkl(cc)), KLIN(zkl(cc))), KLIN(zkl(A)))), KLIN(zkl(EPSa))),
  KADD(KMUL(KINT(2), KLIN(zkl(yy))), KMUL(KLIN(zkl(cc)), KLIN(zkl(B))))];}
LPREC = vecmax(apply(keprec, LMX)); chq(vecmin(apply(q -> kecheck(q, LPREC), LMX)), Str("LModel.ok at precision ", LPREC));
chq(zkl(EPSa) == leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL"), "epsL read back");
\\ SqrtV at precision NS (alpha units): s0 = rho reduced, 3 s0^2 + iL(4 eN) = al^NS (R0 + R1 Y)
NS = 120;
s0 = red(C1, rho, 2 * NS + 4); cs0 = co(C1, s0);
SJ = vw(W, cs0[1]); chq(vw(W, cs0[2]) >= SJ, Str("s0 = al^", SJ, " (unit) + al^", SJ, " (int) Y"));
sd0 = (cs0[1] / al^SJ - 1) / al; sd1 = cs0[2] / al^SJ;
cr = co(C1, 3 * s0^2 + z4); sR0 = cr[1] / al^NS; sR1 = cr[2] / al^NS;
chq(isint(sd0) && isint(sd1) && isint(sR0) && isint(sR1), "SqrtV: d0, d1, R0, R1 integral");
SV = [SJ, NS, zkl(cs0[1]), zkl(cs0[2]), zkl(sd0), zkl(sd1), zkl(sR0), zkl(sR1), 0];
{SVX = [KSUB(KLIN(SV[3]), KMUL(KLIN(EalP(EE, SJ)), KADD(KINT(1), KMUL(KLIN(zkl(al)), KLIN(SV[5]))))),
  KSUB(KLIN(SV[4]), KMUL(KLIN(EalP(EE, SJ)), KLIN(SV[6]))),
  KSUB(KADD(KMUL(KINT(3), KADD(KMUL(KLIN(SV[3]), KLIN(SV[3])), KMUL(KMUL(KLIN(SV[4]), KLIN(SV[4])), KLIN(zkl(A))))),
    KMUL(KINT(2), KADD(KLIN(EAL), KMUL(KLIN(EBL), KLIN(zkl(yy)))))), KMUL(KLIN(EalP(EE, NS)), KLIN(SV[7]))),
  KSUB(KADD(KMUL(KINT(3), KADD(KMUL(KINT(2), KMUL(KLIN(SV[3]), KLIN(SV[4]))), KMUL(KMUL(KLIN(SV[4]), KLIN(SV[4])), KLIN(zkl(B))))),
    KMUL(KINT(2), KMUL(KLIN(EBL), KLIN(zkl(cc))))), KMUL(KLIN(EalP(EE, NS)), KLIN(SV[8])))];}
SV[9] = vecmax(apply(keprec, SVX));
chq(vecmin(apply(q -> kecheck(q, SV[9]), SVX)) && NS < DP + 1 && SJ + 1 < DP + 1 && 2 * e + 2 * SJ < NS, Str("SqrtV.ok at precision ", SV[9]));
SNB = NS - e - SJ;  \\ ||iNv(evN t) - toU(XNv t)|| <= ||al||^SNB
printf("  model: t = %d, EisData prec %d, LModel prec %d, SqrtV j = %d prec %d, iNv within al^%d\n", TE, EPREC, LPREC, SJ, SV[9], SNB);
\\ kappa at F1 and F2
KAPX = vector(2 * e + 1, i, if (i == 1, KLIN(zkl(al)), KADD(KINT(1), KLIN(EalP(EE, i - 1)))));
chq(vector(2 * e + 1, i, keval(KAPX[i])) == concat([al], vector(2 * e, i, 1 + al^i)), "kappa expressions = dyGen alpha i");
t0 = getabstime();
KAPC1 = vector(2 * e + 1, i, mkcert(KAPX[i], KINT(0), Str("kappa ", i - 1, " at F1")));
KAPC2 = vector(2 * e + 1, i, mkcertU([KAPX[i], KINT(0), KINT(0), KINT(0)], Str("kappa ", i - 1, " at F2")));
printf("  kappa: 2 x 7 certificates (%d ms)\n", getabstime() - t0);
ofL(l) = [KLIN(l[1]), KLIN(l[2])];
ofN(l) = [[KLIN(l[1]), KLIN(l[2])], [KLIN(l[3]), KLIN(l[4])]];
t0 = getabstime();
GLC = vector(29, s1, my(tt = ofL(gLs[s1])); mkcert(X0L(tt), X1L(tt), Str("gL ", s1 - 1)));
printf("  gensL: 29 certificates at F1 (%d ms)\n", getabstime() - t0);
chq(vector(29, s1, toFv(keval(X0L(ofL(gLs[s1]))), keval(X1L(ofL(gLs[s1])))) == iLv([KL(gLs[s1][1]), KL(gLs[s1][2])])), "toF(X0L, X1L) = iL(gensL s)");
t0 = getabstime();
GNC = vector(53, s1, mkcertU(XNv(ofN(gNs[s1])), Str("gN ", s1 - 1)));
printf("  gensN: 53 certificates at F2 (%d ms)\n", getabstime() - t0);
{
  my(okN = 1);
  for (s1 = 1, 53, my(xN = ivN([[KL(gNs[s1][1]), KL(gNs[s1][2])], [2 * KL(gNs[s1][3]), 2 * KL(gNs[s1][4])]]));
    if (val(C2, xN - toUv(apply(keval, XNv(ofN(gNs[s1]))))) < 2 * GNC[s1][1][9], okN = 0));
  chq(okN, "toU(XNv) within al^n of iNv(gensN s)");
  chq(MAXNU <= SNB, Str("every UCert n so far (max ", MAXNU, ") is at most the SqrtV precision ", SNB));
  STG++;
}
\\ ---------------------------------------------------------------- stage 3: points (exact U of SelmerSpan)
zeroLCk = [KINT(0), KINT(0)];
addLCk(x, y) = [KADD(x[1], y[1]), KADD(x[2], y[2])];
smulLCk(c, x) = [KMUL(c, x[1]), KMUL(c, x[2])];
sumPLk(Dn, n, cs, P) = if (#cs == 0 || #P == 0, zeroLCk, addLCk(smulLCk(KMUL(cs[1], KINT(Dn^n)), P[1]), sumPLk(Dn, max(n - 1, 0), cs[2 .. #cs], P[2 .. #P])));
sumPNk(Dn, n, cs, P) = if (#cs == 0 || #P == 0, [zeroLCk, zeroLCk], my(r = sumPNk(Dn, max(n - 1, 0), cs[2 .. #cs], P[2 .. #P]), c = KMUL(cs[1], KINT(Dn^n))); [addLCk(smulLCk(c, P[1][1]), r[1]), addLCk(smulLCk(c, P[1][2]), r[2])]);
tabAk = apply(ofL, tabA); tabBk = apply(ofN, tabB);
tExprs(pt, lamL, tL, lamN, tN) = {
  my(P = KLIN(zkl(pt[1])), R = KLIN(zkl(pt[2])), d = pt[3], csL, csN, sL, sN, rL, rN);
  csL = [KMUL(KINT(lamL^2 / d), R), KMUL(KINT(lamL^2 / d), P), KINT(lamL^2)];
  csN = [KMUL(KINT(lamN^2 / d), R), KMUL(KINT(lamN^2 / d), P), KINT(lamN^2)];
  sL = sumPLk(ADn, 2, csL, tabAk); rL = smulLCk(KINT(ADn^2), [KLIN(tL[1]), KLIN(tL[2])]);
  sN = sumPNk(BPD, 2, csN, tabBk); rN = [smulLCk(KINT(BPD^2), [KLIN(tN[1]), KLIN(tN[2])]), smulLCk(KINT(BPD^2), [KLIN(tN[3]), KLIN(tN[4])])];
  [KSUB(sL[1], rL[1]), KSUB(sL[2], rL[2]), KSUB(sN[1][1], rN[1][1]), KSUB(sN[1][2], rN[1][2]), KSUB(sN[2][1], rN[2][1]), KSUB(sN[2][2], rN[2][2])];
}
mucoords1(z) = { my(v = val(C1, z), k = if (v < 0, ceil(-v / 2), 0)); coords(C1, red(C1, z * al^(2 * k), NPF))[1]; }
mucoords2(z) = { my(v = val(C2, z), k = if (v < 0, ceil(-v / 2), 0)); coords(C2, red(C2, z * al^(2 * k), NPF))[1]; }
DDL = Str(LEAN, "Discharge/SelmerSpan/DData.lean");
PDA = leandef5(DDL, "pData"); RDA = leandef5(DDL, "rData"); PDE = leandef5(DDL, "pDen"); RDE = leandef5(DDL, "rDen");
PTS = vector(2); MUD = vector(2);
t0 = getabstime();
{
for (KT = 0, 1,
  my(out = List());
  for (i = 1, 7,
    my(pL = PDA[KT + 1][i], rL = RDA[KT + 1][i], pM = PDE[KT + 1][i], rM = RDE[KT + 1][i], d, P, R, pp, rr, U, Lv, Nv, lamL, lamN, tL, tN, ex, prT, cm, pt);
    d = lcm(pM, rM); P = (d / pM) * pL; R = (d / rM) * rL;
    pp = KL(P) / d; rr = KL(R) / d;
    chq(pp == KL(pL) / pM && rr == KL(rL) / rM, Str("twist ", KT, " point ", i - 1, ": P/d = pL/pM, R/d = rL/rM"));
    U = x^2 + pp * x + rr;
    Lv = Ladd(Ladd(Lmul(alR, alR), Lsc(pp, alR)), [rr, 0]);
    Nv = Nadd(Nadd(Nmul(beR, beR), Nsc(pp, beR)), [[rr, 0], [0, 0]]);
    lamL = d * ADn; while (!isint(lamL^2 * Lv[1]) || !isint(lamL^2 * Lv[2]), lamL *= 2);
    lamN = 2 * d * BDn; while (!isint(lamN^2 * Nv[1][1]) || !isint(lamN^2 * Nv[1][2]) || !isint(lamN^2 * Nv[2][1] / 2) || !isint(lamN^2 * Nv[2][2] / 2), lamN *= 2);
    tL = [zkl(lamL^2 * Lv[1]), zkl(lamL^2 * Lv[2])];
    tN = [zkl(lamN^2 * Nv[1][1]), zkl(lamN^2 * Nv[1][2]), zkl(lamN^2 * Nv[2][1] / 2), zkl(lamN^2 * Nv[2][2] / 2)];
    pt = [P, R, d];
    ex = tExprs([KL(P), KL(R), d], lamL, tL, lamN, tN);
    for (q = 1, #ex, if (keval(ex[q]) != 0, error("t check ", q, " is not an identity (twist ", KT, ", point ", i, ")")));
    prT = vecmax(apply(keprec, ex));
    if (!vecmin(apply(q -> kecheck(q, prT), ex)), error("t checks"));
    if ((lamL^2) % d != 0 || (lamN^2) % d != 0, error("d does not divide Lambda^2"));
    my(tLk = [KLIN(tL[1]), KLIN(tL[2])], tNk = [[KLIN(tN[1]), KLIN(tN[2])], [KLIN(tN[3]), KLIN(tN[4])]]);
    cm = [mkcert(X0L(tLk), X1L(tLk), Str("mu k", KT, " i", i - 1, " at F1")), mkcertU(XNv(tNk), Str("mu k", KT, " i", i - 1, " at F2"))];
    if (cm[1][2] != mucoords1(subst(U, x, taus[1])) || cm[2][2] != mucoords2(subst(U, x, taus[2])), error("mu class mismatch (twist ", KT, ", point ", i - 1, ")"));
    if (toFv(keval(X0L(tLk)), keval(X1L(tLk))) != lamL^2 * subst(U, x, taus[1]), error("tL value"));
    if (val(C2, toUv(apply(keval, XNv(tNk))) - lamN^2 * subst(U, x, taus[2])) < 2 * cm[2][1][9], error("tN value"));
    printf("  twist %d point %d: d %d bits, lamL %d bits, lamN %d bits, prT %d, F1 n0 %d prec %d, F2 n %d prec %d (%d ms)\n", KT, i - 1, #binary(d), #binary(lamL), #binary(lamN), prT, cm[1][1][7], cm[1][1][11], cm[2][1][9], cm[2][1][14], getabstime() - t0);
    listput(out, [zkl(KL(P)), zkl(KL(R)), d, lamL, tL, lamN, tN, prT, cm]));
  MUD[KT + 1] = Vec(out));
  STG++;
}
printf("  mu: 2 x 7 points, 28 certificates (%d ms); max n0 %d, max UCert n %d (SqrtV precision %d), max D %d, max prec %d\n", getabstime() - t0, MAXN0, MAXNU, SNB, MAXD, MAXPREC);
chq(MAXNU <= SNB, "every UCert n is at most the SqrtV precision");
chq(MAXN0 + 1 <= DP && MAXNU + 1 <= DP, "alPow covers every n");
chq(MAXD + 2 <= NYP + 1, "Ypow covers every truncation of the UCerts");
\\ ---------------------------------------------------------------- stage 4: F_2 data
NB1 = 2 * e + 2; NB2 = 4 * e + 2; NB = NB1 + NB2;
rowOf(b1, b2) = sum(i = 1, NB1, b1[i] * 2^(i - 1)) + sum(i = 1, NB2, b2[i] * 2^(NB1 + i - 1));
AKAP = vector(2 * e + 1, i, rowOf(KAPC1[i][2], KAPC2[i][2]));
CGB = vector(82, s1, if (s1 <= 29, rowOf(GLC[s1][2], vector(NB2)), rowOf(vector(NB1), GNC[s1 - 29][2])));
AMU = vector(2, KT, vector(7, i, rowOf(MUD[KT][i][9][1][2], MUD[KT][i][9][2][2])));
f2m(rows, nb) = matrix(#rows, nb, r, j, bittest(rows[r], j - 1));
annRows(rows, nb) = { my(K = lift(matker(Mod(f2m(rows, nb), 2)))); vector(#K, j, sum(i = 1, nb, K[i, j] * 2^(i - 1))); }
dotB(q, v) = hammingweight(bitand(q, v)) % 2;
chq(f2rank(f2m(AKAP, NB)) == 4, "the 7 kappa rows have rank 4 (K_v^x / K_v^x2 of dimension 5, kernel {1, eps})");
VPL = Str(LEAN, "Discharge/SelmerBasis/VPlace.lean");
CVR = leandef5(VPL, "CvRows"); BTR = leandef5(VPL, "βRows");
M4D = Str(LEAN, "M4/Data.lean");
SBM = [leandef5(M4D, "SB"), leandef5(M4D, "SB", "namespace T1")];
chq(SBM[1] != SBM[2] && matsize(SBM[1]) == [7, 4], "SB of T0 and T1 read from M4/Data.lean");
QCV = vector(2); CBV = vector(2); SBB = vector(2);
{
for (KT = 1, 2,
  my(Q, Cp, Mq, Cv, Mm, QV, ok, sp, cb);
  chq(f2rank(f2m(concat(AKAP, AMU[KT]), NB)) == 11, Str("twist ", KT - 1, ": kappa and mu span 11 dimensions (4 + 7)"));
  Q = annRows(concat(AKAP, AMU[KT]), NB);
  chq(#Q == 11, Str("twist ", KT - 1, ": 11 forms annihilating kappa and mu"));
  Cp = matrix(11, 82, r, s1, dotB(Q[r], CGB[s1]));
  Cv = matrix(11, 82, r, s1, bittest(CVR[KT][r], s1 - 1));
  chq(f2rank(Cp) == 11 && f2eqspan(Cp~, Cv~), Str("twist ", KT - 1, ": the rows from the forms span the rows Cv of VPlace.lean (rank 11)"));
  \\ Cv = Mm Cp over F_2: Cp~ Mm~ = Cv~
  Mm = lift(matinverseimage(Mod(Cp~, 2), Mod(Cv~, 2)))~;
  chq(Mod(Mm * Cp - Cv, 2) == 0, Str("twist ", KT - 1, ": Cv = M Cp"));
  QV = vector(11, r, my(q = 0); for (j = 1, 11, if (Mm[r, j] % 2, q = bitxor(q, Q[j]))); q);
  ok = 1; for (r = 1, 11, for (s1 = 1, 82, if (dotB(QV[r], CGB[s1]) != bittest(CVR[KT][r], s1 - 1), ok = 0)));
  chq(ok, Str("twist ", KT - 1, ": dotRow(Cg, QC_r) = Cv row r for all 11 rows"));
  ok = 1; for (r = 1, 11, for (l = 1, 7, if (dotB(QV[r], AKAP[l]) || dotB(QV[r], AMU[KT][l]), ok = 0)));
  chq(ok, Str("twist ", KT - 1, ": the forms QC annihilate kappa and mu"));
  QCV[KT] = QV;
  \\ relAtV: v_j = sum_s beta_js Cg_s + sum_i SB_ij Amu_i in span(kappa)
  SBB[KT] = vector(4, j, sum(i = 1, 7, (SBM[KT][i, j] % 2) * 2^(i - 1)));
  cb = vector(4);
  for (j = 1, 4,
    my(vj = 0, sol);
    for (s1 = 1, 82, if (bittest(BTR[KT][j], s1 - 1), vj = bitxor(vj, CGB[s1])));
    for (i = 1, 7, if (SBM[KT][i, j] % 2, vj = bitxor(vj, AMU[KT][i])));
    sol = matinverseimage(Mod(f2m(AKAP, NB)~, 2), Mod(vector(NB, l, bittest(vj, l - 1))~, 2));
    if (#sol == 0, error("relAtV: column ", j, " of twist ", KT - 1, " not in span(kappa)"));
    cb[j] = sum(l = 1, 7, lift(sol[l]) * 2^(l - 1));
    my(xk = 0); for (l = 1, 7, if (bittest(cb[j], l - 1), xk = bitxor(xk, AKAP[l])));
    if (xk != vj, error("relAtV: xor check")));
  chq(1, Str("twist ", KT - 1, ": relAtV coefficients cB = ", cb));
  \\ negative control: flipping one SB entry breaks the relation for that column
  my(vj = 0, sol); for (s1 = 1, 82, if (bittest(BTR[KT][1], s1 - 1), vj = bitxor(vj, CGB[s1])));
  for (i = 1, 7, if ((SBM[KT][i, 1] + (i == 1)) % 2, vj = bitxor(vj, AMU[KT][i])));
  sol = matinverseimage(Mod(f2m(AKAP, NB)~, 2), Mod(vector(NB, l, bittest(vj, l - 1))~, 2));
  chq(#sol == 0, Str("twist ", KT - 1, ": negative control, SB_11 flipped gives no kappa decomposition"));
  CBV[KT] = cb);
  STG++;
}
\\ ---------------------------------------------------------------- stage 5: Lean output
system(Str("mkdir -p ", OUTD));
wl(fn, str) = write(Str(OUTD, fn), str);
{
  my(fn = "VData.lean");
  system(Str("rm -f ", OUTD, fn));
  wl(fn, "import FurioLombardo.Discharge.SelmerBasis.PlaceUCert\n");
  wl(fn, "/-!\n# Data of the place v (generated by code/selmer-local-conditions/local_data_v.gp, output local_data_v.out)\n\nThe Eisenstein component `E` (`F1`), the model `M` (omega -> y + c Y), the square root data `S` of\n-iL (4 eN) / 3, the certificates of kappa at `F1` (`cK1`, `WCert`) and at `F2` (`cK2`, `UCert`), of the 29 gensL at\n`F1` (`cL`), of the 53 gensN at `F2` (`cN`), the kappa rows and the generator rows (22 bits, `F1` at bits 0 .. 7,\n`F2` at bits 8 .. 21).\n-/\n");
  wl(fn, "namespace FurioLombardo.Discharge.SelmerBasis.V\n\nopen FurioLombardo.M1\n");
  for (d = 0, DP, wl(fn, Str("def al_", d, " : List ℤ := ", lstr(EalP(EE, d)))));
  wl(fn, Str("\ndef alPow : List (List ℤ) := [", strjoin(vector(DP + 1, d, Str("al_", d - 1)), ", "), "]\n"));
  for (n = 0, NYP, my(v = EYp(EE, n)); wl(fn, Str("def Y_", n, " : List ℤ × List ℤ := (", lstr(v[1]), ", ", lstr(v[2]), ")")));
  wl(fn, Str("\ndef Ypow : List (List ℤ × List ℤ) := [", strjoin(vector(NYP + 1, n, Str("Y_", n - 1)), ", "), "]\n"));
  wl(fn, Str("def A : List ℤ := ", lstr(zkl(A)))); wl(fn, Str("def B : List ℤ := ", lstr(zkl(B))));
  wl(fn, Str("def cA : List ℤ := ", lstr(zkl(cA)))); wl(fn, Str("def bB : List ℤ := ", lstr(zkl(bB))));
  wl(fn, Str("\n/-- The Eisenstein component. -/\ndef E : EisData := ⟨", e, ", al_1, A, B, cA, bB, alPow, Ypow, ", EPREC, "⟩\n"));
  wl(fn, Str("/-- The model `ω ↦ y + c Y`. -/\ndef M : LModel := ⟨", lstr(zkl(yy)), ", ", lstr(zkl(cc)), ", ", LPREC, "⟩\n"));
  wl(fn, Str("/-- The square root data. -/\ndef S : SqrtV := ⟨", SV[1], ", ", SV[2], ", ", lstr(SV[3]), ", ", lstr(SV[4]), ", ", lstr(SV[5]), ", ", lstr(SV[6]), ", ", lstr(SV[7]), ", ", lstr(SV[8]), ", ", SV[9], "⟩\n"));
  for (i = 1, 2 * e + 1, wl(fn, Str("def cK1_", i - 1, " : WCert := ", certstr(KAPC1[i][1]))));
  wl(fn, Str("\ndef cK1 : List WCert := [", strjoin(vector(2 * e + 1, i, Str("cK1_", i - 1)), ", "), "]\n"));
  for (i = 1, 2 * e + 1, wl(fn, Str("def cK2_", i - 1, " : UCert := ", certstrU(KAPC2[i][1]))));
  wl(fn, Str("\ndef cK2 : List UCert := [", strjoin(vector(2 * e + 1, i, Str("cK2_", i - 1)), ", "), "]\n"));
  for (i = 1, 29, wl(fn, Str("def cL_", i - 1, " : WCert := ", certstr(GLC[i][1]))));
  wl(fn, Str("\ndef cL : List WCert := [", strjoin(vector(29, i, Str("cL_", i - 1)), ", "), "]\n"));
  for (i = 1, 53, wl(fn, Str("def cN_", i - 1, " : UCert := ", certstrU(GNC[i][1]))));
  wl(fn, Str("\ndef cN : List UCert := [", strjoin(vector(53, i, Str("cN_", i - 1)), ", "), "]\n"));
  wl(fn, Str("/-- The kappa rows. -/\ndef Akap : List ℕ := ", lstr(AKAP), "\n"));
  wl(fn, Str("/-- The generator rows. -/\ndef Cg : List ℕ := ", lstr(CGB), "\n"));
  wl(fn, "end FurioLombardo.Discharge.SelmerBasis.V");
  STG++;
}
{
for (KT = 0, 1,
  my(fn = Str("VDataK", KT, ".lean"));
  system(Str("rm -f ", OUTD, fn));
  wl(fn, "import FurioLombardo.Discharge.SelmerBasis.PointGen\nimport FurioLombardo.Discharge.SelmerBasis.PlaceUCert\n");
  wl(fn, Str("/-!\n# Points of twist ", KT, " at v (generated by code/selmer-local-conditions/local_data_v.gp, output local_data_v.out)\n\nThe 7 points `Dpt ", KT, " i` as `PtData` (only `P`, `R`, `d` and the value fields; `U = X² + (P/d) X + R/d` is lane\nSelmerSpan's exact `U`), their mu certificates at `F1` (`cM1`) and `F2` (`cM2`), the mu rows, the forms `QC`\n(`dotRow Cg QC = CvRows`), and the relAtV bitmasks `SBB` (parities of the columns of `SB`) and `cB`.\n-/\n"));
  wl(fn, Str("namespace FurioLombardo.Discharge.SelmerBasis.V.K", KT, "\n\nopen FurioLombardo.M1\n"));
  for (i = 1, 7, my(md = MUD[KT + 1][i]);
    wl(fn, Str("def pt_", i - 1, " : PtData := ⟨", lstr(md[1]), ", ", lstr(md[2]), ", ", md[3], ", [], [], 0, 0, [], [], [], 0, 0, [], [], [], 0, ",
      md[4], ", ", lstr(md[5]), ", ", md[6], ", ", lstr(md[7]), ", ", md[8], "⟩")));
  wl(fn, Str("\ndef pts : List PtData := [", strjoin(vector(7, i, Str("pt_", i - 1)), ", "), "]\n"));
  for (i = 1, 7, wl(fn, Str("def cM1_", i - 1, " : WCert := ", certstr(MUD[KT + 1][i][9][1][1]))));
  wl(fn, Str("\ndef cM1 : List WCert := [", strjoin(vector(7, i, Str("cM1_", i - 1)), ", "), "]\n"));
  for (i = 1, 7, wl(fn, Str("def cM2_", i - 1, " : UCert := ", certstrU(MUD[KT + 1][i][9][2][1]))));
  wl(fn, Str("\ndef cM2 : List UCert := [", strjoin(vector(7, i, Str("cM2_", i - 1)), ", "), "]\n"));
  wl(fn, Str("/-- The mu rows. -/\ndef Amu : List ℕ := ", lstr(AMU[KT + 1]), "\n"));
  wl(fn, Str("/-- The forms annihilating kappa and mu, with `dotRow Cg QC = CvRows`. -/\ndef QC : List ℕ := ", lstr(QCV[KT + 1]), "\n"));
  wl(fn, Str("/-- Parities of the columns of `SB`. -/\ndef SBB : List ℕ := ", lstr(SBB[KT + 1]), "\n"));
  wl(fn, Str("/-- The kappa coefficients of relAtV. -/\ndef cB : List ℕ := ", lstr(CBV[KT + 1]), "\n"));
  wl(fn, Str("end FurioLombardo.Discharge.SelmerBasis.V.K", KT)));
  STG++;
}
printf("  %d F1 certificates, %d F2 certificates; max n0 %d, max UCert n %d, max D %d, max precision %d\n", NCERT, NCERTU, MAXN0, MAXNU, MAXD, MAXPREC);
if (type(STG) != "t_INT" || STG != NSTG, printf("FAILED: %s of %d braced stages completed (a stage stopped on an error)\n", STG, NSTG); NFAIL++);
printf("DONE, %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00);
