\\ local_data_w12.gp: the data of the place w2 (e = 12, f = 1) for the Lean files
\\ Discharge/SelmerBasis/W2Data*.lean, in the one-level format of W2UnramDefs.lean (UCert1, RhoData, SqrtU) and
\\ PointGen.lean (PtData), with every kernel check emulated exactly (../selmer-local-conditions/w6_kernel_emulation_lib.gp) and its precision chosen.
\\ Model: the three components of K_w2[T]/(fRev_k) are the unramified quadratic extension F = K_w2(zeta),
\\ zeta^2 = zeta - 1: component 0 by iL2 (omega -> (2 zeta - 1) rho, 3 rho^2 = -eps, rho in K_w2) at the root of q,
\\ components 1 and 2 by iN2 b (omega_N -> +- sU / 2, sU^2 = iL2(4 eN)) at the roots of h.
\\ Standard basis of F^x / F^x2 (26 bits, facU of PlaceUCert.lean): al (bit 0), 1 + al^t w (t odd < 24, w = 1, zeta:
\\ bits t, t + 1), 1 + 4 zeta (bit 25); it is the basis of selmer_rows_lib.gp's unramified component, same order (checked).
\\ Certified elements (certOKU1: X * al^a0 * sum_{k < n} p_k al^k = al^(2 mh) (u + s zeta)^2 + al^n (R0 + R1 zeta)):
\\   kappa (25, dyGen al l, exact), the 29 gensL at component 0, the 53 gensN at components 1 and 2, and per twist the
\\   26 points of M4 (local_images_twist<k>_e12.bin), reduced w2-adically as in local_data_w6.gp, at the three components.
\\ F_2 data: rows of 78 bits (component c at bits 26 c .. 26 c + 25) of kappa, of the 82 generators and of mu;
\\   QI annihilates kappa, T is a left inverse of the forms QI on the mu coordinates, QC annihilates kappa and mu,
\\   with QC chosen so that its forms read on the generator rows are exactly Assembly.C2Rows k.
\\ Run from code/earlier-computations (SW2STOP=<stage> stops after that stage; the script must be the gp file argument, a read() from
\\ another file stops silently at the stack resize):
\\   gp -q ../selmer-local-conditions/local_data_w12.gp < /dev/null > ../selmer-local-conditions/local_data_w12.out 2>&1
\\ Output: the Lean data files in /tmp/sw2/lean/ (split by ../selmer-local-conditions/split_lean_data.sh, installed into Discharge/SelmerBasis/).
default(parisizemax, 3000 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp");
read("../selmer-local-conditions/selmer_rows_lib.gp"); read("../selmer-global-bound/tower_lib.gp"); read("../selmer-local-conditions/w6_kernel_emulation_lib.gp");
LEAN = "../../FurioLombardo/";
SUD = Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean");
OUTD = "/tmp/sw2/lean/";
SBu7 = -1;
T00 = getabstime();
STOPAT = if (getenv("SW2STOP"), eval(getenv("SW2STOP")), 99);
zkc(z) = nfalgtobasis(nfK, z);
isint(z) = denominator(zkc(z)) == 1;
zkl(z) = { my(v = zkc(z)); if (denominator(v) != 1, error("zkl: not integral")); v~; }
lstr(v) = Str(v);
KL(l) = nfbasistoalg(nfK, KofList(l));
keval(e) = { my(tt = e[1]); if (tt == 0, if (#e[2] == 0, Mod(0, K21), nfbasistoalg(nfK, e[2]~)), tt == 1, Mod(e[2], K21), tt == 2, keval(e[2]) + keval(e[3]), tt == 3, keval(e[2]) - keval(e[3]), keval(e[2]) * keval(e[3])); }
\\ fast keprec (../selmer-local-conditions/local_data_v.gp): the least k from the bound upward with checkK k e, through a trial at a large k
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
STG = 0;
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
\\ ---------------------------------------------------------------- stage 1: the model at w2
W = sb_place(2); e = mapget(W, "e"); al = mapget(W, "al");
chq(e == 12 && zkl(al) == leandef5(Str(LEAN, "M2/SpecialData.lean"), "al2"), "w2: e = 12, al = Lean's al2");
C = sb_comp(W, 2, -1, 1, 0); one = mapget(C, "one");
Z1 = Y1 * one;
chq(Z1^2 == Z1 - 1, "F = K21[zeta]/(zeta^2 - zeta + 1), zeta = Y1");
\\ the basis of facU, in bit order
facBas = concat([[al * one], concat(vector(12, i, [one + al^(2 * i - 1), one + al^(2 * i - 1) * Z1])), [one + 4 * Z1]]);
chq(facBas == mapget(C, "bas"), "selmer_rows_lib's standard basis of F^x/F^x2 is the facU basis, in the same order (26 elements)");
chq(vector(26, i, coords(C, facBas[i])[1]) == vector(26, i, vector(26, l, l == i)), "the coordinates of the basis are the unit vectors");
toFv(u, v) = one * (u + v * Z1);
\\ rho: 3 rho^2 = -eps in K_w2
C1 = sb_comp(W, 1);
NR = 380;
{
  my(z = -EPSa / 3, cz = coords(C1, redK(W, z, NR)), vz = vw(W, z));
  chq(vz % 2 == 0 && cz[1] == 0 * cz[1], Str("-eps/3 is a square in K_w2 (valuation ", vz, ")"));
  RJ = vz / 2;
  my(r = redK(W, al^RJ * lift(cz[3]), NR));
  for (it = 1, 12, r = redK(W, (r + z / r) / 2, NR));
  RHO = r;
  printf("  rho: v(rho) = %d, v(3 rho^2 + eps) = %d\n", vw(W, RHO), vw(W, 3 * RHO^2 + EPSa));
}
omU = (2 * Z1 - 1) * RHO;
iL2v(z) = one * (z[1] + z[2] * omU);
chq(val(C, iL2v([0, 1])^2 - EPSa * one) >= NR - 40, "iL2(omega)^2 = eps to high precision");
z4 = iL2v([2 * EA, 2 * EB]);
ce4 = coords(C, z4);
printf("  iL2(4 eN): valuation %d, class %s\n", val(C, z4), ce4[1]);
chq(ce4[1] == 0 * ce4[1], "iL2(4 eN) is a square in F");
{
  my(sF = red(C, Z1^0 * al^ce4[2] * ce4[3], NR));
  for (it = 1, 12, sF = red(C, (sF + z4 / sF) / 2, NR));
  SUF = sF;
  printf("  sU: valuation %d, v(sU^2 - iL2(4 eN)) = %d, unit part coordinates v = %s\n", val(C, SUF), val(C, SUF^2 - z4), apply(c -> vw(W, c), co(C, SUF / al^val(C, SUF))));
}
iN2v(zz, sg) = iL2v(zz[1]) + iL2v(zz[2]) * sg * SUF / 2;
taus = [iL2v(alR), iN2v(beR, 1), iN2v(beR, -1)];
printf("  roots: v(q(tau0)) = %s, v(h(tau1)) = %s, v(h(tau2)) = %s\n", val(C, subst(SBq, x, taus[1])), val(C, subst(SBh, x, taus[2])), val(C, subst(SBh, x, taus[3])));
printf("  valuations of the roots: %s\n", apply(tt -> val(C, tt), taus));
STG++;
if (STOPAT <= 1, printf("STOP after stage 1 (%d ms)\n", getabstime() - T00); quit);
\\ ---------------------------------------------------------------- mirrors of W2UnramDefs.lean and PlaceUCert.lean
\\ facU e a: factors [t, [w1, w2]] of the basis product; dpU: foldr stepU [(1, 0)]
zmulU(p, q) = [p[1] * q[1] - p[2] * q[2], p[1] * q[2] + p[2] * q[1] + p[2] * q[2]];
addZL(P, Q) = { my(n = max(#P, #Q), o = vector(n)); for (i = 1, n, o[i] = if (i > #P, Q[i], i > #Q, P[i], P[i] + Q[i])); o; }
stepU(f, P) = addZL(P, concat(vector(f[1], i, [0, 0]), apply(p -> zmulU(f[2], p), P)));
facU(ee, aa) = { my(o = List()); for (j = 0, 2 * ee - 1, if (bittest(aa, j + 1), listput(o, [2 * (j \ 2) + 1, if (j % 2 == 0, [1, 0], [0, 1])])));
  if (bittest(aa, 2 * ee + 1), listput(o, [0, [0, 4]])); Vec(o); }
dpU(F) = { my(P = [[1, 0]]); forstep (i = #F, 1, -1, P = stepU(F[i], P)); P; }
trU(aa, n) = my(P = dpU(facU(e, aa))); P[1 .. min(n, #P)];
bit0U(aa) = if (bittest(aa, 0), 1, 0);
\\ EisData E: alP d = alPow.getD d []
EalP(E, d) = my(P = mapget(E, "alPow")); if (d < #P, P[d + 1], []);
\\ polyE E f a0 n P (right-nested sums, ending with int 0)
polyEk(E, fi, a0, n, P) = { my(r = KINT(0)); forstep (k = #P, 1, -1, r = KADD(KMUL(KINT(P[k][fi]), KLIN(EalP(E, n + k - 1 + a0))), r)); r; }
lhs1k(X0, X1, P1, P2) = [KSUB(KMUL(X0, P1), KMUL(X1, P2)), KADD(KMUL(X0, P2), KMUL(X1, KADD(P1, P2)))];
\\ UCert1 as a vector [a, mh, ub, u, s, c0, n, R0, R1, prec]
rhs1k(E, c) = { [KADD(KMUL(KSUB(KMUL(KLIN(c[4]), KLIN(c[4])), KMUL(KLIN(c[5]), KLIN(c[5]))), KLIN(EalP(E, 2 * c[2]))), KMUL(KLIN(c[8]), KLIN(EalP(E, c[7])))),
  KADD(KMUL(KADD(KMUL(KINT(2), KMUL(KLIN(c[4]), KLIN(c[5]))), KMUL(KLIN(c[5]), KLIN(c[5]))), KLIN(EalP(E, 2 * c[2]))), KMUL(KLIN(c[9]), KLIN(EalP(E, c[7]))))]; }
certExprsU1(E, X0, X1, c) = {
  my(P = trU(c[1], c[7]), a0 = bit0U(c[1]), L = lhs1k(X0, X1, polyEk(E, 1, a0, 0, P), polyEk(E, 2, a0, 0, P)), R = rhs1k(E, c));
  [KSUB(KLIN(if (c[3], c[5], c[4])), KADD(KINT(1), KMUL(KLIN(mapget(E, "al")), KLIN(c[6])))), KSUB(L[1], R[1]), KSUB(L[2], R[2])];
}
certOKU1(E, X0, X1, c) = 2 * c[2] + 2 * mapget(E, "e") < c[7] && c[7] < #mapget(E, "alPow") && vecmin(apply(q -> kecheck(q, c[10]), certExprsU1(E, X0, X1, c)));
certstrU1(c) = Str("⟨", c[1], ", ", c[2], ", ", if (c[3], "true", "false"), ", ", lstr(c[4]), ", ", lstr(c[5]), ", ", lstr(c[6]), ", ", c[7], ", ", lstr(c[8]), ", ", lstr(c[9]), ", ", c[10], "⟩");
\\ RhoData [j, d, n, R, prec]: r0 = al^j (1 + al d)
r0k(E, SR) = KMUL(KLIN(EalP(E, SR[1])), KADD(KINT(1), KMUL(KLIN(mapget(E, "al")), KLIN(SR[2]))));
rhoExprs(E, SR) = [KSUB(KADD(KMUL(KINT(3), KMUL(r0k(E, SR), r0k(E, SR))), KLIN(zkl(EPSa))), KMUL(KLIN(EalP(E, SR[3])), KLIN(SR[4])))];
rhoOK(E, SR) = SR[3] < #mapget(E, "alPow") && SR[1] < #mapget(E, "alPow") && 2 * mapget(E, "e") + 2 * SR[1] < SR[3] && kecheck(rhoExprs(E, SR)[1], SR[5]);
\\ SqrtU [j, n, s00, s01, d0, d1, R0, R1, prec]
suExprs(E, SR, S) = { [KSUB(KLIN(S[3]), KMUL(KLIN(EalP(E, S[1])), KADD(KINT(1), KMUL(KLIN(mapget(E, "al")), KLIN(S[5]))))),
  KSUB(KLIN(S[4]), KMUL(KLIN(EalP(E, S[1])), KLIN(S[6]))),
  KSUB(KSUB(KSUB(KMUL(KLIN(S[3]), KLIN(S[3])), KMUL(KLIN(S[4]), KLIN(S[4]))), KMUL(KINT(2), KSUB(KLIN(EAL), KMUL(KLIN(EBL), r0k(E, SR))))), KMUL(KLIN(EalP(E, S[2])), KLIN(S[7]))),
  KSUB(KSUB(KADD(KMUL(KINT(2), KMUL(KLIN(S[3]), KLIN(S[4]))), KMUL(KLIN(S[4]), KLIN(S[4]))), KMUL(KINT(4), KMUL(KLIN(EBL), r0k(E, SR)))), KMUL(KLIN(EalP(E, S[2])), KLIN(S[8])))]; }
suOK(E, SR, S) = S[2] < #mapget(E, "alPow") && S[1] < #mapget(E, "alPow") && 2 * mapget(E, "e") + 2 * S[1] < S[2] && S[2] + SR[1] <= SR[3] && vecmin(apply(q -> kecheck(q, S[9]), suExprs(E, SR, S)));
\\ X0L2, X1L2, X0N2, X1N2
X0L2(E, SR, tt) = KSUB(tt[1], KMUL(tt[2], r0k(E, SR)));
X1L2(E, SR, tt) = KMUL(KINT(2), KMUL(tt[2], r0k(E, SR)));
X0N2(E, SR, S, tt, bb) = KADD(X0L2(E, SR, tt[1]), KMUL(KINT(if (bb, 1, -1)), KSUB(KMUL(X0L2(E, SR, tt[2]), KLIN(S[3])), KMUL(X1L2(E, SR, tt[2]), KLIN(S[4])))));
X1N2(E, SR, S, tt, bb) = KADD(X1L2(E, SR, tt[1]), KMUL(KINT(if (bb, 1, -1)), KADD(KMUL(X0L2(E, SR, tt[2]), KLIN(S[4])), KMUL(X1L2(E, SR, tt[2]), KADD(KLIN(S[3]), KLIN(S[4]))))));
kapX(E, i) = if (i == 0, KLIN(mapget(E, "al")), KADD(KINT(1), KLIN(EalP(E, i))));
ofL(l) = [KLIN(l[1]), KLIN(l[2])];
ofN(l) = [[KLIN(l[1]), KLIN(l[2])], [KLIN(l[3]), KLIN(l[4])]];
\\ ---------------------------------------------------------------- stage 2: valuations of the global generators
\\ n of the certificate of x: 2 mh + 2 e + 1 with 2 mh = v(x) + (v(x) mod 2)
nOf(vv) = vv + (vv % 2) + 2 * e + 1;
vL = vector(29, s1, val(C, iL2v([KL(gLs[s1][1]), KL(gLs[s1][2])])));
vN = vector(2, bi, vector(53, s1, val(C, iN2v([[KL(gNs[s1][1]), KL(gNs[s1][2])], [2 * KL(gNs[s1][3]), 2 * KL(gNs[s1][4])]], if (bi == 1, 1, -1)))));
printf("  valuations: gensL at component 0 %s; gensN at components 1, 2: max %d, %d\n", vL, vecmax(vN[1]), vecmax(vN[2]));
STG++;
if (STOPAT <= 2, printf("STOP after stage 2 (%d ms)\n", getabstime() - T00); quit);
\\ ---------------------------------------------------------------- stage 3: points
zeroLCk = [KINT(0), KINT(0)];
addLCk(x1, y1) = [KADD(x1[1], y1[1]), KADD(x1[2], y1[2])];
smulLCk(c, x1) = [KMUL(c, x1[1]), KMUL(c, x1[2])];
sumPLk(Dn, n, cs, P) = if (#cs == 0 || #P == 0, zeroLCk, addLCk(smulLCk(KMUL(cs[1], KINT(Dn^n)), P[1]), sumPLk(Dn, max(n - 1, 0), cs[2 .. #cs], P[2 .. #P])));
sumPNk(Dn, n, cs, P) = if (#cs == 0 || #P == 0, [zeroLCk, zeroLCk], my(r = sumPNk(Dn, max(n - 1, 0), cs[2 .. #cs], P[2 .. #P]), c = KMUL(cs[1], KINT(Dn^n))); [addLCk(smulLCk(c, P[1][1]), r[1]), addLCk(smulLCk(c, P[1][2]), r[2])]);
tabAk = apply(ofL, tabA); tabBk = apply(ofN, tabB);
\\ Z's: d^5 Z1, d^5 Z0 of the division of 4 fRev by X^2 + (P/d) X + R/d (PointGen.lean zsE)
ZsE(g, P, R, d) = { my(Dk = KINT(d), w3, w2, w1, w0, Zz1, Zz0);
  w3 = KSUB(KMUL(Dk, g[6]), KMUL(P, g[7]));
  w2 = KSUB(KSUB(KMUL(KINT(d^2), g[5]), KMUL(P, w3)), KMUL(KMUL(Dk, R), g[7]));
  w1 = KSUB(KSUB(KMUL(KINT(d^3), g[4]), KMUL(P, w2)), KMUL(KMUL(Dk, R), w3));
  w0 = KSUB(KSUB(KMUL(KINT(d^4), g[3]), KMUL(P, w1)), KMUL(KMUL(Dk, R), w2));
  Zz1 = KSUB(KSUB(KMUL(KINT(d^5), g[2]), KMUL(P, w0)), KMUL(KMUL(Dk, R), w1));
  Zz0 = KSUB(KMUL(KINT(d^5), g[1]), KMUL(R, w0));
  [Zz1, Zz0]; }
sqK(z) = my(cz = coords(C1, z)); cz[1] == 0 * cz[1];
\\ a Hensel certificate: s ~ sqrt(z) in K_w2, z integral, at precision M (al units): [s, j, dd, Rr]
hens(z, M) = {
  my(v = vw(W, z), z1, cz, s1, j, dd, Rr);
  if (v % 2, error("hens: odd valuation"));
  z1 = redK(W, z / al^v, M + 40); cz = coords(C1, z1);
  if (cz[1] != 0 * cz[1], error("hens: not a square"));
  s1 = redK(W, lift(cz[3]), M + 40);
  for (it = 1, 12, s1 = redK(W, (s1 + z1 / s1) / 2, M + 40));
  s1 = redK(W, al^(v / 2) * s1, M + 20); j = v / 2;
  dd = (s1 / al^j - 1) / al; Rr = (s1^2 - z) / al^M;
  if (!isint(dd) || !isint(Rr), error("hens: certificate not integral"));
  [s1, j, dd, Rr];
}
sgnh(h, sg) = { if (sg == 1, return(h)); my(dd = (-h[1] / al^h[2] - 1) / al); if (!isint(dd), error("sgnh")); [-h[1], h[2], dd, h[4]]; }
NPF = 360;
mucoords(zz) = { my(v = val(C, zz), k = if (v < 0, ceil(-v / 2), 0)); coords(C, red(C, zz * al^(2 * k), NPF))[1]; }
\\ one point: [P, R, d, Z1, Z0, Zk, hn, Mn, ha, Ma, U2]
mkpoint(KT, i, U, g, gE) = {
  my(p = Mod(polcoef(U, 1, x), K21), r = Mod(polcoef(U, 0, x), K21), jd, d, P, R, pp, rr, Zk, Zv1, Zv0, Np, Xa, NR1, hn, ha, Mn, Ma, U2, ok = 0, rowsU, rowsU2, SGN);
  jd = ceil(max(max(-vw(W, p), -vw(W, r)), 0) / e); d = 2^jd;
  for (NR2 = 2, 14, NR1 = 20 * NR2;
    P = redK(W, d * p, NR1); R = redK(W, d * r, NR1); pp = P / d; rr = R / d; U2 = x^2 + pp * x + rr;
    Zk = ZsE(gE, KLIN(zkl(P)), KLIN(zkl(R)), d); Zv1 = keval(Zk[1]); Zv0 = keval(Zk[2]);
    Np = d * (d * Zv0^2 - P * Zv1 * Zv0 + R * Zv1^2);
    if (Np == 0 || vw(W, Np) % 2, next);
    if (!sqK(redK(W, Np / al^vw(W, Np), 60)), next);
    Mn = vw(W, Np) + 2 * e + 8;
    hn = hens(Np, Mn);
    foreach ([1, -1], sg, my(nn = sg * hn[1], Xa0 = 2 * d * Zv0 - P * Zv1 + 2 * nn);
      if (Xa0 != 0 && vw(W, Xa0) % 2 == 0 && sqK(redK(W, Xa0 / al^vw(W, Xa0), 60)), SGN = sg; ok = 1; break));
    if (!ok, next);
    rowsU = vector(3, c, subst(U, x, taus[c])); rowsU2 = vector(3, c, subst(U2, x, taus[c]));
    if (vector(3, c, mucoords(rowsU[c])) != vector(3, c, mucoords(rowsU2[c])), ok = 0; next);
    break);
  if (!ok, error("mkpoint: no reduction found for twist ", KT, " point ", i));
  hn = sgnh(hn, SGN); Xa = 2 * d * Zv0 - P * Zv1 + 2 * hn[1];
  Ma = vw(W, Xa) + 2 * e + 8;
  while (hn[2] + 2 * e + 2 * (vw(W, Xa) / 2) >= Mn, Mn += 8; hn = sgnh(hens(Np, Mn), SGN); Xa = 2 * d * Zv0 - P * Zv1 + 2 * hn[1]);
  ha = hens(Xa, Ma);
  [P, R, d, Zv1, Zv0, Zk, hn, Mn, ha, Ma, U2];
}
FND = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "FnData");
chq(vector(2, KT, vector(7, j, zkl(4 * polcoef(SBf[KT], j - 1, x)))) == vector(2, KT, vector(7, j, FND[KT][7 - j + 1])), "g_j = 4 fRev_k coefficient j is Lean's FE k (6 - j)");
PTS = vector(2);
t0 = getabstime();
{
for (KT = 0, 1,
  my(f = SBf[KT + 1], g = vector(7, j, 4 * polcoef(f, j - 1, x)), gE, RR = read(Str("local_images_twist", KT, "_e12.bin")), pts = List());
  gE = vector(7, j, KLIN(zkl(g[j])));
  if (#RR[7] != 26, error("twist ", KT, ": ", #RR[7], " divisors in the M4 file, 26 expected"));
  for (i = 1, #RR[7], my(uu = lift(Mod(1, K21) * subst(RR[7][i][1], t, x)), U = lift(Mod(1, K21) * polrecip(uu) / polcoef(uu, 0, x)), pt);
    pt = mkpoint(KT, i, U, g, gE); listput(pts, pt));
  PTS[KT + 1] = Vec(pts);
  printf("  twist %d: 26 points, reduction exponents d = %s, v(N') = %s, nM = %s, aM = %s\n", KT, apply(q -> q[3], PTS[KT + 1]), apply(q -> vw(W, q[7][1]^2), PTS[KT + 1]), apply(q -> q[8], PTS[KT + 1]), apply(q -> q[10], PTS[KT + 1])));
  STG++;
}
printf("  points (%d ms)\n", getabstime() - t0);
\\ the values tL = LamL^2 U(alphaR), tN = LamN^2 U(betaR) and their valuations at the three components
PTV = vector(2);
{
for (KT = 1, 2,
  my(out = List());
  for (i = 1, 26,
    my(pt = PTS[KT][i], pp = pt[1] / pt[3], rr = pt[2] / pt[3], d = pt[3], Lv, Nv, lamL, lamN, tL, tN, xs);
    Lv = Ladd(Ladd(Lmul(alR, alR), Lsc(pp, alR)), [rr, 0]);
    Nv = Nadd(Nadd(Nmul(beR, beR), Nsc(pp, beR)), [[rr, 0], [0, 0]]);
    lamL = d * ADn; while (!isint(lamL^2 * Lv[1]) || !isint(lamL^2 * Lv[2]), lamL *= 2);
    lamN = 2 * d * BDn; while (!isint(lamN^2 * Nv[1][1]) || !isint(lamN^2 * Nv[1][2]) || !isint(lamN^2 * Nv[2][1] / 2) || !isint(lamN^2 * Nv[2][2] / 2), lamN *= 2);
    tL = [zkl(lamL^2 * Lv[1]), zkl(lamL^2 * Lv[2])];
    tN = [zkl(lamN^2 * Nv[1][1]), zkl(lamN^2 * Nv[1][2]), zkl(lamN^2 * Nv[2][1] / 2), zkl(lamN^2 * Nv[2][2] / 2)];
    xs = [iL2v([KL(tL[1]), KL(tL[2])]), iN2v([[KL(tN[1]), KL(tN[2])], [2 * KL(tN[3]), 2 * KL(tN[4])]], 1), iN2v([[KL(tN[1]), KL(tN[2])], [2 * KL(tN[3]), 2 * KL(tN[4])]], -1)];
    if (vector(3, c, mucoords(xs[c])) != vector(3, c, mucoords(subst(pt[11], x, taus[c]))), error("mu class of Lambda^2 U differs from U, twist ", KT - 1, " point ", i));
    listput(out, [lamL, tL, lamN, tN, apply(q -> val(C, q), xs)]));
  PTV[KT] = Vec(out);
  printf("  twist %d: valuations of the mu values at the components: %s\n", KT - 1, apply(q -> q[5], PTV[KT])));
  STG++;
}
if (STOPAT <= 3, printf("STOP after stage 3 (%d ms)\n", getabstime() - T00); quit);
\\ ---------------------------------------------------------------- stage 4: model precisions, EisData, RhoData, SqrtU
\\ largest certificate exponents n on the L side (component 0) and on the N side (components 1, 2)
NLMAX = vecmax(concat(apply(nOf, vL), concat(vector(2, KT, apply(q -> nOf(q[5][1]), PTV[KT])))));
NNMAX = vecmax(concat(concat(apply(nOf, vN[1]), apply(nOf, vN[2])), concat(vector(2, KT, concat(apply(q -> nOf(q[5][2]), PTV[KT]), apply(q -> nOf(q[5][3]), PTV[KT]))))));
NKMAX = nOf(1);
SUJ = val(C, SUF); RJ0 = RJ;
SUN = NNMAX + e + SUJ;
SRN = max(NLMAX + e + RJ0, SUN + RJ0);
PMAX = vecmax(concat(vector(2, KT, concat(apply(q -> q[8], PTS[KT]), apply(q -> q[10], PTS[KT])))));
DP = max(max(SRN, SUN), max(PMAX, max(NLMAX, NNMAX)));
printf("  exponents: n up to %d (L side), %d (N side); RhoData n = %d, SqrtU n = %d, point Hensel exponents up to %d; alPow up to al^%d\n", NLMAX, NNMAX, SRN, SUN, PMAX, DP);
chq(SRN + 20 <= NR && SUN + 20 <= NR, "the model precision NR covers the RhoData and SqrtU exponents");
EE = Map(); mapput(EE, "e", e); mapput(EE, "al", zkl(al)); mapput(EE, "A", zkl(al)); mapput(EE, "B", []);
mapput(EE, "cA", []); mapput(EE, "bB", []);
mapput(EE, "alPow", vector(DP + 1, d, zkl(al^(d - 1))));
mapput(EE, "Ypow", [[[1], []]]);
EPREC = vecmax(apply(keprec, eisExprs(EE))); mapput(EE, "prec", EPREC);
chq(vecmin(apply(q -> kecheck(q, EPREC), eisExprs(EE))), Str("EisData.ok at precision ", EPREC, " (", DP + 1, " powers)"));
\\ RhoData: r0 = RHO reduced modulo al^(SRN + 2), j = 0
{
  my(r0 = redK(W, RHO, SRN + 2), dd, RR0);
  chq(vw(W, r0) == 0 && RJ0 == 0, "rho is a unit, j = 0");
  dd = (r0 - 1) / al; RR0 = (3 * r0^2 + EPSa) / al^SRN;
  chq(isint(dd) && isint(RR0), "RhoData: d = (r0 - 1)/al, R = (3 r0^2 + eps)/al^n integral");
  SR = [0, zkl(dd), SRN, zkl(RR0), 0];
  SR[5] = vecmax(apply(keprec, rhoExprs(EE, SR)));
  chq(rhoOK(EE, SR), Str("RhoData.ok at precision ", SR[5]));
  R0V = keval(r0k(EE, SR));
}
\\ SqrtU: s0 = sU reduced modulo al^(SUN + 2), computed from Z0 = iL2(4 eN) with rho replaced by r0
{
  my(Z0 = toFv(2 * EA - 2 * EB * R0V, 4 * EB * R0V), s0 = red(C, SUF, SUN + 2), cs0, dd0, dd1, cr, sR0, sR1);
  for (it = 1, 6, s0 = red(C, (s0 + Z0 / s0) / 2, SUN + 30));
  s0 = red(C, s0, SUN + 2); cs0 = co(C, s0);
  chq(vw(W, cs0[1]) == SUJ && vw(W, cs0[2]) >= SUJ, Str("s0 = al^", SUJ, " (unit + al int) + al^", SUJ, " (int) zeta"));
  dd0 = (cs0[1] / al^SUJ - 1) / al; dd1 = cs0[2] / al^SUJ;
  cr = co(C, s0^2 - Z0); sR0 = cr[1] / al^SUN; sR1 = cr[2] / al^SUN;
  chq(isint(dd0) && isint(dd1) && isint(sR0) && isint(sR1), "SqrtU: d0, d1, R0, R1 integral (the unit coordinate of s0 / al^j is 1 mod al)");
  SU = [SUJ, SUN, zkl(cs0[1]), zkl(cs0[2]), zkl(dd0), zkl(dd1), zkl(sR0), zkl(sR1), 0];
  SU[9] = vecmax(apply(keprec, suExprs(EE, SR, SU)));
  chq(suOK(EE, SR, SU), Str("SqrtU.ok at precision ", SU[9]));
  S0V = s0;
}
printf("  model: EisData prec %d, RhoData prec %d, SqrtU prec %d; L side within al^%d, N side within al^%d\n", EPREC, SR[5], SU[9], SRN - e - SR[1], SUN - e - SU[1]);
\\ one certificate for the exact element X = toU1(keval X0e, keval X1e), with n at most nmax; returns [cert, bits]
NCERT = 0; MAXN = 0; MAXPREC = 0;
mkcert1(X0e, X1e, name, nmax) = {
  my(X0v = keval(X0e), X1v = keval(X1e), Xf = toFv(X0v, X1v), ce, av, m, S, n, aa, P, a0, P1, P2, cS, u0, s1, ub, c0, L0, L1, R0, R1, cert, pr);
  if (val(C, Xf) < 0, error("mkcert1: not integral: ", name));
  ce = coords(C, Xf); if (!verC(C, Xf, ce), error("mkcert1: verC failed for ", name));
  av = ce[1]; m = ce[2]; S = ce[3]; n = 2 * m + 2 * e + 1;
  if (n > nmax, error("mkcert1: n = ", n, " exceeds the approximation bound ", nmax, " for ", name));
  aa = sum(i = 1, #av, av[i] * 2^(i - 1));
  P = trU(aa, n); a0 = bit0U(aa);
  P1 = sum(k = 1, #P, P[k][1] * al^(k - 1 + a0)); P2 = sum(k = 1, #P, P[k][2] * al^(k - 1 + a0));
  cS = co(C, S); u0 = cS[1]; s1 = cS[2];
  if (vw(W, u0) == 0, ub = 0; c0 = (u0 - 1) / al, ub = 1; c0 = (s1 - 1) / al);
  if (!isint(u0) || !isint(s1) || !isint(c0), error("mkcert1: unit coordinate for ", name));
  L0 = X0v * P1 - X1v * P2; L1 = X0v * P2 + X1v * (P1 + P2);
  R0 = (L0 - al^(2 * m) * (u0^2 - s1^2)) / al^n; R1 = (L1 - al^(2 * m) * (2 * u0 * s1 + s1^2)) / al^n;
  if (!isint(R0) || !isint(R1), error("mkcert1: remainder not integral for ", name, ": v = ", vw(W, L0 - al^(2 * m) * (u0^2 - s1^2)), ", ", vw(W, L1 - al^(2 * m) * (2 * u0 * s1 + s1^2)), ", n = ", n));
  cert = [aa, m, ub, zkl(u0), zkl(s1), zkl(c0), n, zkl(R0), zkl(R1), 0];
  pr = vecmax(apply(keprec, certExprsU1(EE, X0e, X1e, cert))); cert[10] = pr;
  if (!certOKU1(EE, X0e, X1e, cert), error("mkcert1: certOKU1 fails for ", name));
  NCERT++; MAXN = max(MAXN, n); MAXPREC = max(MAXPREC, pr);
  [cert, av];
}
NBL = SRN - e - SR[1]; NBN = SUN - e - SU[1];
STG++;
if (STOPAT <= 4, printf("STOP after stage 4 (%d ms)\n", getabstime() - T00); quit);
\\ ---------------------------------------------------------------- stage 5: certificates
\\ SW2PROBE=1: only the largest certificate of each kind (kernel timing probe, stages 6 and 7 skipped)
PROBE = if (getenv("SW2PROBE"), 1, 0);
\\ PtData checks (PointGen.lean): Z's, the two Hensel certificates; the values tL, tN
ptExprs(pt) = {
  my(P = KLIN(zkl(pt[1])), R = KLIN(zkl(pt[2])), d = pt[3], hn = pt[7], ha = pt[9], Zz1 = KLIN(zkl(pt[4])), Zz0 = KLIN(zkl(pt[5])), Np, Xa);
  Np = KMUL(KINT(d), KADD(KSUB(KMUL(KINT(d), KMUL(Zz0, Zz0)), KMUL(P, KMUL(Zz1, Zz0))), KMUL(R, KMUL(Zz1, Zz1))));
  Xa = KSUB(KMUL(KINT(2 * d), Zz0), KMUL(P, Zz1));
  [KSUB(Zz1, pt[6][1]), KSUB(Zz0, pt[6][2]),
   KSUB(KLIN(zkl(hn[1])), KMUL(KLIN(EalP(EE, hn[2])), KADD(KINT(1), KMUL(KLIN(zkl(al)), KLIN(zkl(hn[3])))))),
   KSUB(KSUB(KMUL(KLIN(zkl(hn[1])), KLIN(zkl(hn[1]))), Np), KMUL(KLIN(EalP(EE, pt[8])), KLIN(zkl(hn[4])))),
   KSUB(KLIN(zkl(ha[1])), KMUL(KLIN(EalP(EE, ha[2])), KADD(KINT(1), KMUL(KLIN(zkl(al)), KLIN(zkl(ha[3])))))),
   KSUB(KSUB(KMUL(KLIN(zkl(ha[1])), KLIN(zkl(ha[1]))), KADD(Xa, KMUL(KINT(2), KLIN(zkl(hn[1]))))), KMUL(KLIN(EalP(EE, pt[10])), KLIN(zkl(ha[4]))))];
}
tExprs(pt, lamL, tL, lamN, tN) = {
  my(P = KLIN(zkl(pt[1])), R = KLIN(zkl(pt[2])), d = pt[3], csL, csN, sL, sN, rL, rN);
  csL = [KMUL(KINT(lamL^2 / d), R), KMUL(KINT(lamL^2 / d), P), KINT(lamL^2)];
  csN = [KMUL(KINT(lamN^2 / d), R), KMUL(KINT(lamN^2 / d), P), KINT(lamN^2)];
  sL = sumPLk(ADn, 2, csL, tabAk); rL = smulLCk(KINT(ADn^2), [KLIN(tL[1]), KLIN(tL[2])]);
  sN = sumPNk(BPD, 2, csN, tabBk); rN = [smulLCk(KINT(BPD^2), [KLIN(tN[1]), KLIN(tN[2])]), smulLCk(KINT(BPD^2), [KLIN(tN[3]), KLIN(tN[4])])];
  [KSUB(sL[1], rL[1]), KSUB(sL[2], rL[2]), KSUB(sN[1][1], rN[1][1]), KSUB(sN[1][2], rN[1][2]), KSUB(sN[2][1], rN[2][1]), KSUB(sN[2][2], rN[2][2])];
}
okD(pt, lamL, lamN) = { my(nP = #mapget(EE, "alPow"), hn = pt[7], ha = pt[9]);
  pt[3] > 0 && hn[2] < nP && pt[8] < nP && ha[2] < nP && pt[10] < nP && 2 * e + 2 * hn[2] < pt[8] && 2 * e + 2 * ha[2] < pt[10] &&
  2 * e + 2 * ha[2] + hn[2] < pt[8] && lamL > 0 && lamN > 0 && lamL^2 % pt[3] == 0 && lamN^2 % pt[3] == 0; }
KSEL = if (PROBE, [1, 25], [1 .. 25]);
LSEL = if (PROBE, [vecsort(vector(29, s1, [vL[s1], s1]))[29][2]], [1 .. 29]);
NSEL = vector(2, bi, if (PROBE, [vecsort(vector(53, s1, [vN[bi][s1], s1]))[53][2]], [1 .. 53]));
PSEL = vector(2, KT, if (PROBE, if (KT == 1, [2, 10], []), [1 .. 26]));
t0 = getabstime();
KAPX = vector(25, i, kapX(EE, i - 1));
chq(vector(25, i, keval(KAPX[i])) == concat([al], vector(24, i, 1 + al^i)), "kappa expressions = dyGen al l");
KAPC = vector(25); foreach (KSEL, i, KAPC[i] = mkcert1(KAPX[i], KINT(0), Str("kappa ", i - 1), NKMAX + 400));
printf("  kappa: %d certificates (%d ms)\n", #KSEL, getabstime() - t0);
t0 = getabstime();
GLC = vector(29); foreach (LSEL, s1, my(tt = ofL(gLs[s1])); GLC[s1] = mkcert1(X0L2(EE, SR, tt), X1L2(EE, SR, tt), Str("gL ", s1 - 1), NBL));
chq(vecmin(vector(#LSEL, q, my(s1 = LSEL[q]); val(C, toFv(keval(X0L2(EE, SR, ofL(gLs[s1]))), keval(X1L2(EE, SR, ofL(gLs[s1])))) - iL2v([KL(gLs[s1][1]), KL(gLs[s1][2])])) >= NBL)), "toU1(X0L2, X1L2) is within al^NBL of iL2(gensL s)");
printf("  gensL: %d certificates at component 0 (%d ms)\n", #LSEL, getabstime() - t0);
t0 = getabstime();
GNC = vector(2, bi, vector(53));
for (bi = 1, 2, foreach (NSEL[bi], s1, my(tt = ofN(gNs[s1])); GNC[bi][s1] = mkcert1(X0N2(EE, SR, SU, tt, bi == 1), X1N2(EE, SR, SU, tt, bi == 1), Str("gN ", s1 - 1, " comp ", bi), NBN)));
{
  my(okN = 1);
  for (bi = 1, 2, foreach (NSEL[bi], s1, my(tt = ofN(gNs[s1]), xN = iN2v([[KL(gNs[s1][1]), KL(gNs[s1][2])], [2 * KL(gNs[s1][3]), 2 * KL(gNs[s1][4])]], if (bi == 1, 1, -1)));
    if (val(C, xN - toFv(keval(X0N2(EE, SR, SU, tt, bi == 1)), keval(X1N2(EE, SR, SU, tt, bi == 1)))) < NBN, okN = 0)));
  chq(okN, "toU1(X0N2, X1N2) is within al^NBN of iN2(gensN s), both signs");
}
printf("  gensN: %d certificates at components 1, 2 (%d ms)\n", #NSEL[1] + #NSEL[2], getabstime() - t0);
t0 = getabstime();
MUD = vector(2, KT, vector(26));
{
for (KT = 1, 2, foreach (PSEL[KT], i,
    my(pt = PTS[KT][i], pv = PTV[KT][i], lamL = pv[1], tL = pv[2], lamN = pv[3], tN = pv[4], ex, pr, prT, cm, tLk, tNk);
    ex = ptExprs(pt);
    for (q = 1, #ex, if (keval(ex[q]) != 0, error("point check ", q, " is not an identity (twist ", KT - 1, ", point ", i, ")")));
    pr = vecmax(apply(keprec, ex));
    if (!vecmin(apply(q -> kecheck(q, pr), ex)), error("point checks"));
    if (!okD(pt, lamL, lamN), error("okD fails for twist ", KT - 1, " point ", i));
    ex = tExprs(pt, lamL, tL, lamN, tN);
    for (q = 1, #ex, if (keval(ex[q]) != 0, error("t check ", q, " is not an identity (twist ", KT - 1, ", point ", i, ")")));
    prT = vecmax(apply(keprec, ex));
    if (!vecmin(apply(q -> kecheck(q, prT), ex)), error("t checks"));
    tLk = ofL(tL); tNk = ofN(tN);
    cm = [mkcert1(X0L2(EE, SR, tLk), X1L2(EE, SR, tLk), Str("mu k", KT - 1, " i", i, " comp 0"), NBL),
      mkcert1(X0N2(EE, SR, SU, tNk, 1), X1N2(EE, SR, SU, tNk, 1), Str("mu k", KT - 1, " i", i, " comp 1"), NBN),
      mkcert1(X0N2(EE, SR, SU, tNk, 0), X1N2(EE, SR, SU, tNk, 0), Str("mu k", KT - 1, " i", i, " comp 2"), NBN)];
    if (vector(3, c, cm[c][2]) != vector(3, c, mucoords(subst(pt[11], x, taus[c]))), error("mu class mismatch, twist ", KT - 1, " point ", i));
    MUD[KT][i] = [pr, lamL, tL, lamN, tN, prT, cm]));
  STG++;
}
printf("  points: %d checked, %d mu certificates (%d ms); max n %d (bounds %d, %d), max prec %d\n", #PSEL[1] + #PSEL[2], 3 * (#PSEL[1] + #PSEL[2]), getabstime() - t0, MAXN, NBL, NBN, MAXPREC);
chq(MAXN < DP + 1, "alPow covers every n");
\\ negative controls on the first selected certificate of each kind: a perturbed remainder, a flipped class bit
{
  my(c = KAPC[KSEL[1]][1], c2, X0e = KAPX[KSEL[1]]);
  c2 = c; c2[8] = zkl(KL(c[8]) + 1); chq(!certOKU1(EE, X0e, KINT(0), c2), "negative control: kappa certificate with R0 + 1 fails");
  c2 = c; c2[1] = bitxor(c[1], 2); chq(!certOKU1(EE, X0e, KINT(0), c2), "negative control: kappa certificate with bit 1 flipped fails");
  my(s1 = LSEL[1], tt = ofL(gLs[s1]), cl = GLC[s1][1]);
  c2 = cl; c2[1] = bitxor(cl[1], 2^25); chq(!certOKU1(EE, X0L2(EE, SR, tt), X1L2(EE, SR, tt), c2), "negative control: gensL certificate with bit 25 flipped fails");
  c2 = cl; c2[10] = cl[10] - 40; chq(!certOKU1(EE, X0L2(EE, SR, tt), X1L2(EE, SR, tt), c2), "negative control: gensL certificate at 40 bits less precision fails");
  my(SR2 = SR); SR2[4] = zkl(KL(SR[4]) + 1); chq(!rhoOK(EE, SR2), "negative control: RhoData with R + 1 fails");
  my(SU2 = SU); SU2[7] = zkl(KL(SU[7]) + 1); chq(!suOK(EE, SR, SU2), "negative control: SqrtU with R0 + 1 fails");
}
if (STOPAT <= 5, printf("STOP after stage 5 (%d ms)\n", getabstime() - T00); quit);
\\ ---------------------------------------------------------------- Lean writers
rhostr(S) = Str("⟨", S[1], ", ", lstr(S[2]), ", ", S[3], ", ", lstr(S[4]), ", ", S[5], "⟩");
sustr(S) = Str("⟨", S[1], ", ", S[2], ", ", lstr(S[3]), ", ", lstr(S[4]), ", ", lstr(S[5]), ", ", lstr(S[6]), ", ", lstr(S[7]), ", ", lstr(S[8]), ", ", S[9], "⟩");
ptstr(pt, md) = { my(hn = pt[7], ha = pt[9]);
  Str("⟨", lstr(zkl(pt[1])), ", ", lstr(zkl(pt[2])), ", ", pt[3], ", ", lstr(zkl(pt[4])), ", ", lstr(zkl(pt[5])), ", ",
      hn[2], ", ", pt[8], ", ", lstr(zkl(hn[1])), ", ", lstr(zkl(hn[3])), ", ", lstr(zkl(hn[4])), ", ",
      ha[2], ", ", pt[10], ", ", lstr(zkl(ha[1])), ", ", lstr(zkl(ha[3])), ", ", lstr(zkl(ha[4])), ", ", md[1], ", ",
      md[2], ", ", lstr(md[3]), ", ", md[4], ", ", lstr(md[5]), ", ", md[6], "⟩"); }
\\ the model part of W2Data.lean: al_d, alPow, E, SR, SU
wmodel(fn) = {
  for (d = 0, DP, write(fn, Str("def al_", d, " : List ℤ := ", lstr(EalP(EE, d)))));
  write(fn, Str("\ndef alPow : List (List ℤ) := [", strjoin(vector(DP + 1, d, Str("al_", d - 1)), ", "), "]\n"));
  write(fn, Str("/-- The data of `K_w2` (only `e`, `al` and the powers of `al` are used). -/\ndef E : EisData := ⟨12, FurioLombardo.M2.Special.al2, FurioLombardo.M2.Special.al2, [], [], [], alPow, [([1], [])], ", EPREC, "⟩\n"));
  write(fn, Str("/-- `ρ` with `3 ρ² = -ε`. -/\ndef SR : RhoData := ", rhostr(SR), "\n"));
  write(fn, Str("/-- The square root of `iL2 (4 eN)`. -/\ndef SU : SqrtU := ", sustr(SU), "\n"));
}
sw2probe() = {
  my(dir = "../selmer-local-conditions/probe", hdr, base);
  system(Str("mkdir -p ", dir));
  hdr = "import FurioLombardo.Discharge.SelmerBasis.W2UnramDefs\nimport FurioLombardo.Discharge.SelmerBasis.PlaceWElem\nimport FurioLombardo.Discharge.SelmerBasis.SUnitData\nimport FurioLombardo.M2.SpecialData\n\n/-! Kernel timing probe of the w2 data (generated by code/selmer-local-conditions/local_data_w12.gp with SW2PROBE=1). -/\n\nnamespace FurioLombardo.Discharge.SelmerBasis.W2Probe\n\nopen FurioLombardo.M1 FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.Tower FurioLombardo.Discharge.SelmerBasis.W2U\n";
  base = Str(dir, "sw2_probe_data.lean"); system(Str("rm -f ", base));
  write(base, hdr); wmodel(base);
  foreach (KSEL, i, write(base, Str("def cK_", i - 1, " : UCert1 := ", certstrU1(KAPC[i][1]))));
  foreach (LSEL, s1, write(base, Str("def cL_", s1 - 1, " : UCert1 := ", certstrU1(GLC[s1][1]))));
  for (bi = 1, 2, foreach (NSEL[bi], s1, write(base, Str("def cN", bi, "_", s1 - 1, " : UCert1 := ", certstrU1(GNC[bi][s1][1])))));
  foreach (PSEL[1], i, write(base, Str("def pt_", i - 1, " : PtData := ", ptstr(PTS[1][i], MUD[1][i])));
    for (c = 1, 3, write(base, Str("def cM", c, "_", i - 1, " : UCert1 := ", certstrU1(MUD[1][i][7][c][1])))));
  my(thms = List());
  listput(thms, ["E", "theorem ck_E : E.ok = true := by decide +kernel"]);
  listput(thms, ["SR", "theorem ck_SR : SR.ok E = true := by decide +kernel"]);
  listput(thms, ["SU", "theorem ck_SU : SU.ok E SR = true := by decide +kernel"]);
  foreach (KSEL, i, listput(thms, [Str("K", i - 1), Str("theorem ck_K_", i - 1, " : certOKU1 E (kapX E ", i - 1, ") (.int 0) cK_", i - 1, " = true := by decide +kernel")]));
  foreach (LSEL, s1, listput(thms, [Str("L", s1 - 1), Str("theorem ck_L_", s1 - 1, " : certOKU1 E (X0L2 E SR (ofL (SUnitData.gL.getD ", s1 - 1, " []))) (X1L2 E SR (ofL (SUnitData.gL.getD ", s1 - 1, " []))) cL_", s1 - 1, " = true := by decide +kernel")]));
  for (bi = 1, 2, foreach (NSEL[bi], s1, listput(thms, [Str("N", bi, "_", s1 - 1), Str("theorem ck_N", bi, "_", s1 - 1, " : certOKU1 E (X0N2 E SR SU (ofN (SUnitData.gN.getD ", s1 - 1, " [])) ", if (bi == 1, "true", "false"), ") (X1N2 E SR SU (ofN (SUnitData.gN.getD ", s1 - 1, " [])) ", if (bi == 1, "true", "false"), ") cN", bi, "_", s1 - 1, " = true := by decide +kernel")])));
  foreach (PSEL[1], i, my(q = i - 1);
    listput(thms, [Str("pt", q), Str("theorem ck_pt_", q, " : pt_", q, ".okD E = true ∧ pt_", q, ".okZ E (gW 0) = true ∧ pt_", q, ".okT = true := by\n  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel")]);
    listput(thms, [Str("M1_", q), Str("theorem ck_M1_", q, " : certOKU1 E (X0L2 E SR (ofL pt_", q, ".tL)) (X1L2 E SR (ofL pt_", q, ".tL)) cM1_", q, " = true := by decide +kernel")]);
    listput(thms, [Str("M2_", q), Str("theorem ck_M2_", q, " : certOKU1 E (X0N2 E SR SU (ofN pt_", q, ".tN) true) (X1N2 E SR SU (ofN pt_", q, ".tN) true) cM2_", q, " = true := by decide +kernel")]);
    listput(thms, [Str("M3_", q), Str("theorem ck_M3_", q, " : certOKU1 E (X0N2 E SR SU (ofN pt_", q, ".tN) false) (X1N2 E SR SU (ofN pt_", q, ".tN) false) cM3_", q, " = true := by decide +kernel")]));
  write(base, "\nend FurioLombardo.Discharge.SelmerBasis.W2Probe");
  \\ one file per theorem: the data file's text with the theorem before the end
  foreach (Vec(thms), th, my(fn = Str(dir, "sw2_probe_", th[1], ".lean"));
    system(Str("rm -f ", fn, "; head -n -1 ", base, " > ", fn)); write(fn, Str("\n", th[2], "\n\nend FurioLombardo.Discharge.SelmerBasis.W2Probe")));
  printf("  probe: %d theorem files in %s\n", #thms, dir);
  printf("DONE (probe), %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00);
}
if (PROBE, sw2probe(); quit);
\\ ---------------------------------------------------------------- stage 6: F_2 data
rowOf(bits3) = sum(c = 1, 3, sum(i = 1, 26, bits3[c][i] * 2^(i - 1 + 26 * (c - 1))));
f2m(rows, nb) = matrix(#rows, nb, r, j, bittest(rows[r], j - 1));
annRows(rows, nb) = { my(K = lift(matker(Mod(f2m(rows, nb), 2)))); vector(#K, j, sum(i = 1, nb, K[i, j] * 2^(i - 1))); }
dotB(q, v) = hammingweight(bitand(q, v)) % 2;
dotRowv(q, cols) = sum(s1 = 1, #cols, dotB(q, cols[s1]) * 2^(s1 - 1));
annOK(A, Q) = vecmin(concat([1], vector(#Q, i, vecmin(concat([1], vector(#A, l, !dotB(Q[i], A[l])))))));
Z26 = vector(26);
AKAP = vector(25, i, rowOf([KAPC[i][2], KAPC[i][2], KAPC[i][2]]));
CGB = vector(82, s1, if (s1 <= 29, rowOf([GLC[s1][2], Z26, Z26]), rowOf([Z26, GNC[1][s1 - 29][2], GNC[2][s1 - 29][2]])));
AMU = vector(2, KT, vector(26, i, rowOf(vector(3, c, MUD[KT][i][7][c][2]))));
chq(f2rank(f2m(AKAP, 78)) == 13, "kappa has rank 13 in F^x/F^x2 (three components; the kernel of K_w2^x/K_w2^x2 -> F^x/F^x2 is <-3>)");
QI = annRows(AKAP, 78);
chq(#QI == 65 && annOK(AKAP, QI), "QI: 65 rows annihilating kappa");
C2R = leandef5(Str(LEAN, "Discharge/SelmerBasis/AssemblyData.lean"), "C2Rows");
chq(#C2R == 2 && #C2R[1] == 39 && #C2R[2] == 39, "Assembly.C2Rows read: 39 rows per twist");
QC = vector(2); TI = vector(2);
{
for (KT = 1, 2,
  my(Mq = matrix(#QI, 26, k, i, dotB(QI[k], AMU[KT][i])), sel = List(), cur = matrix(0, 26), Ms, Inv, T, okT = 1, Q0, Cp, C2m, Mx, Q1);
  chq(matrank(Mod(Mq, 2)) == 26, Str("twist ", KT - 1, ": the 26 mu are independent modulo kappa"));
  for (k = 1, #QI, my(nw = matconcat([cur; Mq[k, ]])); if (matrank(Mod(nw, 2)) > matrank(Mod(cur, 2)), cur = nw; listput(sel, k)));
  Ms = matrix(26, 26, a1, b1, Mq[sel[a1], b1]); Inv = lift(Mod(Ms, 2)^(-1)); T = vector(26);
  for (kk = 1, 26, T[kk] = sum(a1 = 1, 26, Inv[kk, a1] * 2^(sel[a1] - 1)));
  \\ leftInvOK: xorSel over the rows R q = dotRow (mu) (QI q) 26 of the bits of T k is 2^k
  for (kk = 1, 26, my(xr = 0); for (k = 1, #QI, if (bittest(T[kk], k - 1), xr = bitxor(xr, dotRowv(QI[k], AMU[KT])))); if (xr != 2^(kk - 1), okT = 0));
  chq(okT, Str("twist ", KT - 1, ": leftInvOK, T is a left inverse of the forms QI on the mu coordinates"));
  TI[KT] = T;
  Q0 = annRows(concat(AKAP, AMU[KT]), 78);
  chq(#Q0 == 39, Str("twist ", KT - 1, ": 39 rows annihilating kappa and mu (the local image has dimension 26 modulo kappa)"));
  \\ change of basis M with M (Q0 read on the generators) = C2Rows
  Cp = matrix(39, 82, i, s1, dotB(Q0[i], CGB[s1])); C2m = matrix(39, 82, i, s1, bittest(C2R[KT][i], s1 - 1));
  chq(matrank(Mod(Cp, 2)) == 39 && f2eqspan(Cp, C2m), Str("twist ", KT - 1, ": the forms read on the 82 generator rows have rank 39 and the row space of Assembly.C2Rows"));
  Mx = lift(matinverseimage(Mod(Cp~, 2), Mod(C2m~, 2)))~;
  Q1 = vector(39, i, my(r = 0); for (j = 1, 39, if (Mx[i, j] % 2, r = bitxor(r, Q0[j]))); r);
  chq(vector(39, i, dotRowv(Q1[i], CGB)) == C2R[KT], Str("twist ", KT - 1, ": QC read on the generator rows (dotRow) is exactly Assembly.C2Rows"));
  chq(annOK(AKAP, Q1) && annOK(AMU[KT], Q1), Str("twist ", KT - 1, ": annOK of QC against kappa and mu"));
  QC[KT] = Q1);
  STG++;
}
\\ ---------------------------------------------------------------- stage 7: Lean output
system(Str("mkdir -p ", OUTD));
wl(fn, str) = write(Str(OUTD, fn), str);
{
  my(fn = "W2Data.lean");
  system(Str("rm -f ", OUTD, fn));
  wl(fn, "import FurioLombardo.Discharge.SelmerBasis.W2UnramDefs\nimport FurioLombardo.M2.SpecialData\n");
  wl(fn, "/-!\n# Data of the place w2 (generated by code/selmer-local-conditions/local_data_w12.gp, output local_data_w12.out)\n\nThe data `E` of `K_w2` (`e = 12`, `al = al2`, the powers `alPow`), `SR` (`ρ`, `3 ρ² = -ε`), `SU` (the square root of\n`iL2 (4 eN)`), the one-level square certificates of kappa (`cK`, `dyGen al l`, `l < 25`), of the 29 gensL at component 0\n(`cL`), of the 53 gensN at components 1 and 2 (`cN1`, `cN2`), the kappa rows `Akap`, the generator rows `Cg` (78 bits,\ncomponent `c` at bits `26 c .. 26 c + 25`) and the rows `QI` annihilating kappa.\n-/\n");
  wl(fn, "namespace FurioLombardo.Discharge.SelmerBasis.W2\n\nopen FurioLombardo.M1 FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.W2U\n");
  wmodel(Str(OUTD, fn));
  for (i = 1, 25, wl(fn, Str("def cK_", i - 1, " : UCert1 := ", certstrU1(KAPC[i][1]))));
  wl(fn, Str("\ndef cK : List UCert1 := [", strjoin(vector(25, i, Str("cK_", i - 1)), ", "), "]\n"));
  for (i = 1, 29, wl(fn, Str("def cL_", i - 1, " : UCert1 := ", certstrU1(GLC[i][1]))));
  wl(fn, Str("\ndef cL : List UCert1 := [", strjoin(vector(29, i, Str("cL_", i - 1)), ", "), "]\n"));
  for (bi = 1, 2, for (i = 1, 53, wl(fn, Str("def cN", bi, "_", i - 1, " : UCert1 := ", certstrU1(GNC[bi][i][1]))));
    wl(fn, Str("\ndef cN", bi, " : List UCert1 := [", strjoin(vector(53, i, Str("cN", bi, "_", i - 1)), ", "), "]\n")));
  wl(fn, Str("/-- The kappa rows. -/\ndef Akap : List ℕ := ", lstr(AKAP), "\n"));
  wl(fn, Str("/-- The generator rows. -/\ndef Cg : List ℕ := ", lstr(CGB), "\n"));
  wl(fn, Str("/-- The rows annihilating kappa. -/\ndef QI : List ℕ := ", lstr(QI), "\n"));
  wl(fn, "end FurioLombardo.Discharge.SelmerBasis.W2");
  STG++;
}
{
for (KT = 0, 1,
  my(fn = Str("W2DataK", KT, ".lean"));
  system(Str("rm -f ", OUTD, fn));
  wl(fn, "import FurioLombardo.Discharge.SelmerBasis.W2UnramDefs\n");
  wl(fn, Str("/-!\n# Points of twist ", KT, " at w2 (generated by code/selmer-local-conditions/local_data_w12.gp, output local_data_w12.out)\n\nThe 26 points (`pts`, PointGen.lean's `PtData`), their mu certificates at the three components (`cM1`, `cM2`, `cM3`),\nthe mu rows `Amu`, the rows `QC` annihilating kappa and mu (read on `Cg` they are `Assembly.C2Rows ", KT, "`) and the left\ninverse `T` of the forms `QI` on the mu coordinates.\n-/\n"));
  wl(fn, Str("namespace FurioLombardo.Discharge.SelmerBasis.W2.K", KT, "\n\nopen FurioLombardo.M1 FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.W2U\n"));
  for (i = 1, 26, wl(fn, Str("def pt_", i - 1, " : PtData := ", ptstr(PTS[KT + 1][i], MUD[KT + 1][i]))));
  wl(fn, Str("\ndef pts : List PtData := [", strjoin(vector(26, i, Str("pt_", i - 1)), ", "), "]\n"));
  for (c = 1, 3, for (i = 1, 26, wl(fn, Str("def cM", c, "_", i - 1, " : UCert1 := ", certstrU1(MUD[KT + 1][i][7][c][1]))));
    wl(fn, Str("\ndef cM", c, " : List UCert1 := [", strjoin(vector(26, i, Str("cM", c, "_", i - 1)), ", "), "]\n")));
  wl(fn, Str("/-- The mu rows. -/\ndef Amu : List ℕ := ", lstr(AMU[KT + 1]), "\n"));
  wl(fn, Str("/-- The rows annihilating kappa and mu. -/\ndef QC : List ℕ := ", lstr(QC[KT + 1]), "\n"));
  wl(fn, Str("/-- The left inverse of the forms `QI` on the mu coordinates. -/\ndef T : List ℕ := ", lstr(TI[KT + 1]), "\n"));
  wl(fn, Str("end FurioLombardo.Discharge.SelmerBasis.W2.K", KT)));
  STG++;
}
printf("  %d certificates in all; max n %d, max precision %d\n", NCERT, MAXN, MAXPREC);
NSTG = 9;
if (type(STG) != "t_INT" || STG != NSTG, printf("FAILED: %s of %d braced stages completed (a stage stopped on an error)\n", STG, NSTG); NFAIL++);
printf("DONE, %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00);
