\\ local_data_w6.gp: the data of the place w3 (e = 6) for the Lean files
\\ Discharge/SelmerBasis/W3*.lean, in the formats of PlaceWCert.lean (WCert, EisData) and PlaceWModel.lean
\\ (LModel, SqrtData), with every kernel check emulated exactly (w6_kernel_emulation_lib.gp) and its precision chosen.
\\ Model (as local_certs_w6.gp): F = K_w3[Y]/(Y^2 - B Y - A), omega = y + c Y (c = alpha^5), A = alpha (1 + alpha cA),
\\ B = alpha bB; standard basis of F^x/F^x2: Y, 1 + alpha^j Y (j = 0 .. 11), 5 (bits 0, j + 1, 13).
\\ Components of K_w3[T]/(fRev_k): 1 (root iL(alphaR)), 2 and 3 (roots iN(+)(betaR), iN(-)(betaR), w_N -> +- sF/2,
\\ sF^2 = iL(4 eN)), all three equal to F; the roots do not depend on the twist.
\\ Elements certified at a component (x within alpha^n0 of toF(X0, X1), certOK with truncation D = n0):
\\   kappa (13, dyGen alpha i), the 29 gensL at component 1, the 53 gensN at components 2 and 3, and per twist the
\\   14 points: M4's divisors (local_images_twist<k>_e6.bin), U = X^2 + p X + r with p, r replaced by w3-adic
\\   approximations P/d, R/d (d = 2^j, P, R small integral; the class of the point does not change, checked),
\\   two Hensel certificates (n0 for n' = d^6 n, a0 for a' = d^3 a, SelmerSpan/Mumford.lean sq_sub_eq), and the
\\   values Lambda^2 U(tau_c) at the three components.
\\ F_2 data per twist: rows (42 bits, component c at bits 14 c .. 14 c + 13) of kappa, mu, the 82 generators;
\\   Q = annihilator rows of span(kappa, mu); T = left inverse of the forms Q on the mu coordinates.
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-local-conditions/local_data_w6.gp < /dev/null > ../selmer-local-conditions/local_data_w6.out 2>&1
\\ Output: the Lean data files in /tmp/sb10/lean/ (installed by hand into Discharge/SelmerBasis/, then compiled).
default(parisizemax, 3000 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp");
read("../selmer-local-conditions/selmer_rows_lib.gp"); read("../selmer-global-bound/tower_lib.gp"); read("../selmer-local-conditions/w6_kernel_emulation_lib.gp");
LEAN = "../../FurioLombardo/";
SUD = Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean");
OUTD = "/tmp/sb10/lean/";
SBu7 = -1;
T00 = getabstime();
zkc(z) = nfalgtobasis(nfK, z);
isint(z) = denominator(zkc(z)) == 1;
zkl(z) = { my(v = zkc(z)); if (denominator(v) != 1, error("zkl: not integral")); v~; }
lstr(v) = Str(v);
KL(l) = nfbasistoalg(nfK, KofList(l));
\\ evaluation of a KE expression in K21
keval(e) = { my(tt = e[1]); if (tt == 0, if (#e[2] == 0, Mod(0, K21), nfbasistoalg(nfK, e[2]~)), tt == 1, Mod(e[2], K21), tt == 2, keval(e[2]) + keval(e[3]), tt == 3, keval(e[2]) - keval(e[3]), keval(e[2]) * keval(e[3])); }
redW(c, N) = {
  if (c == 0, return(Mod(0, K21)));
  my(cv = nfalgtobasis(nfK, c), d = denominator(cv), mm, k = 0);
  while (d % 2 == 0, cv = nfeltmul(nfK, cv, mapget(W, "E")); d = denominator(cv); k++; if (k > 8, error("redW: not w-integral")));
  mm = 2^ceil(N / e); nfbasistoalg(nfK, centerlift(Mod(cv * d, mm) * Mod(d, mm)^(-1)));
}
sqclass(W, u) = {
  my(C0 = sb_comp(W, 1), al = mapget(W, "al"), e = mapget(W, "e"), NP = 2 * e + 8, z, rr, d, s = Mod(1, K21), tt = 0);
  z = redK(W, u, NP); rr = liftres(C0, ksqrt(C0, res(C0, z))); z = redK(W, z / rr^2, NP); s = s * rr;
  for (s1 = 1, 2 * e - 1, d = res(C0, redK(W, (z - 1) / al^s1, NP)); if (d == 0, next);
    if (s1 % 2, tt = s1; break); rr = 1 + al^(s1 / 2) * liftres(C0, ksqrt(C0, d)); z = redK(W, z / rr^2, NP); s = redK(W, s * rr, NP));
  if (!tt, my(d4 = res(C0, redK(W, (z - 1) / 4, NP))); tt = if (d4 == 0, 2 * e + 1, 2 * e));
  [tt, redK(W, s, NP)];
}
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
\\ L42 = [x0, x1] (x0 + x1 om, om^2 = eps), N84 = [X, X'] (X + X' w, w^2 = eN = (ea + eb om) / 2)
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
\\ ---------------------------------------------------------------- stage 1: the model at w3
W = sb_place(3); e = mapget(W, "e"); al = mapget(W, "al");
sc = sqclass(W, EPSa); chq(vw(W, EPSa) == 0 && sc[1] == 11, "w3: eps is a unit of odd depth 11");
yy = Mod(lift(sc[2]), K21); cc = al^5; A = (EPSa - yy^2) / cc^2; B = -2 * yy / cc;
cA = (A / al - 1) / al; bB = B / al;
chq(isint(yy) && isint(A) && isint(B) && isint(cA) && isint(bB) && vw(W, A) == 1, "w3: y, A, B, cA = (A/al - 1)/al, bB = B/al in O_K21");
C = sb_comp(W, 2, A, B, 1); one = mapget(C, "one");
mybas = concat([[Y1 * one], vector(12, j, one * (1 + al^(j - 1) * Y1)), [5 * one]]);
mapput(C, "bas", mybas);
chq(vector(14, i, coords(C, mybas[i])[1]) == vector(14, i, vector(14, l, l == i)), "w3: the coordinates of the basis are the unit vectors");
toFv(u, v) = one * (u + v * Y1);
iLv(z) = one * (z[1] + z[2] * (yy + cc * Y1));
chq(iLv([0, 1])^2 == EPSa * one, "w3: (y + c Y)^2 = eps in K21[Y]/(P1)");
NPF = 800;
z4 = toFv(2 * EA + 2 * EB * yy, 2 * EB * cc);
chq(iLv([2 * EA, 2 * EB]) == z4, "iL(4 eN) = toF(2 ea + 2 eb y, 2 eb c)");
ce = coords(C, z4); chq(ce[1] == 0 * ce[1] && ce[2] == 12, "iL(4 eN) is a square of valuation 24 in F");
sF = red(C, Y1^ce[2] * one * ce[3], NPF);
for (it = 1, 9, sF = red(C, (sF + z4 / sF) / 2, NPF));
chq(val(C, sF^2 - z4) >= 2 * 240 + 40, Str("sF^2 = iL(4 eN) to F-valuation ", val(C, sF^2 - z4)));
iNv(z, sg) = iLv(z[1]) + iLv(z[2]) * sg * sF / 2;
taus = [iLv(alR), iNv(beR, 1), iNv(beR, -1)];
chq(val(C, subst(SBq, x, taus[1])) == oo && val(C, subst(SBh, x, taus[2])) >= NPF / 2 && val(C, subst(SBh, x, taus[3])) >= NPF / 2, "q(tau1) = 0 exactly, h(tau2), h(tau3) = 0 to high precision");
\\ ---------------------------------------------------------------- stage 2: certificates
LM = Map(); mapput(LM, "y", zkl(yy)); mapput(LM, "c", zkl(cc));
X0L(t) = KADD(t[1], KMUL(t[2], KLIN(mapget(LM, "y"))));
X1L(t) = KMUL(t[2], KLIN(mapget(LM, "c")));
\\ the N-type approximation: iL(t1) + b iL(t2) s0, s0 = s00 + s01 Y
X0N(t, bb) = { my(P = X0L(t[2]), Q = X1L(t[2]), R = KADD(KMUL(P, KLIN(SD[3])), KMUL(KMUL(Q, KLIN(SD[4])), KLIN(zkl(A)))));
  if (bb, KADD(X0L(t[1]), R), KSUB(X0L(t[1]), R)); }
X1N(t, bb) = { my(P = X0L(t[2]), Q = X1L(t[2]), R = KADD(KADD(KMUL(P, KLIN(SD[4])), KMUL(Q, KLIN(SD[3]))), KMUL(KMUL(Q, KLIN(SD[4])), KLIN(zkl(B)))));
  if (bb, KADD(X1L(t[1]), R), KSUB(X1L(t[1]), R)); }
\\ one certificate for the exact element X = toF(keval X0e, keval X1e); returns [cert, bitvector, m]
NCERT = 0; MAXN0 = 0; MAXPREC = 0;
\\ STG counts the braced stages completed; an error inside one leaves it short (see the DONE line)
STG = 0; NSTG = 6;
mkcert(X0e, X1e, name) = {
  my(X = toFv(keval(X0e), keval(X1e)), ce, av, m, S, ep, mh, S2, cS, c0, s1, u0, n0, n1, D, aa, rows, Btr, f5, a0, R, cR, R0, R1, cert, pr);
  if (val(C, X) < 0, error("mkcert: not integral: ", name));
  ce = coords(C, X); if (!verC(C, X, ce), error("mkcert: verC failed for ", name));
  av = ce[1]; m = ce[2]; S = ce[3]; ep = m % 2; mh = (m - ep) / 2;
  S2 = red(C, (Y1^2 * one / al)^mh * S, 2 * m + 60);
  cS = co(C, S2); u0 = cS[1]; c0 = (u0 - 1) / al; s1 = cS[2];
  if (!isint(c0) || !isint(s1), error("mkcert: S'' not (1 + al c0) + s1 Y for ", name));
  n0 = 2 * mh + ep + 2 * e + 1; n1 = n0 - 1; D = n0;
  aa = sum(i = 1, #av, av[i] * 2^(i - 1));
  rows = eRows(EE, D, aa);
  f5 = if (bitt(aa, 2 * e + 1), 5, 1); a0 = if (bitt(aa, 0), 1, 0);
  Btr = f5 * (Y1 * one)^a0 * sum(k = 1, #rows, (if (#rows[k] == 0, 0, nfbasistoalg(nfK, rows[k]~))) * (Y1 * one)^(k - 1));
  R = X * Btr - al^(2 * mh) * (Y1 * one)^(2 * ep) * (u0 + s1 * Y1)^2;
  cR = co(C, R); R0 = cR[1] / al^n0; R1 = cR[2] / al^n1;
  if (!isint(R0) || !isint(R1), error("mkcert: remainder not integral for ", name, ": v = ", vw(W, cR[1]), ", ", vw(W, cR[2]), ", n0 = ", n0));
  cert = [aa, mh, ep, zkl(u0), zkl(c0), zkl(s1), n0, n1, zkl(R0), zkl(R1), 0];
  pr = vecmax(apply(keprec, certExprs(EE, D, X0e, X1e, cert))); cert[11] = pr;
  if (!certOK(EE, D, X0e, X1e, cert), error("mkcert: certOK fails for ", name));
  if (type(n0) != "t_INT" || type(pr) != "t_INT", error("mkcert: n0 or prec not an integer for ", name));
  NCERT++; MAXN0 = max(MAXN0, n0); MAXPREC = max(MAXPREC, pr);
  [cert, av, m];
}
certstr(c) = Str("⟨", c[1], ", ", c[2], ", ", c[3], ", ", lstr(c[4]), ", ", lstr(c[5]), ", ", lstr(c[6]), ", ", c[7], ", ", c[8], ", ", lstr(c[9]), ", ", lstr(c[10]), ", ", c[11], "⟩");
\\ EisData (alPow up to DP, Ypow up to 15)
DP = 260;
EE = Map(); mapput(EE, "e", e); mapput(EE, "al", zkl(al)); mapput(EE, "A", zkl(A)); mapput(EE, "B", zkl(B));
mapput(EE, "cA", zkl(cA)); mapput(EE, "bB", zkl(bB));
mapput(EE, "alPow", vector(DP + 1, d, zkl(al^(d - 1))));
mapput(EE, "Ypow", vector(16, n, my(v = co(C, (Y1 * one)^(n - 1))); [zkl(v[1]), zkl(v[2])]));
EPREC = vecmax(apply(keprec, eisExprs(EE))); mapput(EE, "prec", EPREC);
chq(vecmin(apply(x -> kecheck(x, EPREC), eisExprs(EE))), Str("EisData.ok at precision ", EPREC));
\\ LModel
{LMX = [KSUB(KADD(KMUL(KLIN(zkl(yy)), KLIN(zkl(yy))), KMUL(KMUL(KLIN(zkl(cc)), KLIN(zkl(cc))), KLIN(zkl(A)))), KLIN(zkl(EPSa))),
  KADD(KMUL(KINT(2), KLIN(zkl(yy))), KMUL(KLIN(zkl(cc)), KLIN(zkl(B))))];}
LPREC = vecmax(apply(keprec, LMX)); chq(vecmin(apply(x -> kecheck(x, LPREC), LMX)), Str("LModel.ok at precision ", LPREC));
chq(zkl(EPSa) == leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL"), "epsL read back");
\\ SqrtData at precision NS (alpha units): s0 = sF reduced
NS = 240;
s0 = red(C, sF, 2 * NS + 4); cs0 = co(C, s0);
SJ = vw(W, cs0[1]); chq(SJ == 6 && vw(W, cs0[2]) >= SJ, "s0 = al^6 (unit) + al^6 (int) Y");
sd0 = (cs0[1] / al^SJ - 1) / al; sd1 = cs0[2] / al^SJ;
cr = co(C, s0^2 - z4); sR0 = cr[1] / al^NS; sR1 = cr[2] / al^NS;
chq(isint(sd0) && isint(sd1) && isint(sR0) && isint(sR1), "SqrtData: d0, d1, R0, R1 integral");
SD = [SJ, NS, zkl(cs0[1]), zkl(cs0[2]), zkl(sd0), zkl(sd1), zkl(sR0), zkl(sR1), 0];
{SDX = [KSUB(KLIN(SD[3]), KMUL(KLIN(EalP(EE, SJ)), KADD(KINT(1), KMUL(KLIN(zkl(al)), KLIN(SD[5]))))),
  KSUB(KLIN(SD[4]), KMUL(KLIN(EalP(EE, SJ)), KLIN(SD[6]))),
  KSUB(KSUB(KADD(KMUL(KLIN(SD[3]), KLIN(SD[3])), KMUL(KMUL(KLIN(SD[4]), KLIN(SD[4])), KLIN(zkl(A)))),
    KMUL(KINT(2), KADD(KLIN(EAL), KMUL(KLIN(EBL), KLIN(zkl(yy)))))), KMUL(KLIN(EalP(EE, NS)), KLIN(SD[7]))),
  KSUB(KSUB(KADD(KMUL(KINT(2), KMUL(KLIN(SD[3]), KLIN(SD[4]))), KMUL(KMUL(KLIN(SD[4]), KLIN(SD[4])), KLIN(zkl(B)))),
    KMUL(KINT(2), KMUL(KLIN(EBL), KLIN(zkl(cc))))), KMUL(KLIN(EalP(EE, NS)), KLIN(SD[8])))];}
SD[9] = vecmax(apply(keprec, SDX));
chq(vecmin(apply(x -> kecheck(x, SD[9]), SDX)) && NS < DP + 1 && SJ + 1 < DP + 1 && 2 * e + 2 * SJ < NS, Str("SqrtData.ok at precision ", SD[9]));
SNB = NS - e - SJ;  \\ ||sF - s0|| <= ||al||^SNB
printf("  model: EisData prec %d, LModel prec %d, SqrtData prec %d, sF - s0 within al^%d\n", EPREC, LPREC, SD[9], SNB);
\\ kappa
KAPX = vector(13, i, if (i == 1, KLIN(zkl(al)), KADD(KINT(1), KLIN(EalP(EE, i - 1)))));
chq(vector(13, i, keval(KAPX[i])) == concat([al], vector(12, i, 1 + al^i)), "kappa expressions = dyGen alpha i");
t0 = getabstime();
KAPC = vector(13, i, mkcert(KAPX[i], KINT(0), Str("kappa ", i - 1)));
printf("  kappa: 13 certificates (%d ms), bits %s\n", getabstime() - t0, apply(c -> c[1][1], KAPC));
\\ gensL at component 1
ofL(l) = [KLIN(l[1]), KLIN(l[2])];
ofN(l) = [[KLIN(l[1]), KLIN(l[2])], [KLIN(l[3]), KLIN(l[4])]];
t0 = getabstime();
GLC = vector(29, s1, my(tt = ofL(gLs[s1])); mkcert(X0L(tt), X1L(tt), Str("gL ", s1 - 1)));
printf("  gensL: 29 certificates at component 1 (%d ms)\n", getabstime() - t0);
\\ check: X0L/X1L is iL of mkL
chq(vector(29, s1, toFv(keval(X0L(ofL(gLs[s1]))), keval(X1L(ofL(gLs[s1])))) == iLv([KL(gLs[s1][1]), KL(gLs[s1][2])])), "toF(X0L, X1L) = iL(gensL s)");
\\ gensN at components 2, 3 (b = true, false); x = iN(mkN), mkN l = (l0 + l1 om) + (2 l2 + 2 l3 om) w_N
t0 = getabstime();
GNC = vector(2, bi, vector(53, s1, my(tt = ofN(gNs[s1])); mkcert(X0N(tt, bi == 1), X1N(tt, bi == 1), Str("gN ", s1 - 1, " comp ", bi + 1))));
printf("  gensN: 106 certificates at components 2, 3 (%d ms)\n", getabstime() - t0);
{
  my(okN = 1);
  for (bi = 1, 2, for (s1 = 1, 53, my(tt = ofN(gNs[s1]), xN = iNv([[KL(gNs[s1][1]), KL(gNs[s1][2])], [2 * KL(gNs[s1][3]), 2 * KL(gNs[s1][4])]], if (bi == 1, 1, -1)));
    if (val(C, xN - toFv(keval(X0N(tt, bi == 1)), keval(X1N(tt, bi == 1)))) < 2 * GNC[bi][s1][1][7], okN = 0)));
  chq(okN, "toF(X0N, X1N) within al^n0 of iN(gensN s), both signs");
  chq(MAXN0 <= SNB, Str("every n0 so far (max ", MAXN0, ") is at most the sF precision ", SNB));
  STG++;
}
\\ ---------------------------------------------------------------- stage 3: points
\\ Mirrors of Tower's sumPL / sumPN with smulLC / checkLC, for the value Lambda^2 U(alphaR), Lambda^2 U(betaR)
zeroLCk = [KINT(0), KINT(0)];
addLCk(x, y) = [KADD(x[1], y[1]), KADD(x[2], y[2])];
smulLCk(c, x) = [KMUL(c, x[1]), KMUL(c, x[2])];
sumPLk(Dn, n, cs, P) = if (#cs == 0 || #P == 0, zeroLCk, addLCk(smulLCk(KMUL(cs[1], KINT(Dn^n)), P[1]), sumPLk(Dn, max(n - 1, 0), cs[2 .. #cs], P[2 .. #P])));
sumPNk(Dn, n, cs, P) = if (#cs == 0 || #P == 0, [zeroLCk, zeroLCk], my(r = sumPNk(Dn, max(n - 1, 0), cs[2 .. #cs], P[2 .. #P]), c = KMUL(cs[1], KINT(Dn^n))); [addLCk(smulLCk(c, P[1][1]), r[1]), addLCk(smulLCk(c, P[1][2]), r[2])]);
tabAk = apply(ofL, tabA); tabBk = apply(ofN, tabB);
\\ Z's: d^5 Z1, d^5 Z0 of the division of 4 fRev by X^2 + (P/d) X + R/d
ZsE(g, P, R, d) = { my(Dk = KINT(d), w3, w2, w1, w0, Z1, Z0);
  w3 = KSUB(KMUL(Dk, g[6]), KMUL(P, g[7]));
  w2 = KSUB(KSUB(KMUL(KINT(d^2), g[5]), KMUL(P, w3)), KMUL(KMUL(Dk, R), g[7]));
  w1 = KSUB(KSUB(KMUL(KINT(d^3), g[4]), KMUL(P, w2)), KMUL(KMUL(Dk, R), w3));
  w0 = KSUB(KSUB(KMUL(KINT(d^4), g[3]), KMUL(P, w1)), KMUL(KMUL(Dk, R), w2));
  Z1 = KSUB(KSUB(KMUL(KINT(d^5), g[2]), KMUL(P, w0)), KMUL(KMUL(Dk, R), w1));
  Z0 = KSUB(KMUL(KINT(d^5), g[1]), KMUL(R, w0));
  [Z1, Z0]; }
\\ a Hensel certificate: s0 ~ sqrt(z) in K_w3 with z integral, at precision M (alpha units)
hens(z, M) = {
  my(v = vw(W, z), z1, cz, s, j, dd, Rr);
  if (v % 2, error("hens: odd valuation"));
  z1 = redW(z / al^v, M + 40); cz = coords(sb_comp(W, 1), z1);
  if (cz[1] != 0 * cz[1] || cz[2] != 0, error("hens: not a square"));
  s = redW(cz[3], M + 40);
  for (it = 1, 12, s = redW((s + z1 / s) / 2, M + 40));
  s = redW(al^(v / 2) * s, M + 20); j = v / 2;
  dd = (s / al^j - 1) / al; Rr = (s^2 - z) / al^M;
  if (!isint(dd) || !isint(Rr), error("hens: certificate not integral"));
  [s, j, dd, Rr];
}
\\ one point: [P, R, d, Z1, Z0, n-cert, a-cert, prec, mu data]
mkpoint(KT, i, U, g, gE) = {
  my(p = Mod(polcoef(U, 1, x), K21), r = Mod(polcoef(U, 0, x), K21), jd, d, P, R, pp, rr, Zk, Z1, Z0, Np, Xa, NR, hn, ha, Mn, Ma, U2, ok = 0, rowsU, rowsU2, mus);
  jd = ceil(max(max(-vw(W, p), -vw(W, r)), 0) / 6); d = 2^jd;
  for (NR2 = 2, 12, NR = 20 * NR2;
    P = redW(d * p, NR); R = redW(d * r, NR); pp = P / d; rr = R / d; U2 = x^2 + pp * x + rr;
    Zk = ZsE(gE, KLIN(zkl(P)), KLIN(zkl(R)), d); Z1 = keval(Zk[1]); Z0 = keval(Zk[2]);
    Np = d * (d * Z0^2 - P * Z1 * Z0 + R * Z1^2);
    if (Np == 0 || vw(W, Np) % 2, next);
    if (coords(sb_comp(W, 1), redW(Np / al^vw(W, Np), 60))[1] != 0 * vector(8), next);
    Mn = vw(W, Np) + 2 * e + 8;
    hn = hens(Np, Mn);
    foreach ([1, -1], sg, my(nn = sg * hn[1], Xa0 = 2 * d * Z0 - P * Z1 + 2 * nn);
      if (Xa0 != 0 && vw(W, Xa0) % 2 == 0 && coords(sb_comp(W, 1), redW(Xa0 / al^vw(W, Xa0), 60))[1] == 0 * vector(8),
        SGN = sg; ok = 1; break));
    if (!ok, next);
    \\ the class must be the one of the original point
    rowsU = vector(3, c, subst(U, x, taus[c])); rowsU2 = vector(3, c, subst(U2, x, taus[c]));
    if (vector(3, c, mucoords(rowsU[c])) != vector(3, c, mucoords(rowsU2[c])), ok = 0; next);
    break);
  if (!ok, error("mkpoint: no reduction found for twist ", KT, " point ", i));
  \\ the sign of n: n0 -> SGN n0 (then d_n -> (SGN n0 / al^j - 1) / al)
  hn = sgnh(hn, SGN); Xa = 2 * d * Z0 - P * Z1 + 2 * hn[1];
  Ma = vw(W, Xa) + 2 * e + 8;
  \\ the a-certificate needs 2 e + v(Xa) < Mn - j_n (the n-certificate moves a'^2 by 2 (n' - n0), of valuation >= Mn - j_n)
  while (hn[2] + 2 * e + 2 * (vw(W, Xa) / 2) >= Mn, Mn += 8; hn = sgnh(hens(Np, Mn), SGN); Xa = 2 * d * Z0 - P * Z1 + 2 * hn[1]);
  ha = hens(Xa, Ma);
  if (Mn > DP || Ma > DP, error("mkpoint: a Hensel exponent exceeds DP for twist ", KT, " point ", i));
  [P, R, d, Z1, Z0, Zk, hn, Mn, ha, Ma, U2];
}
sgnh(h, sg) = { if (sg == 1, return(h)); my(dd = (-h[1] / al^h[2] - 1) / al); if (!isint(dd), error("sgnh")); [-h[1], h[2], dd, h[4]]; }
mucoords(z) = { my(v = val(C, z), k = if (v < 0, ceil(-v / 4), 0)); coords(C, red(C, z * al^(2 * k), NPF))[1]; }
t0 = getabstime();
\\ the Lean data used by PtData.ok: g_j = 4 fRev_k coefficient j is FE k (6 - j) of M3a (FnData), al = M2's al3
FND = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "FnData");
chq(vector(2, KT, vector(7, j, zkl(4 * polcoef(SBf[KT], j - 1, x)))) == vector(2, KT, vector(7, j, FND[KT][7 - j + 1])), "g_j = 4 fRev_k coefficient j is Lean's FE k (6 - j)");
chq(zkl(al) == leandef5(Str(LEAN, "M2/SpecialData.lean"), "al3"), "al = Lean's al3");
PTS = vector(2); MUC = vector(2);
{
for (KT = 0, 1,
  my(f = SBf[KT + 1], g = vector(7, j, 4 * polcoef(f, j - 1, x)), gE, RR = read(Str("local_images_twist", KT, "_e6.bin")), pts = List(), mus = List());
  gE = vector(7, j, KLIN(zkl(g[j])));
  for (i = 1, #RR[7], my(uu = lift(Mod(1, K21) * subst(RR[7][i][1], t, x)), U = lift(Mod(1, K21) * polrecip(uu) / polcoef(uu, 0, x)), pt);
    pt = mkpoint(KT, i, U, g, gE); listput(pts, pt));
  PTS[KT + 1] = Vec(pts);
  printf("  twist %d: 14 points, reduction exponents d = %s, v(N') = %s\n", KT, apply(q -> q[3], PTS[KT + 1]), apply(q -> vw(W, q[7][1]^2), PTS[KT + 1])));
  STG++;
}
printf("  points (%d ms)\n", getabstime() - t0);
\\ ---------------------------------------------------------------- stage 4: point checks and mu certificates
\\ PtData checks (PointGen.lean): Z's, the two Hensel certificates, the values tL = LamL^2 U(alphaR), tN = LamN^2 U(betaR)
ptExprs(pt, gE) = {
  my(P = KLIN(zkl(pt[1])), R = KLIN(zkl(pt[2])), d = pt[3], hn = pt[7], ha = pt[9], Z1 = KLIN(zkl(pt[4])), Z0 = KLIN(zkl(pt[5])), Np, Xa);
  Np = KMUL(KINT(d), KADD(KSUB(KMUL(KINT(d), KMUL(Z0, Z0)), KMUL(P, KMUL(Z1, Z0))), KMUL(R, KMUL(Z1, Z1))));
  Xa = KSUB(KMUL(KINT(2 * d), Z0), KMUL(P, Z1));
  [KSUB(Z1, pt[6][1]), KSUB(Z0, pt[6][2]),
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
PTX = vector(2); MUD = vector(2);
t0 = getabstime();
{
for (KT = 0, 1,
  my(f = SBf[KT + 1], g = vector(7, j, 4 * polcoef(f, j - 1, x)), gE = vector(7, j, KLIN(zkl(g[j]))), out = List());
  for (i = 1, 14,
    my(pt = PTS[KT + 1][i], pp = pt[1] / pt[3], rr = pt[2] / pt[3], d = pt[3], ex, pr, Lv, Nv, lamL, lamN, tL, tN, prT, cm, bitsc);
    ex = ptExprs(pt, gE);
    for (q = 1, #ex, if (keval(ex[q]) != 0, error("point check ", q, " is not an identity (twist ", KT, ", point ", i, ")")));
    pr = vecmax(apply(keprec, ex));
    if (!vecmin(apply(q -> kecheck(q, pr), ex)), error("point checks"));
    if (!(2 * e + 2 * pt[7][2] < pt[8] && 2 * e + 2 * pt[9][2] < min(pt[10], pt[8] - pt[7][2])), error("point exponents"));
    Lv = Ladd(Ladd(Lmul(alR, alR), Lsc(pp, alR)), [rr, 0]);
    Nv = Nadd(Nadd(Nmul(beR, beR), Nsc(pp, beR)), [[rr, 0], [0, 0]]);
    lamL = d * ADn; while (!isint(lamL^2 * Lv[1]) || !isint(lamL^2 * Lv[2]), lamL *= 2);
    lamN = 2 * d * BDn; while (!isint(lamN^2 * Nv[1][1]) || !isint(lamN^2 * Nv[1][2]) || !isint(lamN^2 * Nv[2][1] / 2) || !isint(lamN^2 * Nv[2][2] / 2), lamN *= 2);
    tL = [zkl(lamL^2 * Lv[1]), zkl(lamL^2 * Lv[2])];
    tN = [zkl(lamN^2 * Nv[1][1]), zkl(lamN^2 * Nv[1][2]), zkl(lamN^2 * Nv[2][1] / 2), zkl(lamN^2 * Nv[2][2] / 2)];
    ex = tExprs(pt, lamL, tL, lamN, tN);
    for (q = 1, #ex, if (keval(ex[q]) != 0, error("t check ", q, " is not an identity (twist ", KT, ", point ", i, ")")));
    prT = vecmax(apply(keprec, ex));
    if (!vecmin(apply(q -> kecheck(q, prT), ex)), error("t checks"));
    my(tLk = [KLIN(tL[1]), KLIN(tL[2])], tNk = [[KLIN(tN[1]), KLIN(tN[2])], [KLIN(tN[3]), KLIN(tN[4])]]);
    cm = [mkcert(X0L(tLk), X1L(tLk), Str("mu k", KT, " i", i, " comp 1")),
      mkcert(X0N(tNk, 1), X1N(tNk, 1), Str("mu k", KT, " i", i, " comp 2")),
      mkcert(X0N(tNk, 0), X1N(tNk, 0), Str("mu k", KT, " i", i, " comp 3"))];
    \\ the class of the certified values is the class of U(tau_c)
    if (vector(3, c, cm[c][2]) != vector(3, c, mucoords(subst(pt[11], x, taus[c]))), error("mu class mismatch"));
    if (toFv(keval(X0L(tLk)), keval(X1L(tLk))) != iLv([nfbasistoalg(nfK, tL[1]~), nfbasistoalg(nfK, tL[2]~)]) || lamL^2 * subst(pt[11], x, taus[1]) != iLv([nfbasistoalg(nfK, tL[1]~), nfbasistoalg(nfK, tL[2]~)]), error("tL value"));
    listput(out, [pr, lamL, tL, lamN, tN, prT, cm]));
  MUD[KT + 1] = Vec(out));
  STG++;
}
printf("  mu: 2 x 14 points checked, 84 certificates (%d ms); max n0 %d (sF precision %d), max prec %d\n", getabstime() - t0, MAXN0, SNB, MAXPREC);
chq(MAXN0 <= SNB, "every n0 is at most the sF precision");
chq(MAXN0 + 1 <= DP, "alPow covers every n0");
\\ ---------------------------------------------------------------- stage 5: F_2 data
rowOf(bits3) = sum(c = 1, 3, sum(i = 1, 14, bits3[c][i] * 2^(i - 1 + 14 * (c - 1))));
bitsOf(n, nb) = vector(nb, i, bittest(n, i - 1));
AKAP = vector(13, i, rowOf([KAPC[i][2], KAPC[i][2], KAPC[i][2]]));
CGB = vector(82, s1, if (s1 <= 29, rowOf([GLC[s1][2], vector(14), vector(14)]), rowOf([vector(14), GNC[1][s1 - 29][2], GNC[2][s1 - 29][2]])));
AMU = vector(2, KT, vector(14, i, rowOf(vector(3, c, MUD[KT][i][7][c][2]))));
f2m(rows, nb) = matrix(#rows, nb, r, j, bittest(rows[r], j - 1));
annRows(rows, nb) = { my(K = lift(matker(Mod(f2m(rows, nb), 2)))); vector(#K, j, sum(i = 1, nb, K[i, j] * 2^(i - 1))); }
dotB(q, v) = hammingweight(bitand(q, v)) % 2;
QI = annRows(AKAP, 42);
chq(#QI == 35, "Q (independence): 35 rows annihilating kappa (rank of kappa 7)");
QC = vector(2); TI = vector(2);
{
for (KT = 1, 2,
  my(Mq = matrix(#QI, 14, k, i, dotB(QI[k], AMU[KT][i])));
  chq(matrank(Mod(Mq, 2)) == 14, Str("twist ", KT - 1, ": the 14 mu are independent modulo kappa"));
  \\ left inverse T (14 x nQ) with T Mq = I: solve via a maximal independent set of rows
  my(sel = List(), cur = matrix(0, 14));
  for (k = 1, #QI, my(nw = matconcat([cur; Mq[k, ]])); if (matrank(Mod(nw, 2)) > matrank(Mod(cur, 2)), cur = nw; listput(sel, k)));
  my(Ms = matrix(14, 14, a1, b1, Mq[sel[a1], b1]), Inv = lift(Mod(Ms, 2)^(-1)), T = vector(14));
  \\ row vector c with c Ms = e_k: c = e_k Inv
  for (kk = 1, 14, T[kk] = sum(a1 = 1, 14, Inv[kk, a1] * 2^(sel[a1] - 1)));
  \\ check: xor of the dotRows of the selected Q rows is 2^(kk-1)
  my(okT = 1); for (kk = 1, 14, my(xr = 0); for (k = 1, #QI, if (bittest(T[kk], k - 1), xr = bitxor(xr, sum(i = 1, 14, dotB(QI[k], AMU[KT][i]) * 2^(i - 1))))); if (xr != 2^(kk - 1), okT = 0));
  chq(okT, Str("twist ", KT - 1, ": left inverse T of the forms Q on the mu coordinates"));
  TI[KT] = T;
  QC[KT] = annRows(concat(AKAP, AMU[KT]), 42);
  chq(#QC[KT] == 21, Str("twist ", KT - 1, ": 21 rows annihilating kappa and mu (dim V_w = 21)"));
  printf("  twist %d: C_w rows (Q_c times the generator coordinates), %d x 82 (nonzero: %d)\n", KT - 1, #QC[KT], #[1 | q <- QC[KT], sum(s1 = 1, 82, dotB(q, CGB[s1])) > 0]));
  STG++;
}
\\ ---------------------------------------------------------------- stage 6: Lean output
system(Str("mkdir -p ", OUTD));
wl(fn, str) = write(Str(OUTD, fn), str);
\\ W3Data.lean
{
  my(fn = "W3Data.lean");
  system(Str("rm -f ", OUTD, fn));
  wl(fn, "import FurioLombardo.Discharge.SelmerBasis.PlaceWModel\n");
  wl(fn, "/-!\n# Data of the place w3 (generated by code/selmer-local-conditions/local_data_w6.gp, output local_data_w6.out)\n\nThe Eisenstein component `E`, the model `M` (omega -> y + c Y), the square root data `S` of iL (4 eN), the\ncertificates of kappa (`cK`), of the 29 gensL at component 1 (`cL`), of the 53 gensN at components 2 and 3\n(`cN1`, `cN2`), the kappa rows and the generator rows (42 bits, component c at bits 14 c .. 14 c + 13).\n-/\n");
  wl(fn, "namespace FurioLombardo.Discharge.SelmerBasis.W3\n\nopen FurioLombardo.M1\n");
  for (d = 0, DP, wl(fn, Str("def al_", d, " : List ℤ := ", lstr(EalP(EE, d)))));
  wl(fn, Str("\ndef alPow : List (List ℤ) := [", strjoin(vector(DP + 1, d, Str("al_", d - 1)), ", "), "]\n"));
  for (n = 0, 15, my(v = EYp(EE, n)); wl(fn, Str("def Y_", n, " : List ℤ × List ℤ := (", lstr(v[1]), ", ", lstr(v[2]), ")")));
  wl(fn, Str("\ndef Ypow : List (List ℤ × List ℤ) := [", strjoin(vector(16, n, Str("Y_", n - 1)), ", "), "]\n"));
  wl(fn, Str("def A : List ℤ := ", lstr(zkl(A)))); wl(fn, Str("def B : List ℤ := ", lstr(zkl(B))));
  wl(fn, Str("def cA : List ℤ := ", lstr(zkl(cA)))); wl(fn, Str("def bB : List ℤ := ", lstr(zkl(bB))));
  wl(fn, Str("\n/-- The Eisenstein component. -/\ndef E : EisData := ⟨", e, ", al_1, A, B, cA, bB, alPow, Ypow, ", EPREC, "⟩\n"));
  wl(fn, Str("/-- The model `ω ↦ y + c Y`. -/\ndef M : LModel := ⟨", lstr(zkl(yy)), ", ", lstr(zkl(cc)), ", ", LPREC, "⟩\n"));
  wl(fn, Str("/-- The square root data. -/\ndef S : SqrtData := ⟨", SD[1], ", ", SD[2], ", ", lstr(SD[3]), ", ", lstr(SD[4]), ", ", lstr(SD[5]), ", ", lstr(SD[6]), ", ", lstr(SD[7]), ", ", lstr(SD[8]), ", ", SD[9], "⟩\n"));
  for (i = 1, 13, wl(fn, Str("def cK_", i - 1, " : WCert := ", certstr(KAPC[i][1]))));
  wl(fn, Str("\ndef cK : List WCert := [", strjoin(vector(13, i, Str("cK_", i - 1)), ", "), "]\n"));
  for (i = 1, 29, wl(fn, Str("def cL_", i - 1, " : WCert := ", certstr(GLC[i][1]))));
  wl(fn, Str("\ndef cL : List WCert := [", strjoin(vector(29, i, Str("cL_", i - 1)), ", "), "]\n"));
  for (bi = 1, 2, for (i = 1, 53, wl(fn, Str("def cN", bi, "_", i - 1, " : WCert := ", certstr(GNC[bi][i][1]))));
    wl(fn, Str("\ndef cN", bi, " : List WCert := [", strjoin(vector(53, i, Str("cN", bi, "_", i - 1)), ", "), "]\n")));
  wl(fn, Str("/-- The kappa rows. -/\ndef Akap : List ℕ := ", lstr(AKAP), "\n"));
  wl(fn, Str("/-- The generator rows. -/\ndef Cg : List ℕ := ", lstr(CGB), "\n"));
  wl(fn, Str("/-- The rows annihilating kappa. -/\ndef QI : List ℕ := ", lstr(QI), "\n"));
  wl(fn, "end FurioLombardo.Discharge.SelmerBasis.W3");
  STG++;
}
\\ W3DataK<k>.lean
{
for (KT = 0, 1,
  my(fn = Str("W3DataK", KT, ".lean"));
  system(Str("rm -f ", OUTD, fn));
  wl(fn, "import FurioLombardo.Discharge.SelmerBasis.PointGen\n");
  wl(fn, Str("/-!\n# Points of twist ", KT, " at w3 (generated by code/selmer-local-conditions/local_data_w6.gp, output local_data_w6.out)\n\nThe 14 points (`pt`, PointGen.lean's `PtData`), their mu certificates at the three components (`cM1`, `cM2`,\n`cM3`), the mu rows, the rows annihilating kappa and mu (`QC`) and the left inverse `T`.\n-/\n"));
  wl(fn, Str("namespace FurioLombardo.Discharge.SelmerBasis.W3.K", KT, "\n\nopen FurioLombardo.M1\n"));
  for (i = 1, 14, my(pt = PTS[KT + 1][i], md = MUD[KT + 1][i], hn = pt[7], ha = pt[9]);
    wl(fn, Str("def pt_", i - 1, " : PtData := ⟨", lstr(zkl(pt[1])), ", ", lstr(zkl(pt[2])), ", ", pt[3], ", ", lstr(zkl(pt[4])), ", ", lstr(zkl(pt[5])), ", ",
      hn[2], ", ", pt[8], ", ", lstr(zkl(hn[1])), ", ", lstr(zkl(hn[3])), ", ", lstr(zkl(hn[4])), ", ",
      ha[2], ", ", pt[10], ", ", lstr(zkl(ha[1])), ", ", lstr(zkl(ha[3])), ", ", lstr(zkl(ha[4])), ", ", md[1], ", ",
      md[2], ", ", lstr(md[3]), ", ", md[4], ", ", lstr(md[5]), ", ", md[6], "⟩")));
  wl(fn, Str("\ndef pts : List PtData := [", strjoin(vector(14, i, Str("pt_", i - 1)), ", "), "]\n"));
  for (c = 1, 3, for (i = 1, 14, wl(fn, Str("def cM", c, "_", i - 1, " : WCert := ", certstr(MUD[KT + 1][i][7][c][1]))));
    wl(fn, Str("\ndef cM", c, " : List WCert := [", strjoin(vector(14, i, Str("cM", c, "_", i - 1)), ", "), "]\n")));
  wl(fn, Str("/-- The mu rows. -/\ndef Amu : List ℕ := ", lstr(AMU[KT + 1]), "\n"));
  wl(fn, Str("/-- The rows annihilating kappa and mu. -/\ndef QC : List ℕ := ", lstr(QC[KT + 1]), "\n"));
  wl(fn, Str("/-- The left inverse of the forms `QI` on the mu coordinates. -/\ndef T : List ℕ := ", lstr(TI[KT + 1]), "\n"));
  wl(fn, Str("end FurioLombardo.Discharge.SelmerBasis.W3.K", KT)));
  STG++;
}
printf("  %d certificates in all; max n0 %d, max precision %d\n", NCERT, MAXN0, MAXPREC);
if (type(STG) != "t_INT" || STG != NSTG, printf("FAILED: %s of %d braced stages completed (a stage stopped on an error)\n", STG, NSTG); NFAIL++);
printf("DONE, %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00);
