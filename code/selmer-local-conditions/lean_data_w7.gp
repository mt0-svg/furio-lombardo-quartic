\\ lean_data_w7.gp: the data of the place w7 above 7 (e = 7, f = 3) for twist 1, in the
\\ frozen format of lean/FurioLombardo/Discharge/SelmerBasis/W7Spec.lean, with every kernel check of W7Spec emulated
\\ node for node (checkK through ../selmer-local-conditions/w6_kernel_emulation_lib.gp) and its precision chosen.
\\ Model (W7Spec docstring): r = sqrt(eps) near y0 (y0^2 - eps = al7^ny y0R), iota+ : omega -> -r (eN a square),
\\ iota- : omega -> r; S = sqrt(iota+(4 eN)) near S0 (S0^2 - (2 ea - 2 eb y0) = al7^ns S0R); A4 = iota-(4 eN),
\\ 2 ea + 2 eb y0 = al7 E4U; F' = K_w[Z]/(Z^2 - A4). Components: 0 iota+ alpha, 1 iota- alpha, 2 iota_N(+) beta,
\\ 3 iota_N(-) beta, 4 iota' beta in F' (Omega = 2 omega_N -> +-S, resp. Z).
\\ Written: tab (al7^(2^i), i < 9), tabK, M, 4 points pts (PtSq), 3 pairs (PairData, (0, i)), cL (29 x 2 KCert),
\\ cN (53 x (KCert, KCert, FCert)), cK (2 FCert), Akap, Amu, Cg, QI, nQI, TI, QC.
\\ Independent checks: the certificate bits against the square classes of the high precision local values (the method
\\ of local_data_w7.gp, pr^240), QC . Cg = C7Rows, a known-answer test of the checkK emulation on the kernel-checked
\\ certificate ck_w7k1sq1 of Count/At7.lean, and negative controls (perturbed remainder, flipped bit, low precision).
\\ Data read from the Lean sources only (same parser as local_data_w7.gp).
\\ Run from code/selmer-local-conditions:
\\   gp -q lean_data_w7.gp < /dev/null > lean_data_w7.out 2>&1
\\ Output: the Lean data files in /tmp/sp7_2/lean/ (installed by kernel_checks_w7.sh).
[x, b, w, z, y];
default(parisizemax, 3000 * 10^6);
default(nbthreads, 1);
NF = 0; NOK = 0; STG = 0; NSTG = 12;
T00 = getabstime();
chq(c, msg) = if (c, NOK++; printf("ok: %s\n", msg), NF++; printf("CHECK FAILED: %s\n", msg));
LEAN = "../../FurioLombardo/";
OUTD = "/tmp/sp7_2/lean/";
startswith(s, p) = my(A = Vecsmall(s), B = Vecsmall(p)); #A >= #B && A[1 .. #B] == B;
isblank(s) = my(A = Vecsmall(s)); #[c | c <- A, c != 32 && c != 9] == 0;
getraw(fn, nm) = {
  my(L = readstr(fn), pre = Str("def ", nm, " "), acc = "", on = 0);
  for (i = 1, #L, my(s = L[i]);
    if (!on,
      if (startswith(s, pre), on = 1; my(A = Vecsmall(s), p = 0);
        for (j = 1, #A - 1, if (A[j] == 58 && A[j + 1] == 61, p = j; break));
        if (p == 0, error("no := in ", s)); acc = Strchr(A[p + 2 .. #A])),
      if (isblank(s) || startswith(s, "/-") || startswith(s, "def ") || startswith(s, "theorem"), break);
      acc = Str(acc, s)));
  if (!on, error("no def ", nm, " in ", fn));
  Strchr([c | c <- Vecsmall(acc), c != 33]);
}
getdef(fn, nm) = eval(getraw(fn, nm));
read("../selmer-local-conditions/w6_kernel_emulation_lib.gp");
\\ keprec of w6_kernel_emulation_lib.gp, faster on large expressions (code/selmer-local-conditions/local_data_v.gp): after a few steps from the
\\ bound, the quotient digits at a safe precision give the needed precision directly (any passing k is valid)
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
\\ ---------------------------------------------------------------- stage 0: Lean data
fL = getdef(Str(LEAN, "M1/Basic.lean"), "fL");
Dz = getdef(Str(LEAN, "M1/DataField.lean"), "Dz");
zkNum = getdef(Str(LEAN, "M1/DataField.lean"), "zkNum");
epsL = getdef(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL");
eaL = getdef(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL");
ebL = getdef(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL");
al7L = getdef(Str(LEAN, "M2/SpecialData.lean"), "al7");
DB = Str(LEAN, "Discharge/M3a/DataBruin.lean");
FnData = getdef(DB, "FnData");
SU = Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean");
gLd = vector(29, i, getdef(SU, Str("gL_", i - 1)));
gNd = vector(53, j, getdef(SU, Str("gN_", j - 1)));
alphaL = getdef(SU, "alphaL"); alphaDen = getdef(SU, "alphaDen");
betaN = getdef(SU, "betaN"); betaDen = getdef(SU, "betaDen"); betaPowDen = getdef(SU, "betaPowDen");
alphaPow = vector(6, i, getdef(SU, Str("alphaPow_", i - 1)));
betaPow = vector(6, i, getdef(SU, Str("betaPow_", i - 1)));
C7Rows = getdef(Str(LEAN, "Discharge/SelmerBasis/AssemblyData.lean"), "C7Rows");
CD = Str(LEAN, "Discharge/SelmerBasis/Count/CertData.lean");
w7k1x = getdef(CD, "w7k1x"); w7k1sqT = getdef(CD, "w7k1sqT"); w7k1sqA = getdef(CD, "w7k1sqA"); w7k1sqB = getdef(CD, "w7k1sqB");
w7P64 = getdef(Str(LEAN, "Discharge/SelmerBasis/Count/At7.lean"), "w7P64");
{
chq(#fL == 22 && #zkNum == 21 && #epsL == 21 && #al7L == 21 && #FnData == 2 && #alphaL == 2 && #betaN == 4 && #C7Rows == 5
  && #alphaPow == 6 && #betaPow == 6 && alphaDen == 92 && betaDen == 184 && betaPowDen == 368,
  "Lean data parsed (fL, zkNum, Dz, epsL, eaL, ebL, al7, FnData, 29 gL, 53 gN, alphaL, betaN, alphaPow, betaPow, C7Rows)");
KZN = zkNum; KDZ = Dz; KFL = fL;
STG++;
}
fZ = Pol(Vecrev(fL), 'b);
nfK = nfinit(fZ);
chq(vector(21, j, Mod(nfbasistoalg(nfK, vectorv(21, i, i == j)), fZ)) == vector(21, j, Mod(Pol(Vecrev(zkNum[j]), 'b) / Dz, fZ)), "nfinit(fL).zk is Lean's basis zkNum / Dz");
zkE(a) = nfbasistoalg(nfK, Col(concat(a, vector(21 - #a))));
zkc(g) = nfalgtobasis(nfK, g)~;
isint(g) = denominator(nfalgtobasis(nfK, g)) == 1;
zkl(g) = { my(v = nfalgtobasis(nfK, g)); if (denominator(v) != 1, error("zkl: not integral")); v~; }
eps = zkE(epsL); ea = zkE(eaL); eb = zkE(ebL); al7 = zkE(al7L);
P7 = idealprimedec(nfK, 7);
chq(#P7 == 1 && P7[1].e == 7 && P7[1].f == 3, "7 has a single prime pr above it in K21, e = 7, f = 3");
pr = P7[1];
chq(nfeltval(nfK, al7, pr) == 1 && abs(norm(al7)) == 343, "al7 generates pr (v = 1, |N(al7)| = 343), so x / al7^k is integral iff v(x) >= k");
modP = nfmodprinit(nfK, pr);
vw(g) = if (g == 0, oo, nfeltval(nfK, g, pr));
res(g) = nfmodpr(nfK, g, modP);
resl(r) = nfbasistoalg(nfK, nfmodprlift(nfK, r, modP));
ubit(g) = my(r = res(g)); if (r == 0, error("ubit: not a unit")); !issquare(r);
clsK(g) = my(v = vw(g)); [v % 2, ubit(g / al7^v)];
\\ exact value in K21 of a KE expression
keval(e) = { my(t = e[1]); if (t == 0, if (#e[2] == 0, Mod(0, fZ), zkE(e[2])), t == 1, Mod(e[2], fZ), t == 2, keval(e[2]) + keval(e[3]), t == 3, keval(e[2]) - keval(e[3]), keval(e[2]) * keval(e[3])); }
\\ ---------------------------------------------------------------- arithmetic mod pr^m (as local_data_w7.gp, m a parameter)
NPREC = 240;
M7 = NPREC \ 7 + 2;
intz(g) = my(v = nfalgtobasis(nfK, g), d = denominator(v)); if (d % 7 == 0, error("intz: denominator divisible by 7")); nfbasistoalg(nfK, (d * v) * lift(Mod(1, 7^M7) / d));
redm(g, m) = nfbasistoalg(nfK, nfeltreduce(nfK, nfalgtobasis(nfK, intz(g)), idealpow(nfK, pr, m)));
invm(u, m) = {
  my(z = resl(1 / res(u)), k = 1);
  while (k < m, z = redm(z * (2 - u * z), m); k *= 2);
  if (vw(redm(u * z - 1, m)) < m, error("invm: no inverse")); z;
}
sqrtm(u, m) = {
  my(r = resl(sqrt(res(u))), k = 1);
  while (k < m, r = redm(r - (r^2 - u) * invm(2 * r, m), m); k *= 2);
  if (vw(redm(r^2 - u, m)) < m, error("sqrtm: no square root")); r;
}
\\ [Ui, Uc] with U Ui = 1 + al7 Uc (Ui the lift of the residue inverse)
unitc(U) = { my(Ui, Uc); if (vw(U) != 0, error("unitc: not a unit")); Ui = resl(1 / res(U)); Uc = (U * Ui - 1) / al7;
  if (!isint(U) || !isint(Ui) || !isint(Uc), error("unitc: not integral")); [Ui, Uc]; }
\\ ---------------------------------------------------------------- mirrors of W7Spec.lean
KEpow(e, n) = if (n == 0, KINT(1), n == 1, e, KMUL(KEpow(e, n - 1), e));
\\ alPw tab d, tab a vector of zk vectors (Lean list), i the current head index
alPwR(tab, i, d) = if (i > #tab, KINT(1), d == 0, KINT(1), d % 2 == 1, if (d \ 2 == 0, KLIN(tab[i]), KMUL(KLIN(tab[i]), alPwR(tab, i + 1, d \ 2))), alPwR(tab, i + 1, d \ 2));
alPw(tab, d) = alPwR(tab, 1, d);
powOKe(tab, i) = KSUB(KMUL(KLIN(tab[i + 1]), KLIN(tab[i + 1])), KLIN(if (i + 2 <= #tab, tab[i + 2], [])));
unitOKe(U, Ui, Uc) = KSUB(KMUL(KLIN(U), KLIN(Ui)), KADD(KINT(1), KMUL(KLIN(al7L), KLIN(Uc))));
sgnE(bb) = KINT(if (bb, -1, 1));
XLp(y0, x) = KSUB(x[1], KMUL(x[2], KLIN(y0)));
XLm(y0, x) = KADD(x[1], KMUL(x[2], KLIN(y0)));
XNs(y0, S0, bb, x) = if (bb, KADD(XLp(y0, x[1]), KMUL(XLp(y0, x[2]), KLIN(S0))), KSUB(XLp(y0, x[1]), KMUL(XLp(y0, x[2]), KLIN(S0))));
ofL(a) = [KLIN(if (#a >= 1, a[1], [])), KLIN(if (#a >= 2, a[2], []))];
ofN(a) = [[KLIN(if (#a >= 1, a[1], [])), KLIN(if (#a >= 2, a[2], []))], [KLIN(if (#a >= 3, a[3], [])), KLIN(if (#a >= 4, a[4], []))]];
\\ Model as a Map with the fields of W7Spec.Model
MN(M) = min(mapget(M, "ny"), mapget(M, "ns"));
okYe(tab, M) = KSUB(KSUB(KMUL(KLIN(mapget(M, "y0")), KLIN(mapget(M, "y0"))), KLIN(epsL)), KMUL(alPw(tab, mapget(M, "ny")), KLIN(mapget(M, "y0R"))));
okSe(tab, M) = { KSUB(KSUB(KMUL(KLIN(mapget(M, "S0")), KLIN(mapget(M, "S0"))),
  KSUB(KMUL(KINT(2), KLIN(eaL)), KMUL(KMUL(KINT(2), KLIN(ebL)), KLIN(mapget(M, "y0"))))), KMUL(alPw(tab, mapget(M, "ns")), KLIN(mapget(M, "S0R")))); }
okEe(M) = KSUB(KADD(KMUL(KINT(2), KLIN(eaL)), KMUL(KMUL(KINT(2), KLIN(ebL)), KLIN(mapget(M, "y0")))), KMUL(KLIN(al7L), KLIN(mapget(M, "E4U"))));
\\ the six expressions of Model.ok, in the order k1 .. k6
modelExprs(tab, M) = { [okYe(tab, M), unitOKe(mapget(M, "y0"), mapget(M, "y0i"), mapget(M, "y0c")), okSe(tab, M),
  unitOKe(mapget(M, "S0"), mapget(M, "S0i"), mapget(M, "S0c")), okEe(M), unitOKe(mapget(M, "E4U"), mapget(M, "E4Ui"), mapget(M, "E4Uc"))]; }
modelOK(tab, M) = { my(ex = modelExprs(tab, M), ks = mapget(M, "ks"));
  mapget(M, "ny") < 2^#tab && mapget(M, "ns") < 2^#tab && vecmin(vector(6, i, kecheck(ex[i], ks[i]))); }
\\ KCert as a vector [a0, a1, h, U, Ui, Uc, n, R, k1, k2] (a0, a1 in {0, 1})
kcExprs(tab, X, c) = { [KSUB(KMUL(KMUL(X, if (c[1], KLIN(al7L), KINT(1))), sgnE(c[2])),
  KADD(KMUL(alPw(tab, 2 * c[3]), KMUL(KLIN(c[4]), KLIN(c[4]))), KMUL(alPw(tab, c[7]), KLIN(c[8])))), unitOKe(c[4], c[5], c[6])]; }
kcOK(tab, N, X, c) = { my(ex = kcExprs(tab, X, c)); 2 * c[3] < c[7] && 2 * c[3] < N && c[7] < 2^#tab && kecheck(ex[1], c[9]) && kecheck(ex[2], c[10]); }
kcBits(c) = c[1] + 2 * c[2];
\\ FCert as a vector [a0, a1, j, h, U, Ui, Uc, n, R, Ry, k1, k2, k3]
fcXp(E4U, X, Y, c) = if (c[1], KMUL(KMUL(KLIN(al7L), KLIN(E4U)), Y), X);
fcYp(X, Y, c) = if (c[1], X, Y);
fcExprs(tab, E4U, X, Y, c) = { [KSUB(KMUL(fcXp(E4U, X, Y, c), sgnE(c[2])),
    KADD(KMUL(KMUL(alPw(tab, c[3] + 2 * c[4]), KEpow(KLIN(E4U), c[3])), KMUL(KLIN(c[5]), KLIN(c[5]))), KMUL(alPw(tab, c[8]), KLIN(c[9])))),
  unitOKe(c[5], c[6], c[7]), KSUB(fcYp(X, Y, c), KMUL(alPw(tab, c[3] + 2 * c[4]), KLIN(c[10])))]; }
fcOK(tab, N, E4U, X, Y, c) = { my(ex = fcExprs(tab, E4U, X, Y, c)); c[3] + 2 * c[4] < c[8] && c[3] + 2 * c[4] < N && c[8] < 2^#tab &&
  kecheck(ex[1], c[11]) && kecheck(ex[2], c[12]) && kecheck(ex[3], c[13]); }
fcBits(c) = c[1] + 2 * c[2];
\\ Count.gE 1 (.lin x) 0: shiftP of M3a's frevL 1 (PolyK.lean addP, smulP, mulP; Count/KE.lean shiftP)
addPl(l, m) = if (#l == 0, m, #m == 0, l, concat([KADD(l[1], m[1])], addPl(l[2 .. #l], m[2 .. #m])));
smulPl(a, l) = apply(e -> KMUL(a, e), l);
mulPl(l, m) = if (#l == 0, [], addPl(smulPl(l[1], m), concat([KINT(0)], mulPl(l[2 .. #l], m))));
shiftPl(xE, l) = if (#l == 0, [], addPl([l[1]], mulPl([xE, KINT(1)], shiftPl(xE, l[2 .. #l]))));
frevL1 = vector(7, j, KLIN(FnData[2][8 - j]));
gE1(xE) = my(L = shiftPl(xE, frevL1)); if (#L >= 1, L[1], KINT(0));
\\ PtSq as a vector [x, T, A, B, Bi, Cb, m, k1, k2, k3]
ptExprs(tab, p) = { [KSUB(KSUB(gE1(KLIN(p[1])), KMUL(KLIN(p[2]), KLIN(p[2]))), KMUL(alPw(tab, p[7] + 1), KLIN(p[3]))),
  KSUB(KMUL(KLIN(p[2]), KLIN(p[2])), KMUL(alPw(tab, p[7]), KLIN(p[4]))), unitOKe(p[4], p[5], p[6])]; }
ptOK(tab, p) = { my(ex = ptExprs(tab, p)); p[7] + 1 < 2^#tab && kecheck(ex[1], p[8]) && kecheck(ex[2], p[9]) && kecheck(ex[3], p[10]); }
\\ the L42 and N84 coordinates (TowerEval.lean sumPL, sumPN; SUnitTower.lean addLC, smulLC, zeroLC, ...)
zeroLCe = [KINT(0), KINT(0)];
addLCe(x, y) = [KADD(x[1], y[1]), KADD(x[2], y[2])];
smulLCe(c, x) = [KMUL(c, x[1]), KMUL(c, x[2])];
addNCe(x, y) = [addLCe(x[1], y[1]), addLCe(x[2], y[2])];
smulNCe(c, x) = [smulLCe(c, x[1]), smulLCe(c, x[2])];
sumPLe(D, n, cs, P) = if (#cs == 0 || #P == 0, zeroLCe, addLCe(smulLCe(KMUL(cs[1], KINT(D^n)), P[1]), sumPLe(D, max(n - 1, 0), cs[2 .. #cs], P[2 .. #P])));
sumPNe(D, n, cs, P) = if (#cs == 0 || #P == 0, [zeroLCe, zeroLCe], addNCe(smulNCe(KMUL(cs[1], KINT(D^n)), P[1]), sumPNe(D, max(n - 1, 0), cs[2 .. #cs], P[2 .. #P])));
tabAe = vector(6, i, ofL(alphaPow[i]));
tabBe = vector(6, i, ofN(betaPow[i]));
\\ PtData.okT with d = 1, lamL = LAML, lamN = LAMN (csL = [LAML^2 R, LAML^2 P, LAML^2]): the six checkK expressions
okTExprs(P, R, tL, tN, LAML, LAMN) = {
  my(csL = [KMUL(KINT(LAML^2), KLIN(R)), KMUL(KINT(LAML^2), KLIN(P)), KINT(LAML^2)], csN = [KMUL(KINT(LAMN^2), KLIN(R)), KMUL(KINT(LAMN^2), KLIN(P)), KINT(LAMN^2)], sL, rL, sN, rN);
  sL = sumPLe(alphaDen, 2, csL, tabAe); rL = smulLCe(KINT(alphaDen^2), ofL(tL));
  sN = sumPNe(betaPowDen, 2, csN, tabBe); rN = smulNCe(KINT(betaPowDen^2), ofN(tN));
  [KSUB(sL[1], rL[1]), KSUB(sL[2], rL[2]), KSUB(sN[1][1], rN[1][1]), KSUB(sN[1][2], rN[1][2]), KSUB(sN[2][1], rN[2][1]), KSUB(sN[2][2], rN[2][2])];
}
\\ PairData as a Map: i1, i2, P, R, kP, kR, tL, tN, precT, lamL, lamN, c0 .. c3 (KCert), c4 (FCert), dv, dW, dWi, dWc, kd1, kd2
okUExprs(tab, pts, pd) = { my(x1 = pts[mapget(pd, "i1") + 1][1], x2 = pts[mapget(pd, "i2") + 1][1]);
  [KSUB(KSUB(KLIN(x1), KLIN(x2)), KMUL(alPw(tab, mapget(pd, "dv")), KLIN(mapget(pd, "dW")))), unitOKe(mapget(pd, "dW"), mapget(pd, "dWi"), mapget(pd, "dWc")),
   KSUB(KLIN(mapget(pd, "P")), KSUB(KINT(0), KADD(KLIN(x1), KLIN(x2)))), KSUB(KLIN(mapget(pd, "R")), KMUL(KLIN(x1), KLIN(x2)))]; }
okUOK(tab, pts, pd) = { my(ex = okUExprs(tab, pts, pd)); 0 < mapget(pd, "lamL") && 0 < mapget(pd, "lamN") && mapget(pd, "i1") < #pts && mapget(pd, "i2") < #pts && mapget(pd, "dv") < 2^#tab &&
  kecheck(ex[1], mapget(pd, "kd1")) && kecheck(ex[2], mapget(pd, "kd2")) && kecheck(ex[3], mapget(pd, "kP")) && kecheck(ex[4], mapget(pd, "kR")); }
okTOK(pd) = { my(ex = okTExprs(mapget(pd, "P"), mapget(pd, "R"), mapget(pd, "tL"), mapget(pd, "tN"), mapget(pd, "lamL"), mapget(pd, "lamN"))); vecmin(apply(e -> kecheck(e, mapget(pd, "precT")), ex)); }
\\ the approximations of the five component values of an element (LC for c = 0, 1; NC for c = 2, 3, 4)
apL(M, t) = [XLp(mapget(M, "y0"), t), XLm(mapget(M, "y0"), t)];
apN(M, t) = [XNs(mapget(M, "y0"), mapget(M, "S0"), 1, t), XNs(mapget(M, "y0"), mapget(M, "S0"), 0, t), XLm(mapget(M, "y0"), t[1]), XLm(mapget(M, "y0"), t[2])];
okCOK(tab, M, pd) = { my(tl = ofL(mapget(pd, "tL")), tn = ofN(mapget(pd, "tN")), N = MN(M), a = apL(M, tl), n = apN(M, tn));
  kcOK(tab, N, a[1], mapget(pd, "c0")) && kcOK(tab, N, a[2], mapget(pd, "c1")) && kcOK(tab, N, n[1], mapget(pd, "c2")) &&
  kcOK(tab, N, n[2], mapget(pd, "c3")) && fcOK(tab, N, mapget(M, "E4U"), n[3], n[4], mapget(pd, "c4")); }
pdBits(pd) = kcBits(mapget(pd, "c0")) + 4 * kcBits(mapget(pd, "c1")) + 16 * kcBits(mapget(pd, "c2")) + 64 * kcBits(mapget(pd, "c3")) + 256 * fcBits(mapget(pd, "c4"));
okLOK(tab, M, cc, s) = { my(a = apL(M, ofL(gLd[s + 1]))); kcOK(tab, MN(M), a[1], cc[1]) && kcOK(tab, MN(M), a[2], cc[2]); }
okNOK(tab, M, cc, s) = { my(n = apN(M, ofN(gNd[s + 1]))); kcOK(tab, MN(M), n[1], cc[1]) && kcOK(tab, MN(M), n[2], cc[2]) && fcOK(tab, MN(M), mapget(M, "E4U"), n[3], n[4], cc[3]); }
kapXE(i) = if (i == 0, KLIN(al7L), KINT(-1));
kapLow(i) = if (i == 0, 85, 170);
bitsL(cc) = kcBits(cc[1]) + 4 * kcBits(cc[2]);
bitsN(cc) = 16 * kcBits(cc[1]) + 64 * kcBits(cc[2]) + 256 * fcBits(cc[3]);
\\ Echelon.lean: dotB, dotRow, annOK, xorSel, leftInvOK
dotB(r, x, y) = hammingweight(bitand(bitand(x, y), 2^r - 1)) % 2;
dotRow(r, Ccol, q, n) = sum(s = 0, n - 1, if (dotB(r, q, Ccol(s)), 2^s, 0));
annOK(r, A, nA, Q, nQ) = { for (i = 0, nQ - 1, for (l = 0, nA - 1, if (dotB(r, Q(i), A(l)), return(0)))); 1; }
xorSel(R, m, c) = { my(o = 0); for (q = 0, m - 1, if (bittest(c, q), o = bitxor(o, R(q)))); o; }
leftInvOK(R, m, n, T) = { for (k = 0, n - 1, if (xorSel(R, m, T(k)) != 2^k, return(0))); 1; }
getD(v, i) = if (i < #v, v[i + 1], 0);
\\ 4 fRev_1(t) (constant coefficient FnData[1][6])
fr4(t) = sum(i = 0, 6, zkE(FnData[2][7 - i]) * t^i);
\\ ---------------------------------------------------------------- stage 1: known-answer test of the checkK emulation
\\ ck_w7k1sq1 of Count/At7.lean, accepted by the Lean kernel at checkK 1152: gE 1 (.lin w7k1x) 0 - T^2 = (P64 al7) A
{
  my(e1 = KSUB(KSUB(gE1(KLIN(w7k1x)), KMUL(KLIN(w7k1sqT), KLIN(w7k1sqT))), KMUL(KMUL(KLIN(w7P64), KLIN(al7L)), KLIN(w7k1sqA))),
     e2 = KSUB(KMUL(KLIN(w7k1sqT), KLIN(w7k1sqT)), KMUL(KLIN(w7P64), KLIN(w7k1sqB))), xv, k1, k2);
  xv = zkE(w7k1x);
  chq(keval(gE1(KLIN(w7k1x))) == fr4(xv), "KAT: the mirror of Count.gE 1 (.lin x) 0 evaluates to 4 fRev_1(x) (x = w7k1x)");
  chq(kecheck(e1, 1152) && kecheck(e2, 640), "KAT: ck_w7k1sq1 (checkK 1152) and ck_w7k1sq2 (checkK 640) of Count/At7.lean pass in the emulation");
  k1 = keprec(e1); k2 = keprec(e2);
  printf("KAT: least passing precisions %d (Lean 1152), %d (Lean 640)\n", k1, k2);
  chq(k1 <= 1152 && k2 <= 640 && !kecheck(e1, k1 - 1) && !kecheck(e2, k2 - 1), "KAT: keprec is minimal and below the Lean precisions");
  my(Ap = w7k1sqA); Ap[1] += 1;
  my(e3 = KSUB(KSUB(gE1(KLIN(w7k1x)), KMUL(KLIN(w7k1sqT), KLIN(w7k1sqT))), KMUL(KMUL(KLIN(w7P64), KLIN(al7L)), KLIN(Ap))));
  chq(!kecheck(e3, 1152) && !kecheck(e3, 4096), "negative control: ck_w7k1sq1 with A_0 + 1 fails at 1152 and 4096");
  STG++;
}
\\ ---------------------------------------------------------------- stage 2: local values at precision pr^240 (local_data_w7.gp)
\\ yh = r mod pr^240 with iota+ : omega -> -yh making eN a unit square; sh = sqrt(iota+(eN)) (S = 2 sh);
\\ A4h = iota-(4 eN) = 2 ea + 2 eb yh (valuation 1)
{
  yh = sqrtm(eps, NPREC);
  if (clsK((ea - eb * yh) / 2) != [0, 0], yh = -yh);
  chq(vw(redm(yh^2 - eps, NPREC)) >= NPREC, "yh^2 = eps mod pr^240");
  chq(clsK((ea - eb * yh) / 2) == [0, 0] && vw(ea + eb * yh) == 1, "omega -> -yh: eN a unit square; omega -> yh: v(4 eN) = 1 (F' ramified)");
  sh = sqrtm((ea - eb * yh) / 2, NPREC);
  A4h = 2 * ea + 2 * eb * yh;
  chq(vw(redm(sh^2 - (ea - eb * yh) / 2, NPREC)) >= NPREC, "sh^2 = iota+(eN) mod pr^240");
  STG++;
}
\\ true local values: L42 element [x0, x1] (plain) at iota+-, N84 element [[X0, X1], [X2, X3]] (X + X' Omega) at iota_N(+-), iota'
ipL(x) = x[1] - x[2] * yh;
imL(x) = x[1] + x[2] * yh;
inN(x, sg) = ipL(x[1]) + sg * ipL(x[2]) * 2 * sh;
\\ square class bits (a0, a1) at F' of x + y Z (Z^2 = A4h), from the true values
clsFh(xv, yv) = {
  my(vx = vw(xv), vy = vw(yv), xp, wv, jj);
  if (vx == oo && vy == oo, error("clsFh: zero"));
  if (vx <= vy, xp = xv, xp = A4h * yv);
  wv = vw(xp); jj = wv % 2;
  [if (vx <= vy, 0, 1), ubit(xp / al7^wv / (A4h / al7)^jj)];
}
\\ the 10 class bits of an element of L42 (components 0, 1) or N84 (components 2, 3, 4)
clsLh(x) = concat([clsK(ipL(x)), clsK(imL(x)), [0, 0], [0, 0], [0, 0]]);
clsNh(x) = concat([[0, 0], [0, 0], clsK(inN(x, 1)), clsK(inN(x, -1)), clsFh(imL(x[1]), imL(x[2]))]);
bits2row(v) = sum(i = 1, #v, v[i] * 2^(i - 1));
\\ the plain L42 / N84 values of the Lean coordinate lists
valL(a) = [zkE(a[1]), zkE(a[2])];
valN(a) = [[zkE(a[1]), zkE(a[2])], [zkE(a[3]), zkE(a[4])]];
\\ roots: alpha = (alphaL0 + alphaL1 omega) / 92; beta = X + X' Omega, X = (betaN0 + betaN1 omega) / 184, X' = (betaN2 + betaN3 omega) / 368
alR = [zkE(alphaL[1]) / alphaDen, zkE(alphaL[2]) / alphaDen];
beR = [[zkE(betaN[1]) / betaDen, zkE(betaN[2]) / betaDen], [zkE(betaN[3]) / (2 * betaDen), zkE(betaN[4]) / (2 * betaDen)]];
Lmul(x, y) = [x[1] * y[1] + eps * x[2] * y[2], x[1] * y[2] + x[2] * y[1]];
Ladd(x, y) = [x[1] + y[1], x[2] + y[2]];
Lsc(c, x) = [c * x[1], c * x[2]];
E4 = [2 * ea, 2 * eb];
Nmul(x, y) = [Ladd(Lmul(x[1], y[1]), Lmul(E4, Lmul(x[2], y[2]))), Ladd(Lmul(x[1], y[2]), Lmul(x[2], y[1]))];
Nadd(x, y) = [Ladd(x[1], y[1]), Ladd(x[2], y[2])];
Nsc(c, x) = [Lsc(c, x[1]), Lsc(c, x[2])];
{
  my(ap = vector(6, i, Lsc(alphaDen^(i - 1), vector(2, k, 1)) ), okA = 1, okB = 1, pa = [1, 0], pb = [[1, 0], [0, 0]]);
  for (i = 1, 6, if (valL(alphaPow[i]) != Lsc(alphaDen^(i - 1), pa), okA = 0); pa = Lmul(pa, alR));
  for (i = 1, 6, if (valN(betaPow[i]) != Nsc(betaPowDen^(i - 1), pb), okB = 0); pb = Nmul(pb, beR));
  chq(okA && okB, "alphaPow_i = (92 alpha)^i and betaPow_i = (368 beta)^i in the coordinates read (conventions of alR, beR)");
  my(qa = Lmul(alR, alR), hb);
  printf("alpha integral in zk coordinates: %d %d; beta: %d %d %d %d\n", isint(alR[1]), isint(alR[2]), isint(beR[1][1]), isint(beR[1][2]), isint(beR[2][1]), isint(beR[2][2]));
  printf("v(alpha) at iota+: %s, iota-: %s; v(beta coords at iota'): %s %s\n", vw(ipL(alR)), vw(imL(alR)), vw(imL(beR[1])), vw(imL(beR[2])));
  STG++;
}
\\ ---------------------------------------------------------------- stage 3: the four split points (the search of local_data_w7.gp)
\\ the five roots of fRev 1 at the components: tq1 = iota+ alpha, tq2 = iota- alpha, th1, th2 = iota_N(+-) beta, thA + thB Z = iota' beta
tq1 = ipL(alR); tq2 = imL(alR); th1 = inN(beR, 1); th2 = inN(beR, -1); thA = imL(beR[1]); thB = imL(beR[2]);
fRev1(t) = fr4(t) / 4;
\\ class bits of x - T at the five components (x in K21)
ptClsh(t) = concat([clsK(t - tq1), clsK(t - tq2), clsK(t - th1), clsK(t - th2), clsFh(t - thA, -thB)]);
isSplit(t) = my(ft = fRev1(t), v = vw(ft)); v < NPREC - 40 && v % 2 == 0 && !ubit(ft / al7^v);
rankF2(M) = matrank(Mod(M, 2));
kapClsh = [concat([[1, 0], [1, 0], [1, 0], [1, 0], clsFh(al7, 0)]), concat([[0, 1], [0, 1], [0, 1], [0, 1], clsFh(-1, 0)])];
{
  my(fz = fZ, ok = 1);
  \\ fRev 1 vanishes at the five roots (F' root: both coordinates of h(thA + thB Z))
  chq(vw(redm(fr4(tq1), NPREC)) >= NPREC - 10 && vw(redm(fr4(tq2), NPREC)) >= NPREC - 10 && vw(redm(fr4(th1), NPREC)) >= NPREC - 10
    && vw(redm(fr4(th2), NPREC)) >= NPREC - 10, "fRev 1 vanishes at tq1, tq2, th1, th2 mod pr^(240 - 10)");
  my(acc = [0, 0], cf = vector(7, i, zkE(FnData[2][8 - i])));
  forstep (j = 7, 1, -1, acc = [acc[1] * thA + A4h * acc[2] * thB, acc[1] * thB + acc[2] * thA]; acc[1] += cf[j]);
  chq(vw(redm(acc[1], NPREC)) >= NPREC - 10 && vw(redm(acc[2], NPREC)) >= NPREC - 10, "fRev 1 vanishes at thA + thB Z in F' (both coordinates) mod pr^(240 - 10)");
  PTS = List();
  my(roots = [tq1, tq2, th1, th2, thA], tried = 0);
  for (m = 1, 12, for (ri = 1, 5, for (t = -3, 3,
    my(base = nfbasistoalg(nfK, nfeltreduce(nfK, nfalgtobasis(nfK, intz(roots[ri])), idealpow(nfK, pr, m))), xx = base + t * al7^m);
    tried++;
    if (isSplit(xx),
      my(cand = concat(Vec(PTS), [xx]), M = Mat(concat([Col(kapClsh[1]), Col(kapClsh[2])], vector(#cand - 1, i, Col(ptClsh(cand[i + 1]) + ptClsh(cand[1]))))));
      if (#cand == 1 || rankF2(M) == #cand + 1, listput(PTS, xx);
        printf("  split point %d: x = root %d truncated at pr^%d plus %d al7^%d, v(4 fRev_1(x)) = %d\n", #PTS, ri, m, t, m, vw(fr4(xx)))));
    if (#PTS >= 4, break(3)))));
  printf("split point search: %d candidates tried, %d points kept\n", tried, #PTS);
  chq(#PTS == 4, "four split points whose sums D_1i = P_1 + P_i (i = 2, 3, 4) give three independent classes modulo kappa");
  PTS = Vec(PTS);
  chq(vecmin(apply(isint, PTS)), "the four abscissas are integral");
  STG++;
}
\\ ---------------------------------------------------------------- stage 4: precision needed, the model, the power table
\\ NEED = 1 + the largest exponent 2h (K components: v + a0) or j + 2h (F': the valuation of x') met by a certificate,
\\ from the true local values; the model precision is NY = NS = NEED + 4
vneedK(xv) = my(v = vw(xv)); v + v % 2;
vneedF(xv, yv) = my(vx = vw(xv), vy = vw(yv)); if (vx <= vy, vx, 1 + vy);
{
  my(vm = 0);
  for (s = 1, 29, my(x = valL(gLd[s])); vm = max(vm, max(vneedK(ipL(x)), vneedK(imL(x)))));
  for (s = 1, 53, my(x = valN(gNd[s])); vm = max(vm, max(max(vneedK(inN(x, 1)), vneedK(inN(x, -1))), vneedF(imL(x[1]), imL(x[2])))));
  for (i = 2, 4, foreach([tq1, tq2, th1, th2], tt, vm = max(vm, vneedK((PTS[1] - tt) * (PTS[i] - tt))));
    my(fx = [(PTS[1] - thA) * (PTS[i] - thA) + A4h * thB^2, -thB * (PTS[1] - thA) - thB * (PTS[i] - thA)]);
    vm = max(vm, vneedF(fx[1], fx[2])));
  vm = max(vm, 1);
  NEED = vm + 1;
  NY = NEED + 4; NS = NEED + 4;
  printf("largest certificate exponent %d: NEED = %d, model precision ny = ns = %d\n", vm, NEED, NY);
  STG++;
}
{
  tab = vector(9, i, zkl(al7^(2^(i - 1))));
  tabK = vector(8, i, keprec(powOKe(tab, i - 1)));
  chq(#tab == 9 && tab[1] == al7L && vecmin(vector(8, i, kecheck(powOKe(tab, i - 1), tabK[i]))), Str("tab: 9 entries al7^(2^i), tab_0 = al7, powOK at the precisions tabK = ", tabK));
  chq(vecmin(vector(8, i, zkE(tab[i + 1]) == zkE(tab[i])^2)), "tab_{i+1} = tab_i^2 in K21");
  chq(vecmin(vector(511, d, keval(alPw(tab, d)) == al7^d)), "alPw tab d = al7^d for 1 <= d < 512 (exact evaluation)");
  printf("tab: largest coordinate digits %s\n", vector(9, i, #Str(vecmax(apply(abs, tab[i])))));
  \\ the model
  my(y0 = redm(yh, NY), S0, E4, t);
  S0 = sqrtm(2 * ea - 2 * eb * y0, NS);
  if (vw(S0 - 2 * sh) == 0, S0 = redm(-S0, NS));
  E4 = (2 * ea + 2 * eb * y0) / al7;
  M = Map();
  mapput(M, "y0", zkl(y0)); mapput(M, "ny", NY); mapput(M, "y0R", zkl((y0^2 - eps) / al7^NY));
  t = unitc(y0); mapput(M, "y0i", zkl(t[1])); mapput(M, "y0c", zkl(t[2]));
  mapput(M, "S0", zkl(S0)); mapput(M, "ns", NS); mapput(M, "S0R", zkl((S0^2 - (2 * ea - 2 * eb * y0)) / al7^NS));
  t = unitc(S0); mapput(M, "S0i", zkl(t[1])); mapput(M, "S0c", zkl(t[2]));
  mapput(M, "E4U", zkl(E4));
  t = unitc(E4); mapput(M, "E4Ui", zkl(t[1])); mapput(M, "E4Uc", zkl(t[2]));
  mapput(M, "ks", apply(keprec, modelExprs(tab, M)));
  chq(modelOK(tab, M), Str("Model.ok at the precisions k1 .. k6 = ", mapget(M, "ks")));
  chq(vw(y0 - yh) >= NY && vw(S0 - 2 * sh) >= NS, "the model approximates the local values: v(y0 - r) >= ny, v(S0 - S) >= ns (S = 2 sh)");
  chq(vw(E4) == 0 && vw(al7 * E4 - A4h) >= NY, "E4U is a unit and al7 E4U approximates A4 = iota-(4 eN) to pr^ny");
  printf("model: y0 digits %d, y0R digits %d, S0 digits %d, S0R digits %d, E4U digits %d\n", #Str(vecmax(apply(abs, mapget(M, "y0")))), #Str(vecmax(apply(abs, mapget(M, "y0R")))),
    #Str(vecmax(apply(abs, mapget(M, "S0")))), #Str(vecmax(apply(abs, mapget(M, "S0R")))), #Str(vecmax(apply(abs, mapget(M, "E4U")))));
  STG++;
}
\\ ---------------------------------------------------------------- certificate makers
\\ KCert for the approximation Xe: a0 = v mod 2, h = (v + a0) / 2, a1 = [unit part nonsquare], U the lift of the residue
\\ square root, n = 2h + 1 (the least n), R = (X al7^a0 (-1)^a1 - al7^2h U^2) / al7^n
MAXK = 0; NCK = 0; NCF = 0;
mkK(tab, N, Xe, nm) = {
  my(xv = keval(Xe), v, a0, zv, h, u, a1, U, n, R, t, c, ex);
  if (xv == 0, error("mkK: zero value ", nm));
  v = vw(xv); a0 = v % 2; zv = xv * al7^a0; h = (v + a0) / 2;
  u = zv / al7^(2 * h); a1 = ubit(u);
  U = resl(sqrt(res(u * (-1)^a1)));
  n = 2 * h + 1;
  if (2 * h >= N, error("mkK: 2h >= N for ", nm));
  R = (zv * (-1)^a1 - al7^(2 * h) * U^2) / al7^n;
  t = unitc(U);
  c = [a0, a1, h, zkl(U), zkl(t[1]), zkl(t[2]), n, zkl(R), 0, 0];
  ex = kcExprs(tab, Xe, c);
  if (keval(ex[1]) != 0 || keval(ex[2]) != 0, error("mkK: identity fails for ", nm));
  c[9] = keprec(ex[1]); c[10] = keprec(ex[2]);
  if (!kcOK(tab, N, Xe, c), error("mkK: KCert.ok fails for ", nm));
  MAXK = max(MAXK, max(c[9], c[10])); NCK++;
  c;
}
\\ FCert for the approximation (Xe, Ye) of x + y Z: a0 = [v(x) > v(y)], x' = x or al7 E4U y, w = v(x') = j + 2h,
\\ a1 = [x' / (al7^w E4U^j) nonsquare], n = w + 1, R = (x' (-1)^a1 - al7^w E4U^j U^2) / al7^n, Ry = y' / al7^w
mkF(tab, N, E4U, Xe, Ye, nm) = {
  my(xv = keval(Xe), yv = keval(Ye), E4 = zkE(E4U), vx, vy, a0, xp, yp, wv, j, h, u, a1, U, n, R, Ry, t, c, ex);
  vx = vw(xv); vy = vw(yv);
  if (vx == oo && vy == oo, error("mkF: zero value ", nm));
  if (vx <= vy, a0 = 0; xp = xv; yp = yv, a0 = 1; xp = al7 * E4 * yv; yp = xv);
  wv = vw(xp); j = wv % 2; h = (wv - j) / 2;
  u = xp / al7^wv / E4^j; a1 = ubit(u);
  U = resl(sqrt(res(u * (-1)^a1)));
  n = wv + 1;
  if (wv >= N, error("mkF: j + 2h >= N for ", nm));
  R = (xp * (-1)^a1 - al7^wv * E4^j * U^2) / al7^n;
  Ry = yp / al7^wv;
  t = unitc(U);
  c = [a0, a1, j, h, zkl(U), zkl(t[1]), zkl(t[2]), n, zkl(R), zkl(Ry), 0, 0, 0];
  ex = fcExprs(tab, E4U, Xe, Ye, c);
  if (keval(ex[1]) != 0 || keval(ex[2]) != 0 || keval(ex[3]) != 0, error("mkF: identity fails for ", nm));
  c[11] = keprec(ex[1]); c[12] = keprec(ex[2]); c[13] = keprec(ex[3]);
  if (!fcOK(tab, N, E4U, Xe, Ye, c), error("mkF: FCert.ok fails for ", nm));
  MAXK = max(MAXK, vecmax(c[11 .. 13])); NCF++;
  c;
}
\\ ---------------------------------------------------------------- stage 5: the 82 generators and kappa
{
  my(N = MN(M), E4U = mapget(M, "E4U"), okc = 1, t0 = getabstime());
  chq(N >= 2 && N == min(NY, NS), Str("M.N = min ny ns = ", N, " >= 2"));
  cL = vector(29, s, my(a = apL(M, ofL(gLd[s]))); [mkK(tab, N, a[1], Str("gL ", s - 1, " c0")), mkK(tab, N, a[2], Str("gL ", s - 1, " c1"))]);
  printf("  29 gensL certificates (%d ms)\n", getabstime() - t0);
  cN = vector(53, s, my(a = apN(M, ofN(gNd[s]))); [mkK(tab, N, a[1], Str("gN ", s - 1, " c2")), mkK(tab, N, a[2], Str("gN ", s - 1, " c3")),
    mkF(tab, N, E4U, a[3], a[4], Str("gN ", s - 1, " c4"))]);
  printf("  53 gensN certificates (%d ms)\n", getabstime() - t0);
  cK = vector(2, i, mkF(tab, N, E4U, kapXE(i - 1), KINT(0), Str("kappa ", i - 1)));
  chq(vecmin(vector(29, s, okLOK(tab, M, cL[s], s - 1))), "okL tab M (cL s) s for the 29 gensL");
  chq(vecmin(vector(53, s, okNOK(tab, M, cN[s], s - 1))), "okN tab M (cN s) s for the 53 gensN");
  chq(vecmin(vector(2, i, fcOK(tab, N, E4U, kapXE(i - 1), KINT(0), cK[i]))), "cK: FCert.ok at kapXE i, int 0 (i = 0, 1)");
  \\ the certificate bits against the classes of the true local values (pr^240)
  for (s = 1, 29, if (bitsL(cL[s]) != bits2row(clsLh(valL(gLd[s]))), okc = 0; printf("  class mismatch gL %d\n", s - 1)));
  for (s = 1, 53, if (bitsN(cN[s]) != bits2row(clsNh(valN(gNd[s]))), okc = 0; printf("  class mismatch gN %d\n", s - 1)));
  chq(okc, "the 82 generator rows equal the square classes of the local values at pr^240 (method of local_data_w7.gp)");
  chq(vector(2, i, kapLow(i - 1) + 256 * fcBits(cK[i])) == vector(2, i, bits2row(kapClsh[i])), "the kappa rows kapLow i + 256 cK_i.bits equal the classes of al7, -1 at the five components");
  printf("  largest precision %d; KCert %d, FCert %d; 2h, j + 2h at most %d (N = %d) (%d ms)\n", MAXK, NCK, NCF,
    vecmax(concat([vector(29, s, 2 * max(cL[s][1][3], cL[s][2][3])), vector(53, s, max(2 * max(cN[s][1][3], cN[s][2][3]), cN[s][3][3] + 2 * cN[s][3][4]))])), N, getabstime() - t0);
  STG++;
}
\\ ---------------------------------------------------------------- stage 6: the four points (PtSq) and the three pairs (PairData)
\\ PtSq: Y = 4 fRev_1(x) (gE 1 (.lin x) 0), m = v(Y) even, T = al7^(m/2) t (t the lift of the residue square root of
\\ Y / al7^m), B = T^2 / al7^m = t^2, A = (Y - T^2) / al7^(m+1)
mkPt(tab, xv) = {
  my(xl = zkl(xv), Ye = gE1(KLIN(xl)), Yv, m, tt, T, B, A, t, p, ex);
  Yv = keval(Ye);
  if (Yv != fr4(xv), error("mkPt: gE mirror"));
  m = vw(Yv); if (m % 2, error("mkPt: odd valuation"));
  tt = resl(sqrt(res(Yv / al7^m)));
  T = al7^(m / 2) * tt; B = T^2 / al7^m; A = (Yv - T^2) / al7^(m + 1);
  t = unitc(B);
  p = [xl, zkl(T), zkl(A), zkl(B), zkl(t[1]), zkl(t[2]), m, 0, 0, 0];
  ex = ptExprs(tab, p);
  if (keval(ex[1]) != 0 || keval(ex[2]) != 0 || keval(ex[3]) != 0, error("mkPt: identity fails"));
  p[8] = keprec(ex[1]); p[9] = keprec(ex[2]); p[10] = keprec(ex[3]);
  if (!ptOK(tab, p), error("mkPt: PtSq.ok fails"));
  p;
}
mkPair(tab, M, pts, i1, i2) = {
  my(x1 = zkE(pts[i1 + 1][1]), x2 = zkE(pts[i2 + 1][1]), pd = Map(), P = -(x1 + x2), R = x1 * x2, dv, dW, t, UL, UN, tL, tN, ex, N = MN(M), E4U = mapget(M, "E4U"), tl, tn, a, nn);
  mapput(pd, "i1", i1); mapput(pd, "i2", i2); mapput(pd, "P", zkl(P)); mapput(pd, "R", zkl(R));
  dv = vw(x1 - x2); dW = (x1 - x2) / al7^dv; t = unitc(dW);
  mapput(pd, "dv", dv); mapput(pd, "dW", zkl(dW)); mapput(pd, "dWi", zkl(t[1])); mapput(pd, "dWc", zkl(t[2]));
  mapput(pd, "kd1", 0); mapput(pd, "kd2", 0); mapput(pd, "kP", 0); mapput(pd, "kR", 0);
  mapput(pd, "lamL", 92); mapput(pd, "lamN", 368);
  UL = Ladd(Ladd(Lmul(alR, alR), Lsc(P, alR)), [R, 0]);
  UN = Nadd(Nadd(Nmul(beR, beR), Nsc(P, beR)), [[R, 0], [0, 0]]);
  if (isint(UL[1]) && isint(UL[2]), error("mkPair: U(alpha) integral, Lambda_L = 1 would do"));
  tL = [zkl(92^2 * UL[1]), zkl(92^2 * UL[2])];
  tN = [zkl(368^2 * UN[1][1]), zkl(368^2 * UN[1][2]), zkl(368^2 * UN[2][1]), zkl(368^2 * UN[2][2])];
  mapput(pd, "tL", tL); mapput(pd, "tN", tN);
  ex = okUExprs(tab, pts, pd);
  if (vecmax(apply(e -> keval(e) != 0, ex)), error("mkPair: okU identity fails"));
  mapput(pd, "kd1", keprec(ex[1])); mapput(pd, "kd2", keprec(ex[2])); mapput(pd, "kP", keprec(ex[3])); mapput(pd, "kR", keprec(ex[4]));
  ex = okTExprs(zkl(P), zkl(R), tL, tN, 92, 368);
  if (vecmax(apply(e -> keval(e) != 0, ex)), error("mkPair: okT identity fails"));
  mapput(pd, "precT", vecmax(apply(keprec, ex)));
  tl = ofL(tL); tn = ofN(tN); a = apL(M, tl); nn = apN(M, tn);
  mapput(pd, "c0", mkK(tab, N, a[1], Str("pair ", i2, " c0"))); mapput(pd, "c1", mkK(tab, N, a[2], Str("pair ", i2, " c1")));
  mapput(pd, "c2", mkK(tab, N, nn[1], Str("pair ", i2, " c2"))); mapput(pd, "c3", mkK(tab, N, nn[2], Str("pair ", i2, " c3")));
  mapput(pd, "c4", mkF(tab, N, E4U, nn[3], nn[4], Str("pair ", i2, " c4")));
  pd;
}
{
  my(t0 = getabstime(), okc = 1);
  pts = vector(4, i, mkPt(tab, PTS[i]));
  chq(vecmin(vector(4, i, ptOK(tab, pts[i]))), Str("PtSq.ok for the 4 points; m = ", vector(4, i, pts[i][7]), ", precisions ", vector(4, i, pts[i][8 .. 10])));
  pairs = vector(3, i, mkPair(tab, M, pts, 0, i));
  chq(vecmin(vector(3, i, okUOK(tab, pts, pairs[i]) && okTOK(pairs[i]) && okCOK(tab, M, pairs[i]))), "okU, toPt.okT, okC for the 3 pairs (0, i)");
  for (i = 1, 3, printf("  pair (0, %d): dv %d, kd1 %d, kd2 %d, kP %d, kR %d, precT %d, bits %d\n", i, mapget(pairs[i], "dv"), mapget(pairs[i], "kd1"),
    mapget(pairs[i], "kd2"), mapget(pairs[i], "kP"), mapget(pairs[i], "kR"), mapget(pairs[i], "precT"), pdBits(pairs[i])));
  \\ the pair rows against the classes of (x1 - tau)(x2 - tau) at pr^240
  for (i = 1, 3, if (pdBits(pairs[i]) != bits2row(Mod(ptClsh(PTS[1]) + ptClsh(PTS[i + 1]), 2)), okc = 0));
  chq(okc, "the 3 pair rows equal the sum of the classes of x1 - T and x_i - T at pr^240 (method of local_data_w7.gp)");
  \\ the true local value of Lambda^2 U(tau) is within pr^N of the approximation at every component
  my(okv = 1);
  for (i = 1, 3, my(pd = pairs[i], tl = valL(mapget(pd, "tL")), tn = valN(mapget(pd, "tN")), x1 = PTS[1], x2 = PTS[i + 1], L2 = 92^2, N2 = 368^2);
    if (vw(ipL(tl) - L2 * (x1 - tq1) * (x2 - tq1)) < 200 || vw(imL(tl) - L2 * (x1 - tq2) * (x2 - tq2)) < 200, okv = 0);
    if (vw(inN(tn, 1) - N2 * (x1 - th1) * (x2 - th1)) < 200 || vw(inN(tn, -1) - N2 * (x1 - th2) * (x2 - th2)) < 200, okv = 0));
  chq(okv, "tL, tN evaluate at the K_w components to Lambda^2 (x1 - tau)(x2 - tau) (pr^200)");
  printf("  points and pairs (%d ms)\n", getabstime() - t0);
  STG++;
}
\\ ---------------------------------------------------------------- stage 7: the F_2 data
f2m(rows, nb) = matrix(#rows, nb, r, j, bittest(rows[r], j - 1));
annRows(rows, nb) = { my(K = lift(matker(Mod(f2m(rows, nb), 2)))); vector(#K, j, sum(i = 1, nb, K[i, j] * 2^(i - 1))); }
{
  Akap = vector(2, i, kapLow(i - 1) + 256 * fcBits(cK[i]));
  Amu = vector(3, i, pdBits(pairs[i]));
  Cg = concat(vector(29, s, bitsL(cL[s])), vector(53, s, bitsN(cN[s])));
  chq(matrank(Mod(f2m(Akap, 10), 2)) == 2 && matrank(Mod(f2m(concat(Akap, Amu), 10), 2)) == 5, "kappa has rank 2, kappa and mu span 5 = 10 / 2 dimensions");
  \\ QI: the annihilator of kappa (8 forms); TI: the left inverse of the forms QI on the mu coordinates
  QI = annRows(Akap, 10); nQI = #QI;
  my(Rq = vector(nQI, q, dotRow(10, i -> getD(Amu, i), QI[q], 3)), Rm = matrix(3, nQI, k, q, bittest(Rq[q], k - 1)));
  TI = vector(3, k, my(sol = matinverseimage(Mod(Rm, 2), Mod(vectorv(3, l, l == k), 2))); if (#sol == 0, error("TI: no solution")); sum(q = 1, nQI, lift(sol[q]) * 2^(q - 1)));
  \\ QC: the annihilator of kappa and mu (5 forms) combined so that dotRow Cg QC = C7Rows
  my(Q = annRows(concat(Akap, Amu), 10), Rc, C7, Tm);
  chq(#Q == 5, "the annihilator of span(kappa, mu) has dimension 5");
  Rc = matrix(5, 82, r, s, dotB(10, Q[r], Cg[s]));
  C7 = matrix(5, 82, r, s, bittest(C7Rows[r], s - 1));
  chq(matrank(Mod(Rc, 2)) == 5, "the 5 annihilator forms give 5 independent rows on the generators");
  Tm = matinverseimage(Mod(Rc~, 2), Mod(C7~, 2));
  if (#Tm == 0, error("QC: C7Rows not in the span of the rows"));
  Tm = lift(Tm)~;
  QC = vector(5, r, my(q = 0); for (j = 1, 5, if (Tm[r, j] % 2, q = bitxor(q, Q[j]))); q);
  \\ the W7Check statements, emulated
  chq(vector(2, i, Akap[i]) == vector(2, i, kapLow(i - 1) + 256 * fcBits(cK[i])), "kap_bits");
  chq(vector(3, i, Amu[i]) == vector(3, i, pdBits(pairs[i])), "mu_bits");
  chq(vecmin(vector(29, s, Cg[s] == bitsL(cL[s]))) && vecmin(vector(53, s, Cg[29 + s] == bitsN(cN[s]))), "cgL_bits, cgN_bits");
  chq(annOK(10, l -> getD(Akap, l), 2, q -> getD(QI, q), nQI), Str("annI (nQI = ", nQI, ")"));
  chq(leftInvOK(q -> dotRow(10, i -> getD(Amu, i), getD(QI, q), 3), nQI, 3, q -> getD(TI, q)), "leftInv");
  chq(annOK(10, l -> getD(Akap, l), 2, q -> getD(QC, q), 5), "annCk");
  chq(annOK(10, i -> getD(Amu, i), 3, q -> getD(QC, q), 5), "annCm");
  chq(vecmin(vector(5, q, dotRow(10, s -> getD(Cg, s), getD(QC, q - 1), 82) == C7Rows[q])), "c7_rows: dotRow 10 Cg QC_q 82 = C7Rows_q for q < 5");
  \\ the QC of local_data_w7.gp (bit i - 1 = column i of its printed matrix) is the same (QC is unique: the rows have rank 5)
  my(QC1 = [0, 1, 1, 1, 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0, 0, 1, 0, 0; 1, 1, 0, 0, 0, 0, 0, 0, 1, 1; 1, 1, 0, 1, 1, 0, 0, 0, 1, 0; 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]);
  chq(QC == vector(5, r, sum(i = 1, 10, QC1[r, i] * 2^(i - 1))), "QC equals the QC printed by local_data_w7.gp");
  printf("Akap = %s, Amu = %s, QI = %s, TI = %s, QC = %s\n", Akap, Amu, QI, TI, QC);
  STG++;
}
\\ ---------------------------------------------------------------- stage 8: negative controls (each must fail)
{
  my(N = MN(M), E4U = mapget(M, "E4U"), a = apL(M, ofL(gLd[1])), nn = apN(M, ofN(gNd[1])), c, p, pd, t, Cg2, Ak2, tb2, M2);
  c = cL[1][1]; c[8][1] += 1; chq(!kcOK(tab, N, a[1], c), "negative control: KCert of gL 0 with R_0 + 1 fails");
  c = cL[1][1]; c[2] = 1 - c[2]; chq(!kcOK(tab, N, a[1], c), "negative control: KCert of gL 0 with a1 flipped fails");
  c = cL[1][1]; c[1] = 1 - c[1]; chq(!kcOK(tab, N, a[1], c), "negative control: KCert of gL 0 with a0 flipped fails");
  c = cL[1][1]; c[9] -= 1; chq(!kcOK(tab, N, a[1], c), "negative control: KCert of gL 0 at precision k1 - 1 fails (k1 minimal)");
  c = cN[1][1]; chq(!kcOK(tab, 2 * c[3], nn[1], c), "negative control: KCert of gN 0 c2 with N = 2h fails (2h < N)");
  c = cL[1][2]; chq(!kcOK(tab, N, a[1], c), "negative control: the c1 certificate of gL 0 fails on the c0 approximation XLp");
  c = cN[1][3]; c[10][1] += 1; chq(!fcOK(tab, N, E4U, nn[3], nn[4], c), "negative control: FCert of gN 0 with Ry_0 + 1 fails");
  c = cN[1][3]; c[1] = 1 - c[1]; chq(!fcOK(tab, N, E4U, nn[3], nn[4], c), "negative control: FCert of gN 0 with a0 flipped fails");
  c = cN[1][3]; c[2] = 1 - c[2]; chq(!fcOK(tab, N, E4U, nn[3], nn[4], c), "negative control: FCert of gN 0 with a1 flipped fails");
  c = cK[1]; chq(!fcOK(tab, N, E4U, kapXE(1), KINT(0), c), "negative control: the certificate of al7 fails on -1");
  p = pts[1]; p[3][1] += 1; chq(!ptOK(tab, p), "negative control: PtSq 0 with A_0 + 1 fails");
  p = pts[1]; p[7] -= 2; chq(!ptOK(tab, p), "negative control: PtSq 0 with m - 2 fails");
  pd = pairs[1]; t = mapget(pd, "P"); t[1] += 1; pd = Map(); foreach(Mat(pairs[1])[, 1], kk, mapput(pd, kk, mapget(pairs[1], kk))); mapput(pd, "P", t);
  chq(!okUOK(tab, pts, pd), "negative control: pair 0 with P_0 + 1 fails okU");
  pd = Map(); foreach(Mat(pairs[1])[, 1], kk, mapput(pd, kk, mapget(pairs[1], kk))); mapput(pd, "lamL", 1);
  chq(!okTOK(pd), "negative control: pair 0 with lamL = 1 fails okT");
  pd = Map(); foreach(Mat(pairs[1])[, 1], kk, mapput(pd, kk, mapget(pairs[1], kk))); mapput(pd, "i2", 2);
  chq(!okUOK(tab, pts, pd), "negative control: pair 0 with i2 = 2 (wrong point) fails okU");
  M2 = Map(); foreach(Mat(M)[, 1], kk, mapput(M2, kk, mapget(M, kk))); t = mapget(M, "y0R"); t[1] += 1; mapput(M2, "y0R", t);
  chq(!modelOK(tab, M2), "negative control: the model with y0R_0 + 1 fails");
  M2 = Map(); foreach(Mat(M)[, 1], kk, mapput(M2, kk, mapget(M, kk))); mapput(M2, "ny", NY + 1);
  chq(!modelOK(tab, M2), "negative control: the model with ny + 1 fails");
  tb2 = tab; tb2[9][1] += 1; chq(!kecheck(powOKe(tb2, 7), tabK[8]) && !kecheck(powOKe(tb2, 7), 4096), "negative control: tab_8 + (1, 0, ...) fails powOK");
  Cg2 = Cg; Cg2[1] = bitxor(Cg2[1], 1);
  chq(!vecmin(vector(5, q, dotRow(10, s -> getD(Cg2, s), getD(QC, q - 1), 82) == C7Rows[q])), "negative control: Cg_0 with bit 0 flipped fails c7_rows");
  Ak2 = Akap; Ak2[2] = bitxor(Ak2[2], 2^8);
  chq(!annOK(10, l -> getD(Ak2, l), 2, q -> getD(QC, q), 5), "negative control: the -1 row with bit 8 flipped fails annCk");
  chq(!leftInvOK(q -> dotRow(10, i -> getD(Amu, i), getD(QI, q), 3), nQI, 3, q -> getD([TI[2], TI[1], TI[3]], q)), "negative control: TI with two entries swapped fails leftInv");
  STG++;
}
\\ ---------------------------------------------------------------- stage 9: Lean output (named-field structure instances)
bstr(bb) = if (bb, "true", "false");
kcStr(c) = { Str("{ a0 := ", bstr(c[1]), ", a1 := ", bstr(c[2]), ", h := ", c[3], ", U := ", c[4], ", Ui := ", c[5], ", Uc := ", c[6],
  ", n := ", c[7], ", R := ", c[8], ", k1 := ", c[9], ", k2 := ", c[10], " }"); }
fcStr(c) = { Str("{ a0 := ", bstr(c[1]), ", a1 := ", bstr(c[2]), ", j := ", c[3], ", h := ", c[4], ", U := ", c[5], ", Ui := ", c[6], ", Uc := ", c[7],
  ", n := ", c[8], ", R := ", c[9], ", Ry := ", c[10], ", k1 := ", c[11], ", k2 := ", c[12], ", k3 := ", c[13], " }"); }
ptStr(p) = { Str("{ x := ", p[1], ", T := ", p[2], ", A := ", p[3], ", B := ", p[4], ", Bi := ", p[5], ", Cb := ", p[6], ", m := ", p[7],
  ", k1 := ", p[8], ", k2 := ", p[9], ", k3 := ", p[10], " }"); }
modelStr(M) = { my(ks = mapget(M, "ks")); Str("{ y0 := ", mapget(M, "y0"), ", ny := ", mapget(M, "ny"), ", y0R := ", mapget(M, "y0R"), ", y0i := ", mapget(M, "y0i"),
  ", y0c := ", mapget(M, "y0c"), ", S0 := ", mapget(M, "S0"), ", ns := ", mapget(M, "ns"), ", S0R := ", mapget(M, "S0R"), ", S0i := ", mapget(M, "S0i"),
  ", S0c := ", mapget(M, "S0c"), ", E4U := ", mapget(M, "E4U"), ", E4Ui := ", mapget(M, "E4Ui"), ", E4Uc := ", mapget(M, "E4Uc"),
  ", k1 := ", ks[1], ", k2 := ", ks[2], ", k3 := ", ks[3], ", k4 := ", ks[4], ", k5 := ", ks[5], ", k6 := ", ks[6], " }"); }
pairStr(pd) = { Str("{ i1 := ", mapget(pd, "i1"), ", i2 := ", mapget(pd, "i2"), ", P := ", mapget(pd, "P"), ", R := ", mapget(pd, "R"),
  ", kP := ", mapget(pd, "kP"), ", kR := ", mapget(pd, "kR"), ", tL := ", mapget(pd, "tL"), ", tN := ", mapget(pd, "tN"), ", precT := ", mapget(pd, "precT"),
  ", lamL := ", mapget(pd, "lamL"), ", lamN := ", mapget(pd, "lamN"), ", c0 := ", kcStr(mapget(pd, "c0")), ", c1 := ", kcStr(mapget(pd, "c1")),
  ", c2 := ", kcStr(mapget(pd, "c2")), ", c3 := ", kcStr(mapget(pd, "c3")), ", c4 := ", fcStr(mapget(pd, "c4")), ", dv := ", mapget(pd, "dv"),
  ", dW := ", mapget(pd, "dW"), ", dWi := ", mapget(pd, "dWi"), ", dWc := ", mapget(pd, "dWc"), ", kd1 := ", mapget(pd, "kd1"), ", kd2 := ", mapget(pd, "kd2"), " }"); }
nlist(p, n) = { my(s = ""); for (i = 0, n - 1, s = Str(s, if (i, ", ", ""), p, i)); Str("[", s, "]"); }
wl(fn, str) = write(Str(OUTD, fn), str);
lhead(fn, title, body) = {
  system(Str("rm -f ", OUTD, fn));
  wl(fn, "import FurioLombardo.Discharge.SelmerBasis.W7Spec\n");
  wl(fn, Str("/-!\n# ", title, " (generated by code/selmer-local-conditions/lean_data_w7.gp, output lean_data_w7.out)\n\n", body, "\nFormats: W7Spec.lean.\n-/\n"));
  wl(fn, "namespace FurioLombardo.Discharge.SelmerBasis.W7\n\nopen FurioLombardo.M1\n");
}
{
  system(Str("mkdir -p ", OUTD));
  my(fn = "W7Data.lean");
  lhead(fn, "Data of the place above 7, twist 1: model, points, pairs, F₂ data",
    "The table `tab` of `al7^(2^i)` (`i < 9`) with the precisions `tabK` of `powOK`, the model `M`, the four points\n`pts` (`PtSq`), the three pairs `(0, i)` (`PairData`, `lamL = 92`, `lamN = 368`), the certificates `cK` of `al7` and\n`-1` at `F'`, and the `F₂` data: the rows `Akap`, `Amu`, `Cg` (bits `2c`, `2c + 1` at the component `c`), the forms `QI`\n(`nQI` of them, annihilating `Akap`) with the left inverse `TI`, and the forms `QC` (`dotRow 10 Cg QC = C7Rows`).\n");
  for (i = 1, 9, wl(fn, Str("def tab_", i - 1, " : List ℤ := ", tab[i])));
  wl(fn, Str("\ndef tab : List (List ℤ) := ", nlist("tab_", 9), "\n"));
  wl(fn, Str("def tabK : List ℕ := ", tabK, "\n"));
  wl(fn, Str("def M : Model := ", modelStr(M), "\n"));
  for (i = 1, 4, wl(fn, Str("def pt_", i - 1, " : PtSq := ", ptStr(pts[i]))));
  wl(fn, Str("\ndef pts : List PtSq := ", nlist("pt_", 4), "\n"));
  for (i = 1, 3, wl(fn, Str("def pair_", i - 1, " : PairData := ", pairStr(pairs[i]))));
  wl(fn, Str("\ndef pairs : List PairData := ", nlist("pair_", 3), "\n"));
  for (i = 1, 2, wl(fn, Str("def cK_", i - 1, " : FCert := ", fcStr(cK[i]))));
  wl(fn, Str("\ndef cK : List FCert := ", nlist("cK_", 2), "\n"));
  wl(fn, Str("def Akap : List ℕ := ", Akap, "\n"));
  wl(fn, Str("def Amu : List ℕ := ", Amu, "\n"));
  wl(fn, Str("def Cg : List ℕ := ", Cg, "\n"));
  wl(fn, Str("def QI : List ℕ := ", QI, "\n"));
  wl(fn, Str("def nQI : ℕ := ", nQI, "\n"));
  wl(fn, Str("def TI : List ℕ := ", TI, "\n"));
  wl(fn, Str("def QC : List ℕ := ", QC, "\n"));
  wl(fn, "end FurioLombardo.Discharge.SelmerBasis.W7");
  fn = "W7DataL.lean";
  lhead(fn, "Certificates of the 29 gensL at the place above 7, twist 1",
    "`cL s`: the `KCert`s of `gensL s` at the components 0 (`XLp`) and 1 (`XLm`).\n");
  for (s = 1, 29, wl(fn, Str("def cL_", s - 1, " : KCert × KCert := (", kcStr(cL[s][1]), ", ", kcStr(cL[s][2]), ")")));
  wl(fn, Str("\ndef cL : List (KCert × KCert) := ", nlist("cL_", 29), "\n"));
  wl(fn, "end FurioLombardo.Discharge.SelmerBasis.W7");
  fn = "W7DataN.lean";
  lhead(fn, "Certificates of the 53 gensN at the place above 7, twist 1",
    "`cN s`: the `KCert`s of `gensN s` at the components 2, 3 (`XNs`, `S ≈ ± S0`) and the `FCert` at `F'` (`XLm` of the two\ncoordinates).\n");
  for (s = 1, 53, wl(fn, Str("def cN_", s - 1, " : KCert × KCert × FCert := (", kcStr(cN[s][1]), ", ", kcStr(cN[s][2]), ", ", fcStr(cN[s][3]), ")")));
  wl(fn, Str("\ndef cN : List (KCert × KCert × FCert) := ", nlist("cN_", 53), "\n"));
  wl(fn, "end FurioLombardo.Discharge.SelmerBasis.W7");
  \\ read back the list-valued definitions
  my(D = Str(OUTD, "W7Data.lean"));
  chq(vector(9, i, getdef(D, Str("tab_", i - 1))) == tab && getdef(D, "tabK") == tabK && getdef(D, "Akap") == Akap && getdef(D, "Amu") == Amu
    && getdef(D, "Cg") == Cg && getdef(D, "QI") == QI && getdef(D, "nQI") == nQI && getdef(D, "TI") == TI && getdef(D, "QC") == QC,
    "W7Data.lean read back: tab, tabK, Akap, Amu, Cg, QI, nQI, TI, QC");
  system(Str("wc -c ", OUTD, "W7Data.lean ", OUTD, "W7DataL.lean ", OUTD, "W7DataN.lean"));
  STG++;
}
if (STG != NSTG, printf("FAILED: %d of %d braced stages completed (a stage stopped on an error)\n", STG, NSTG); NF++);
printf("DONE, %d failed checks (%d ok, %d ms)\n", NF, NOK, getabstime() - T00);
