\\ local_data_w7.gp: the local data at the place w7 above 7 (e = 7, f = 3) for twist 1,
\\ in the tower model of the Lean side: iota+- : L42 -> K_w (omega -> +-y, y^2 = eps), N84 -> K_w over iota+
\\ (omega_N -> +-s, s^2 = iota+(eN)), N84 -> F' = K_w(z') over iota- (z'^2 = iota-(eN), odd valuation).
\\ Arithmetic in O_K21 / pr^N (N = NPREC pi-units, pr = (al7)); every approximation is a global element of K21.
\\ Data read from the Lean sources: fL (M1/Basic.lean), Dz, zkNum (M1/DataField.lean), epsL (M3b/K21Defs.lean),
\\ eaL, ebL (M3b/DataL.lean), al7 (M2/SpecialData.lean), FnData, qData, hData, qDen, hDen (M3a/DataBruin.lean),
\\ gL_i, gN_j, alphaL, alphaDen, betaN, betaDen (SelmerBasis/SUnitData.lean), C7Rows (SelmerBasis/AssemblyData.lean).
\\ Square classes: at a component K_w, (v(x) mod 2, [x / al7^v(x) has a nonsquare residue in F_343]); at F',
\\ with the uniformizer Pi' = z' / al7^k (v(iota-(eN)) = 2k + 1), (v_Pi'(x) mod 2, [unit part nonsquare]).
\\ Run from code/selmer-local-conditions: gp -q local_data_w7.gp < /dev/null
[x, b, w, z, y];
default(parisizemax, 1500 * 10^6);
default(nbthreads, 1);
NF = 0; NOK = 0;
chq(c, msg) = if (c, NOK++; printf("ok: %s\n", msg), NF++; printf("CHECK FAILED: %s\n", msg));
LEAN = "../../FurioLombardo/";
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
fL = getdef(Str(LEAN, "M1/Basic.lean"), "fL");
Dz = getdef(Str(LEAN, "M1/DataField.lean"), "Dz");
zkNum = getdef(Str(LEAN, "M1/DataField.lean"), "zkNum");
epsL = getdef(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL");
eaL = getdef(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL");
ebL = getdef(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL");
al7L = getdef(Str(LEAN, "M2/SpecialData.lean"), "al7");
DB = Str(LEAN, "Discharge/M3a/DataBruin.lean");
FnData = getdef(DB, "FnData"); qData = getdef(DB, "qData"); hData = getdef(DB, "hData");
qDen = getdef(DB, "qDen"); hDen = getdef(DB, "hDen");
SU = Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean");
gLd = vector(29, i, getdef(SU, Str("gL_", i - 1)));
gNd = vector(53, j, getdef(SU, Str("gN_", j - 1)));
alphaL = getdef(SU, "alphaL"); alphaDen = getdef(SU, "alphaDen");
betaN = getdef(SU, "betaN"); betaDen = getdef(SU, "betaDen");
C7Rows = getdef(Str(LEAN, "Discharge/SelmerBasis/AssemblyData.lean"), "C7Rows");
{
chq(#fL == 22 && #zkNum == 21 && #epsL == 21 && #al7L == 21 && #FnData == 2 && #alphaL == 2 && #betaN == 4 && #C7Rows == 5,
  "Lean data parsed (fL, zkNum, epsL, eaL, ebL, al7, FnData, qData, hData, 29 gL, 53 gN, alphaL, betaN, C7Rows)");
}
fZ = Pol(Vecrev(fL), 'b);
W = vector(21, j, Pol(Vecrev(zkNum[j]), 'b) / Dz);
nfK = nfinit(fZ);
chq(vector(21, j, Mod(nfbasistoalg(nfK, vectorv(21, i, i == j)), fZ)) == vector(21, j, Mod(W[j], fZ)), "nfinit(fL).zk is Lean's basis zkNum / Dz");
zkE(a) = nfbasistoalg(nfK, Col(a));
zkc(g) = nfalgtobasis(nfK, g)~;
eps = zkE(epsL); ea = zkE(eaL); eb = zkE(ebL); al7 = zkE(al7L);
P7 = idealprimedec(nfK, 7);
chq(#P7 == 1 && P7[1].e == 7 && P7[1].f == 3, "7 has a single prime pr above it in K21, e = 7, f = 3");
pr = P7[1];
chq(nfeltval(nfK, al7, pr) == 1 && abs(norm(al7)) == 343, "al7 generates pr (v = 1, |N(al7)| = 343)");
modP = nfmodprinit(nfK, pr);
vw(g) = if (g == 0, oo, nfeltval(nfK, g, pr));
\\ residue in F_343 of a pr-unit
res(g) = nfmodpr(nfK, g, modP);
\\ the class bit of a unit: 1 iff its residue is a nonsquare in F_343
ubit(g) = my(r = res(g)); if (r == 0, error("ubit: not a unit")); !issquare(r);
\\ square class at a K_w component of a global approximation g (valid when v(g) < precision)
clsK(g) = my(v = vw(g)); [v % 2, ubit(g / al7^v)];
\\ ---------------------------------------------------------------- arithmetic mod pr^N
NPREC = 240;
IP = idealpow(nfK, pr, NPREC);
M7 = NPREC \ 7 + 2;
\\ g with a denominator d prime to 7 is replaced by d g (d^-1 mod 7^M7), equal to g mod 7^M7 O_K, inside pr^N
intz(g) = my(v = nfalgtobasis(nfK, g), d = denominator(v)); if (d % 7 == 0, error("intz: denominator divisible by 7")); nfbasistoalg(nfK, (d * v) * lift(Mod(1, 7^M7) / d));
red(g) = nfbasistoalg(nfK, nfeltreduce(nfK, nfalgtobasis(nfK, intz(g)), IP));
\\ inverse of a pr-unit modulo pr^N (Newton from the residue inverse)
invN(u) = {
  my(z = nfbasistoalg(nfK, nfmodprlift(nfK, 1 / res(u), modP)), k = 1);
  while (k < NPREC, z = red(z * (2 - u * z)); k *= 2);
  if (vw(red(u * z) - 1) < NPREC, error("invN: no inverse mod pr^N")); z;
}
\\ square root modulo pr^N of a pr-unit with square residue (Newton, p odd)
sqrtN(u) = {
  my(r0 = sqrt(res(u)), r = nfbasistoalg(nfK, nfmodprlift(nfK, r0, modP)), k = 1);
  while (k < NPREC, r = red(r - (r^2 - u) * invN(2 * r)); k *= 2);
  r;
}
\\ ---------------------------------------------------------------- 1. eps and the two embeddings of L42
vE = vw(eps);
printf("v(eps) = %d, residue of eps a square in F_343: %d\n", vE, issquare(res(eps)));
chq(vE == 0 && issquare(res(eps)), "eps is a pr-unit with square residue, so sqrt(eps) lies in K_w (Hensel, p odd)");
y0 = sqrtN(eps);
chq(vw(y0^2 - eps) >= NPREC, Str("y0^2 = eps mod pr^", NPREC));
eNp(y) = (ea + eb * y) / 2;
e1 = eNp(y0); e2 = eNp(-y0);
printf("v(iota(eN)) at omega -> y0: %d, at omega -> -y0: %d\n", vw(e1), vw(e2));
{
  my(c1 = clsK(e1), c2 = clsK(e2));
  printf("classes [v mod 2, nonsquare unit]: omega -> y0: %s, omega -> -y0: %s\n", c1, c2);
  if (c1 == [0, 0], ypl = y0, if (c2 == [0, 0], ypl = -y0, error("no embedding with iota(eN) a square")));
}
\\ iota+ : omega -> ypl (eN a square), iota- : omega -> -ypl
eP = eNp(ypl); eM = eNp(-ypl);
kP = vw(eP) / 2; vM = vw(eM); kM = (vM - 1) / 2;
chq(vw(eP) % 2 == 0 && clsK(eP) == [0, 0], Str("iota+(eN) is a square in K_w (valuation ", vw(eP), ", unit part square residue)"));
chq(vM % 2 == 1, Str("iota-(eN) has odd valuation ", vM, ", so F' = K_w(sqrt iota-(eN)) is ramified quadratic"));
s0 = al7^kP * sqrtN(eP / al7^(2 * kP));
chq(vw(red(s0^2 - eP)) >= NPREC - 2 * kP || vw(s0^2 - eP) >= NPREC, "s0^2 = iota+(eN) mod pr^(N - 2 kP)");
\\ ---------------------------------------------------------------- 2. the five components and their roots
KT = 2;  \\ twist 1 (index 2 of the Lean lists)
fRevC = vector(7, j, zkE(FnData[KT][7 - j + 1]) / 4);  \\ coefficient of x^(j-1) is FnData[k][6 - (j-1)] / 4
fRev1(t) = sum(j = 1, 7, fRevC[j] * t^(j - 1));
c1 = fRevC[7];
qC = [zkE(qData[KT][1]) / qDen[KT], zkE(qData[KT][2]) / qDen[KT], 1];
hC = [zkE(hData[KT][1]) / hDen[KT], zkE(hData[KT][2]) / hDen[KT], zkE(hData[KT][3]) / hDen[KT], zkE(hData[KT][4]) / hDen[KT], 1];
qP(t) = sum(j = 1, 3, qC[j] * t^(j - 1));
hP(t) = sum(j = 1, 5, hC[j] * t^(j - 1));
{
  my(X = 'X, ok = 1, fq = c1 * sum(j = 1, 3, qC[j] * X^(j - 1)) * sum(j = 1, 5, hC[j] * X^(j - 1)));
  chq(fq == sum(j = 1, 7, fRevC[j] * X^(j - 1)), "fRev 1 = c q h over K21 (exact)");
}
printf("v(c1) = %d\n", vw(c1));
\\ roots: q at omega -> +-ypl; h at iota+ with z -> +-s0; h at iota- in F' = K_w(z'), z'^2 = eM
aR(y) = (zkE(alphaL[1]) + zkE(alphaL[2]) * y) / alphaDen;
b0(y) = (zkE(betaN[1]) + zkE(betaN[2]) * y) / betaDen;
b1(y) = (zkE(betaN[3]) + zkE(betaN[4]) * y) / betaDen;
tq1 = aR(ypl); tq2 = aR(-ypl);
th1 = b0(ypl) + b1(ypl) * s0; th2 = b0(ypl) - b1(ypl) * s0;
thA = b0(-ypl); thB = b1(-ypl);  \\ the root thA + thB z' in F'
\\ F' arithmetic: pairs [A, B] = A + B z', z'^2 = eM
fmul(u, v) = [u[1] * v[1] + eM * u[2] * v[2], u[1] * v[2] + u[2] * v[1]];
fpoly(C, r) = my(acc = [0, 0]); forstep (j = #C, 1, -1, acc = fmul(acc, r); acc[1] += C[j]); acc;
{
  my(hA = fpoly(hC, [thA, thB]));
  chq(vw(red(qP(tq1))) >= NPREC - 10 && vw(red(qP(tq2))) >= NPREC - 10, "q(iota+-(alphaR)) = 0 mod pr^(N - 10)");
  chq(vw(red(hP(th1))) >= NPREC - 10 && vw(red(hP(th2))) >= NPREC - 10, "h(iota+(betaR)) at z -> +-s0 = 0 mod pr^(N - 10)");
  chq(vw(red(hA[1])) >= NPREC - 10 && vw(red(hA[2])) >= NPREC - 10, "h(iota-(betaR)) = 0 in F' (both coordinates) mod pr^(N - 10)");
  printf("root valuations: v(tq1) = %d, v(tq2) = %d, v(th1) = %d, v(th2) = %d, v(thA) = %d, v(thB) = %d\n", vw(tq1), vw(tq2), vw(th1), vw(th2), vw(thA), vw(thB));
  printf("differences: v(tq1 - tq2) = %d, v(th1 - th2) = %d, v(tq1 - th1) = %d, v(tq1 - th2) = %d, v(tq2 - th1) = %d, v(tq2 - th2) = %d, v(tq1 - thA) = %d, v(th1 - thA) = %d\n",
    vw(tq1 - tq2), vw(th1 - th2), vw(tq1 - th1), vw(tq1 - th2), vw(tq2 - th1), vw(tq2 - th2), vw(tq1 - thA), vw(th1 - thA));
}
\\ ---------------------------------------------------------------- 3. square classes at the five components
\\ components (this script's order): 1 = q at iota+ (root tq1), 2 = q at iota- (tq2), 3 = h at iota+, z -> s0 (th1),
\\ 4 = h at iota+, z -> -s0 (th2), 5 = h at iota- in F' (thA + thB z'); bits 2c - 1 (v mod 2), 2c (unit part nonsquare)
\\ class of A + B z' in F' (Pi' = z', since v(eM) = 1)
clsF(u) = {
  my(A = u[1], B = u[2], vA = vw(A), vB = vw(B));
  if (vA == oo && vB == oo, error("clsF: zero"));
  if (vA <= vB, [0, ubit(A / eM^vA)], [1, ubit(B / eM^vB)]);
}
chq(vM == 1, "v(iota-(eN)) = 1: z' itself is a uniformizer of F'");
chq(ubit(-1) == 1, "-1 has a nonsquare residue in F_343 (343 = 3 mod 4)");
VMAX = 0;
trk(g) = my(v = vw(g)); if (v < oo, VMAX = max(VMAX, v)); g;
clsAll(c1v, c2v, c3v, c4v, c5v) = concat([c1v, c2v, c3v, c4v, c5v]);
Z2 = [0, 0];
\\ gensL i: a0 + a1 omega; gensN j: A + B' z, A = a0 + a1 omega, B' = 2 (b0 + b1 omega)
genCls(s) = {
  if (s <= 29,
    my(g = gLd[s], a0 = zkE(g[1]), a1 = zkE(g[2]));
    clsAll(clsK(trk(a0 + a1 * ypl)), clsK(trk(a0 - a1 * ypl)), Z2, Z2, Z2),
    my(g = gNd[s - 29], a0 = zkE(g[1]), a1 = zkE(g[2]), bb0 = zkE(g[3]), bb1 = zkE(g[4]),
       Ap = a0 + a1 * ypl, Bp = 2 * (bb0 + bb1 * ypl), Am = a0 - a1 * ypl, Bm = 2 * (bb0 - bb1 * ypl));
    clsAll(Z2, Z2, clsK(trk(Ap + Bp * s0)), clsK(trk(Ap - Bp * s0)), clsF([trk(Am), trk(Bm)])));
}
Cg = matrix(10, 82, i, s, 0);
{
  for (s = 1, 82, my(v = genCls(s)); for (i = 1, 10, Cg[i, s] = v[i]));
  printf("generator classes computed; largest valuation met %d (precision %d)\n", VMAX, NPREC);
  chq(VMAX < NPREC - 40, "every valuation met is far below the precision");
}
kapCls = [clsAll([1, 0], [1, 0], [1, 0], [1, 0], clsF([al7, 0])), clsAll([0, 1], [0, 1], [0, 1], [0, 1], clsF([-1, 0]))];
printf("kappa classes: al7 %s, -1 %s\n", kapCls[1], kapCls[2]);
\\ ---------------------------------------------------------------- 4. split points
\\ class of x - T at the five components (x in K21)
ptCls(t) = clsAll(clsK(trk(t - tq1)), clsK(trk(t - tq2)), clsK(trk(t - th1)), clsK(trk(t - th2)), clsF([trk(t - thA), -thB]));
isSplit(t) = my(ft = fRev1(t), v = vw(ft)); v < NPREC - 40 && v % 2 == 0 && !ubit(ft / al7^v);
rankF2(M) = matrank(Mod(M, 2));
\\ candidates: truncations of the roots plus small multiples of powers of al7
PTS = List();
{
  my(roots = [tq1, tq2, th1, th2, thA], tried = 0);
  for (m = 1, 12, for (ri = 1, 5, for (t = -3, 3,
    my(base = nfbasistoalg(nfK, nfeltreduce(nfK, nfalgtobasis(nfK, intz(roots[ri])), idealpow(nfK, pr, m))), xx = base + t * al7^m);
    tried++;
    if (isSplit(xx),
      my(cand = concat(Vec(PTS), [xx]), M = Mat(concat([Col(kapCls[1]), Col(kapCls[2])], vector(#cand - 1, i, Col(ptCls(cand[i + 1]) + ptCls(cand[1]))))));
      if (#cand == 1 || rankF2(M) == #cand + 1, listput(PTS, xx);
        printf("  split point %d: x = root %d truncated at pr^%d plus %d al7^%d, v(f(x)) = %d\n", #PTS, ri, m, t, m, vw(fRev1(xx)))));
    if (#PTS >= 4, break(3)))));
  printf("split point search: %d candidates tried, %d points kept\n", tried, #PTS);
}
chq(#PTS == 4, "four split points whose differences D_1i = P_1 + P_i give three independent classes modulo kappa");
muCls = vector(3, i, ptCls(PTS[1]) + ptCls(PTS[i + 1]));
{
  my(V = Mat(concat([Col(kapCls[1]), Col(kapCls[2])], vector(3, i, Col(muCls[i])))));
  chq(rankF2(V) == 5, "dim span(kappa, mu) = 5 = half of dim G/G^2 = 10");
  \\ annihilator: forms q with q . V = 0
  my(Q = matker(Mod(V~, 2)));
  chq(#Q == 5, "the annihilator of span(kappa, mu) has dimension 5");
  my(R = Q~ * Mod(Cg, 2), C7 = matrix(5, 82, i, s, bittest(C7Rows[i], s - 1)));
  chq(matrank(R) == 5 && matrank(Mod(C7, 2)) == 5 && matrank(concat(R~, Mod(C7, 2)~)) == 5,
    "the rows (annihilator times generator classes) span the same space as Assembly.C7Rows (second computation of the rows at 7)");
  \\ T with T R = C7, then QC = T Q~
  my(Tm = matsolve(R~, Mod(C7, 2)~)~);
  QC = lift(Tm * Q~);
  chq(Mod(QC, 2) * Mod(Cg, 2) == Mod(C7, 2) && Mod(QC, 2) * V == 0, "QC (5 forms) annihilates kappa and mu and QC . Cg = C7Rows exactly");
}
printf("QC = %s\n", QC);
if (NF == 0, printf("DONE, 0 failed checks (%d ok)\n", NOK), printf("DONE, %d FAILED checks\n", NF));
