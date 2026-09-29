\\ chart_base_points.gp: base points of the formal chart of R7 for the twists
\\ k = 0, 1: y^2 = F_k(x), F_k = (fRev k).map sigma over K_v (v the place of K21 above 2 with e = 3).
\\ Sections:
\\  A. consistency with the Lean data (FnData of DataBruin.lean, Dz, uOdd, theta0, place of sigma);
\\  B. question 1: global points (a, b) with a in Q of height <= 1000 or a small element of Z[theta]:
\\     residue filter at 60 degree one primes (known-answer tested), survivors tested by nfroots;
\\  C. local square classes of fRev_k(a) at v: integers, the 512 classes mod 8, and an exhaustive split of O_v and
\\     of p (for s = 1/a) into classes on which both square classes are constant: no common base abscissa;
\\  D. for each chosen (k, a): the Taylor data of sqrt(f_a) at 0 (f_a = fRev_k(X + a)): beta (V0 = b beta),
\\     R0, R1, R2 (f_a - f_a(0) beta^2 = X^4 (R0 + R1 X + R2 X^2), exact identity in K21[X]), their
\\     valuations at v, the Hensel certificate for b (residue of sigma(4 f_a(0)) as Lean's zres computes it,
\\     a triple b0 with (2^m b0)^2 congruent to it modulo 2^(2m+3)), the numerators N0, N2 of R0, R2 as
\\     integral zk lists with nonzero residues at a degree one prime (Lean: zkE_ne_zero_of_res);
\\  E. second implementation of D in K_v = Q_2[b]/(g), g the cubic factor of K21 over Q_2 (factorpadic):
\\     b by Newton, V0 by the recursion V1 = f1/(2b), ..., q_j = coefficients of f_a - V0^2, valuations.
\\ Run from code/local-group:  gp -q chart_base_points.gp < /dev/null > chart_base_points.out
default(parisizemax, 2*10^9); default(nbthreads, 2);
read("chart_lib.gp");
printf("PARI/GP %s\n", version());
\\ ================= A =================
s = externstr("awk '/^def FnData/{f=1;next} f&&/^$/{exit} f' ../../FurioLombardo/Discharge/M3a/DataBruin.lean");
LF = eval(concat(s));
chq(LF == FnD, "FnData of DataBruin.lean");
print("A. FnData of DataBruin.lean = zk coordinates of 4 f_k (recomputed): OK; Dz, uOdd, theta0, place: OK");
print("   primes above 2: ", apply(q -> [q.e, q.f], idealprimedec(nf, 2)), " (one with e = 3)");
for (k = 1, 2, printf("   k = %d: v(coefficients of fRev_k), degree 0..6: %s\n", k - 1, vector(7, i, vl(polcoef(frev[k], i - 1, t)))));
\\ ================= B =================
den2 = lcm(concat(vector(2, k, vector(7, i, denominator(content(polcoef(frev[k], i - 1, t)))))));
DK = poldisc(K21);
PR = List();
{ forprime (p = 3, 5000, if (den2 % p == 0 || Dz % p == 0 || DK % p == 0, next);
    my(R = polrootsmod(K21, p)); if (#R == 0, next);
    foreach (R, r, listput(PR, [p, lift(r)])); if (#PR >= 60, break)); }
PR = Vec(PR);
redc(c, p, r) = my(e = if (type(c) == "t_POL", subst(c, b, r), c)); Mod(numerator(e), p) / Mod(denominator(e), p);
FP = vector(2, k, vector(#PR, i, my(p = PR[i][1], r = PR[i][2]); Polrev(apply(c -> redc(c, p, r), Vecrev(frev[k])), t)));
{ for (k = 1, 2, for (i = 1, 5, my(p = PR[i][1], r = PR[i][2], A = 3/7, fa = red(subst(frev[k], t, A)));
    chq(redc(fa, p, r) == subst(FP[k][i], t, Mod(A, p)), "reduction"))); }
test(k, n, d) = {
  for (i = 1, #PR, my(p = PR[i][1]); if (d % p == 0, next);
    my(v = subst(FP[k][i], t, Mod(n, p) / d)); if (v != 0 && kronecker(lift(v), p) == -1, return(0)));
  1;
}
testK(k, A) = {
  for (i = 1, #PR, my(p = PR[i][1], r = PR[i][2], ar = Mod(subst(A, b, r), p));
    my(v = subst(FP[k][i], t, ar)); if (v != 0 && kronecker(lift(v), p) == -1, return(0)));
  1;
}
FPsave = FP; FP = vector(2, k, vector(#PR, i, FPsave[k][i]^2));
{ my(bad = 0); for (d = 1, 30, for (n = -30, 30, if (gcd(n, d) != 1, next); if (!test(1, n, d) || !test(2, n, d), bad++)));
  chq(bad == 0, "KAT of the filter"); }
FP = FPsave;
printf("B. residue filter: %d degree one primes (p <= %d); known-answer test (fRev_k^2: every a survives): OK\n", #PR, PR[#PR][1]);
H = 1000;
{ for (k = 1, 2, my(surv = List(), cnt = 0);
    for (d = 1, H, for (n = -H, H, if (gcd(n, d) != 1, next); cnt++; if (test(k, n, d), listput(surv, n / d))));
    foreach (surv, A, my(fa = red(subst(frev[k], t, A))); if (#nfroots(nf, 'Y^2 - Mod(fa, K21)) > 0, print("   GLOBAL POINT: k = ", k - 1, ", a = ", A)));
    printf("   k = %d: %d rationals n/d (|n| <= %d, 1 <= d <= %d), survivors of the filter: %s\n", k - 1, cnt, H, H, Vec(surv)));
  for (k = 1, 2, my(surv = List(), cnt = 0);
    forvec (c = vector(4, i, [-3, 3]), if (c[2] == 0 && c[3] == 0 && c[4] == 0, next); cnt++;
      my(A = c[1] + c[2]*b + c[3]*b^2 + c[4]*b^3); if (testK(k, A), listput(surv, A)));
    foreach (surv, A, my(fa = red(subst(frev[k], t, A))); if (#nfroots(nf, 'Y^2 - Mod(fa, K21)) > 0, print("   GLOBAL POINT: k = ", k - 1, ", a = ", A)));
    printf("   k = %d: %d elements c0 + c1 theta + c2 theta^2 + c3 theta^3 (|ci| <= 3, not in Q), survivors: %s\n", k - 1, cnt, Vec(surv))); }
\\ ================= C =================
{ for (k = 1, 2, my(good = []);
    for (n = -12, 12, my(fa = red(subst(frev[k], t, n))); if (fa != 0 && nfislocalpower(nf, pr, fa, 2), good = concat(good, n)));
    printf("C. k = %d: integers a in [-12, 12] with fRev_k(a) a square in K_v: %s\n", k - 1, good)); }
{ my(cnt = [0, 0, 0, 0]);
  for (i0 = 0, 7, for (i1 = 0, 7, for (i2 = 0, 7,
    my(A = i0 + i1*PI + i2*PI^2, s = vector(2, k, my(fa = red(subst(frev[k], t, A))); fa != 0 && nfislocalpower(nf, pr, fa, 2)));
    cnt[1 + s[1] + 2*s[2]]++)));
  printf("   classes a = i0 + i1 PI + i2 PI^2 mod 8 (512): [neither, k = 0 only, k = 1 only, both] = %s\n", cnt);
  chq(cnt[4] == 0, "no common class"); }
\\ exhaustive version: split a0 + p^N O_v until the square class of each fRev_k is constant on the class
\\ (status: fRev(a) / fRev(a0) in 1 + p^7, a subset of the squares, for all a in the class, from the exact
\\ valuations of the Hasse derivatives at a0: N j + v(fRev^[j](a0)) >= v(fRev(a0)) + 7 for j = 1..6)
hasse(P) = { my(Q = subst(P, t, t + 'Y)); vector(poldegree(P, t), j, polcoef(Q, j, 'Y)); }
status(P, H, a0, N) = {
  my(v0 = vl(red(subst(P, t, a0))));
  if (v0 == oo, return(0));
  for (j = 1, #H, my(vj = vl(red(subst(H[j], t, a0)))); if (vj != oo && N * j + vj < v0 + 7, return(0)));
  if (v0 % 2, return(-1));
  if (nfislocalpower(nf, pr, red(subst(P, t, a0)), 2), 1, -1);
}
walk(P1, P2, c0, maxN) = {
  my(H1 = hasse(P1), H2 = hasse(P2), stack = List([c0]), both = List(), deep = List(), nodes = 0);
  while (#stack, my(c = stack[#stack], s1, s2); listpop(stack); nodes++;
    s1 = status(P1, H1, c[1], c[2]); s2 = status(P2, H2, c[1], c[2]);
    if (s1 == -1 || s2 == -1, next);
    if (s1 == 1 && s2 == 1, listput(both, c); next);
    if (c[2] >= maxN, listput(deep, c); next);
    listput(stack, [c[1], c[2] + 1]); listput(stack, [c[1] + PI^c[2], c[2] + 1]));
  [nodes, #both, #deep];
}
WK1 = walk(frev[1], frev[2], [0, 0], 30);
WK2 = walk(fk[1], fk[2], [0, 1], 30);
printf("   exhaustive split of O_v (a) and of p (s = 1/a, fRev_k(a) = a^6 f_k(s)): [classes visited, classes with both squares, undetermined at depth 30] = %s, %s\n", WK1, WK2);
chq(WK1[2] == 0 && WK1[3] == 0 && WK2[2] == 0 && WK2[3] == 0, "no common base abscissa in K_v");
\\ ================= D =================
\\ the Taylor data of sqrt(f) at 0 for f of degree <= 6 with f(0) != 0 (closed formulas, no square root)
tay(fc) = {
  my(f0 = fc[1], b1, b2, b3, R0, R1, R2);
  b1 = fc[2] / (2 * f0); b2 = (fc[3] / f0 - b1^2) / 2; b3 = (fc[4] / f0 - 2 * b1 * b2) / 2;
  R0 = fc[5] - f0 * (b2^2 + 2 * b1 * b3); R1 = fc[6] - f0 * (2 * b2 * b3); R2 = fc[7] - f0 * b3^2;
  [[b1, b2, b3], [R0, R1, R2]];
}
\\ square root of a residue triple modulo 2^n by search over units b0 (first coordinate odd), n <= 6
sqrtT(r, n) = { forvec (v = [[0, 2^n - 1], [0, 2^n - 1], [0, 2^n - 1]], if (v[1] % 2 == 1 && tmul(v, v, n) == tmod(r, n), return(v))); 0; }
N0f(g) = 64*g[1]^3*g[5] - 16*g[1]^2*g[3]^2 - 32*g[1]^2*g[2]*g[4] + 24*g[1]*g[2]^2*g[3] - 5*g[2]^4;
N2f(g) = 256*g[1]^5*g[7] - (8*g[1]^2*g[4] - 4*g[1]*g[2]*g[3] + g[2]^3)^2;
LEANPR = [[13, 11, 1], [23, 5, 4], [3, 2, 2]];   \\ (p, r, w) with w Dz = 1 mod p: ConcreteCheck.lean ck_Dz13, ck_Dz23, ck_Dz3
resp(L, p, r, w) = { my(c = comboL(L)); lift(Mod(w, p) * subst(Polrev(c, 'W), 'W, Mod(r, p))); }
lstr(v) = { my(s = "["); for (i = 1, #v, s = Str(s, v[i], if (i < #v, ", ", ""))); Str(s, "]") };
CASES = [[0, 0], [0, 2], [0, -2], [1, 1], [1, -1], [1, 3]];
DATA = vector(#CASES);
{ for (ci = 1, #CASES,
    my(k = CASES[ci][1], A = CASES[ci][2], fa, fc, T, g, gL, g0L, zr, vg0, m, n, b0, beta, lhs, N0, N2, N0L, N2L, rs);
    fa = red(subst(frev[k + 1], t, t + A));
    fc = vector(7, j, Mod(polcoef(fa, j - 1, t), K21));
    chq(fc[1] != 0, "f_a(0) != 0");
    T = tay(fc);
    \\ exact identity f_a - f_a(0) beta^2 = X^4 (R0 + R1 X + R2 X^2)
    beta = 1 + T[1][1] * t + T[1][2] * t^2 + T[1][3] * t^3;
    lhs = Mod(1, K21) * fa - fc[1] * beta^2 - t^4 * (T[2][1] + T[2][2] * t + T[2][3] * t^2);
    chq(lhs == 0, "Taylor identity");
    chq(T[2][1] != 0 && T[2][3] != 0, "genericity R0, R2 != 0");
    \\ g = 4 f_a: integral zk lists (Lean: FE k, i.e. FnData, shifted by the binomial expansion)
    gL = vector(7, j, sum(i = j - 1, 6, binomial(i, j - 1) * A^(i - j + 1) * FnD[k + 1][7 - i]));
    for (j = 1, 7, chq(zkr(gL[j]) == 4 * fc[j], "gL"));
    g = vector(7, j, zkr(gL[j]));
    g0L = gL[1];
    vg0 = vl(g[1]);
    chq(vg0 % 2 == 0, "even valuation of f_a(0)");
    chq(vg0 == 0 || vg0 == 6, "valuation 0 or 6 of 4 f_a(0)");
    m = if (vg0 == 0, 0, 1); n = 2 * m + 3;
    zr = resZK(g0L, 28);
    b0 = sqrtT(zr / 4^m, n - 2 * m);
    chq(b0 != 0, "residue square root");
    chq(tmod(tmul(2^m * b0, 2^m * b0, n) - tmod(zr, n), n) == [0, 0, 0], "Hensel residue certificate");
    chq(nfislocalpower(nf, pr, g[1], 2), "nfislocalpower");
    \\ numerators of R0, R2 (homogeneous in g): N0(g) = 4^7 f0^3 R0(f), N2(g) = 4^10 f0^5 R2(f)
    N0 = N0f(g); N2 = N2f(g);
    chq(N0 == 4^7 * fc[1]^3 * T[2][1], "N0 formula"); chq(N2 == 4^10 * fc[1]^5 * T[2][3], "N2 formula");
    N0L = zkl(N0); N2L = zkl(N2);
    rs = vector(#LEANPR, i, [resp(N0L, LEANPR[i][1], LEANPR[i][2], LEANPR[i][3]), resp(N2L, LEANPR[i][1], LEANPR[i][2], LEANPR[i][3])]);
    DATA[ci] = [k, A, T, gL, zr, m, n, b0, N0L, N2L, rs, vg0];
    printf("D. k = %d, a = %d: f_a(0) = fRev_k(%d), v(4 f_a(0)) = %d, square in K_v: yes\n", k, A, A, vg0);
    printf("   Hensel certificate: zres(g0L) mod 2^%d = %s, b0 = %s, (2^%d b0)^2 = zres mod 2^%d (so ||sigma(4 f_a(0)) - (2^%d evZ b0)^2|| <= 2^-%d < ||2^%d evZ b0||^2 = 2^-%d)\n",
      n, tmod(zr, n), b0, m, n, m, n, m + 1, 2 * m + 2);
    printf("   v(beta_1..3) = %s, v(R0, R1, R2) = %s, v(N0) = %d, v(N2) = %d\n", apply(vl, T[1]), apply(vl, T[2]), vl(N0), vl(N2));
    printf("   residues of N0, N2 at (p, theta - r) = (13, 11), (23, 5), (3, 2): %s\n", rs);
  ); }
\\ ================= E =================
FAC = factorpadic(K21, 2, 600);
g3 = [FAC[i, 1] | i <- [1 .. #FAC~], poldegree(FAC[i, 1]) == 3];
chq(#g3 == 1, "one cubic factor"); g3 = g3[1];
toKv(e) = Mod(subst(lift(Mod(e, K21)), b, 'b), g3);
vKv(x) = if (x == 0, oo, valuation(norm(x), 2));
chq(vKv(toKv(PI)) == 1, "PI uniformizer in Q_2[b]/(g3)");
\\ the root of the cubic factor is the image of theta under an embedding of the place pr (the only e = 3 place)
sqrtKv(c, y) = { for (i = 1, 12, y = y - (y^2 - c) / (2 * y)); y; }
{ for (ci = 1, #CASES,
    my(k = CASES[ci][1], A = CASES[ci][2], fa, fc, bb, V, q, y0, W);
    fa = red(subst(frev[k + 1], t, t + A));
    fc = vector(7, j, toKv(polcoef(fa, j - 1, t)));
    \\ initial approximation found here, independently of D: y0 = 2^m (i0 + i1 PI + i2 PI^2), v(y0^2 - 4 f_a(0)) > 2 v(2 y0)
    my(D = DATA[ci], m = D[6], P1 = toKv(PI), c4 = 4 * fc[1]);
    y0 = 0;
    forvec (v = [[0, 7], [0, 7], [0, 7]], my(yy = 2^m * (v[1] + v[2] * P1 + v[3] * P1^2)); if (v[1] % 2 == 1 && vKv(yy^2 - c4) > 2 * vKv(2 * yy), y0 = yy; break));
    chq(y0 != 0, "initial approximation in K_v");
    bb = sqrtKv(fc[1], y0 / 2);
    chq(vKv(bb^2 - fc[1]) >= 60, "b^2 = f_a(0) in K_v (p-adic precision)");
    V = vector(4); V[1] = bb; V[2] = fc[2] / (2 * bb); V[3] = (fc[3] - V[2]^2) / (2 * bb); V[4] = (fc[4] - 2 * V[2] * V[3]) / (2 * bb);
    q = [fc[5] - V[3]^2 - 2 * V[2] * V[4], fc[6] - 2 * V[3] * V[4], fc[7] - V[4]^2];
    chq(apply(vKv, q) == apply(vl, D[3][2]), "valuations of q_j = R_j (two implementations)");
    printf("E. k = %d, a = %d: v(b) = %d, v(V1, V2, V3) = %s, v(q0, q1, q2) = %s (agree with D)\n", k, A, vKv(bb), [vKv(V[2]), vKv(V[3]), vKv(V[4])], apply(vKv, q));
  ); }
\\ ================= F: the certificate data of the two chosen base points =================
\\ residues at the degree one prime (13, theta - 11) (Lean ConcreteCheck: ck_root13, ck_DB13, ck_Dz13 with w = 1):
\\ of g_j = 4 coeff_j(f_a) for j = 0..4, and N0 evaluated on these residues (the image of N0(g) under M1 resHom)
N0p(G) = 64*G[1]^3*G[5] - 16*G[1]^2*G[3]^2 - 32*G[1]^2*G[2]*G[4] + 24*G[1]*G[2]^2*G[3] - 5*G[2]^4;
{ foreach ([1, 4], ci, my(D = DATA[ci], G = vector(5, j, Mod(resp(D[4][j], 13, 11, 1), 13)));
    chq(G[1] != 0, "g0 nonzero at 13"); chq(N0p(G) != 0, "N0 nonzero at 13"); chq(lift(N0p(G)) == D[11][1][1], "N0 residue two ways");
    printf("F. k = %d, a = %d: residues of g_0..g_4 at (13, theta - 11): %s, N0 residue %d\n", D[1], D[2], apply(lift, G), lift(N0p(G)))); }
\\ ================= data for Lean =================
print("\nLean data (zk coordinates on nfinit(K21).zk, M1's zkE):");
{ for (ci = 1, #CASES, my(D = DATA[ci]);
    printf("k = %d, a = %d:\n  g0L (4 f_a(0)) = %s\n  b0 = %s, m = %d, n = %d, zres mod 2^n = %s\n", D[1], D[2], lstr(D[4][1]), D[8], D[6], D[7], tmod(D[5], D[7]));
    printf("  gL (4 * coefficients of f_a, degree 0..6) = %s\n", lstr(apply(lstr, D[4])));
    printf("  N0L = %s\n  N2L = %s\n", lstr(D[9]), lstr(D[10]));
    printf("  max |zk coordinate| of N0L, N2L: %.3e, %.3e\n", vecmax(apply(abs, D[9])), vecmax(apply(abs, D[10])));
  ); }
quit;
