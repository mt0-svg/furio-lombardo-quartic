\\ schaefer_certs.gp: certificates of the global Schaefer lemma for fRev k (the
\\ "Global statement"; Lean: lean/FurioLombardo/Discharge/SelmerBasis/SchaeferModel.lean, schaefer_global_of_certs
\\ with D = 14). Every element of K21 is a list of zk coordinates (M1's zkE); all data below are integral.
\\   pi      a generator of pr3 pr439 (norm +-1317), piInv = 1317 / pi (integral), aT = -469;
\\   m1, F   F = m1 f1 with f1 = fRev(aT + pi t) / pi^6, m1 a power of 2 times a power of 7 (F integral);
\\   A, B, e1, e  A F + B F' = e1 F_6 (A = Res(F, F') U, B = Res(F, F') V with U F + V F' = 1, e1 = Res / F_6),
\\           e1 e = 14^N;
\\   for i = 0, 1, 2: F2 = t^6 F(i + 1/t) (= m1 f2), A2 F2 + B2 F2' = R2 (A2 = R2 U2, B2 = R2 V2, R2 = Res(F2, F2')),
\\           y m1 F_6 + z F(i) R2 = 14^N m1^2.
\\ Lean reading: f1 = pQ m1 F, A1 = pK A, B1 = pK B, so A1 f1 + B1 f1' = C (e1 lc f1); f2 = pQ m1 F2, A2 = pK A2,
\\ B2 = pK B2, r2 = R2 / m1, so A2 f2 + B2 f2' = C r2 and y lc f1 + z f1(i) r2 = 14^N.
\\ Output: the Lean data file lean/FurioLombardo/Discharge/SelmerBasis/SchaeferCertData.lean and a size report.
\\ Run from code/selmer-global-bound:
\\   gp -q -D parisizemax=1400000000 -D nbthreads=1 schaefer_certs.gp > schaefer_certs.out (LEANOUT=<dir>/
\\   writes SchaeferCertData.lean to <dir> instead)
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
NCHK = 0; NFAIL = 0;
chk(c, msg) = { NCHK++; if (!c, NFAIL++; print("FAIL: ", msg)); };
o = Mod(1, K21);
red(g) = lift(o * g);
den(v) = denominator(content(v));
zkl(e) = { my(v = zkc(e)); if (den(v) != 1, error("non integral zk coordinates")); v~ };
maxbits(v) = vecmax(apply(c -> if (c == 0, 0, exponent(c) + 1), v));
pbits(P) = vecmax(vector(poldegree(P, t) + 1, j, maxbits(zkl(polcoef(P, j - 1, t)))));
ok27(n) = n == 2^valuation(n, 2) * 7^valuation(n, 7);
pr3 = 0; pr439 = 0;
\\ pi: an element of norm +-1317 among small elements of pr3 pr439 (LLL on T2), chosen once for both twists
T0 = getabstime();
{
  my(dfr = red(poldisc(o * polrecip(F0))));
  foreach(idealprimedec(nf, 3), pr, if (idealval(nf, dfr, pr) > 0, pr3 = pr));
  foreach(idealprimedec(nf, 439), pr, if (idealval(nf, dfr, pr) > 0, pr439 = pr));
  chk(pr3 != 0 && pr439 != 0 && pr3.f == 1 && pr439.f == 1, "bad primes above 3 and 439 of degree 1");
}
Ipi = idealmul(nf, pr3, pr439);
piT = 0;
\\ first try: short elements of the ideal (LLL for T2); else a generator from bnfisprincipal
{
  my(H = idealhnf(nf, Ipi), L, best = 0, bs = 10^100);
  L = H * qflll(H~ * nf.t2 * H);
  for (j = 1, 21, my(g = L[, j], n = norm(o * nfbasistoalg(nf, g)));
    if (abs(n) == 1317 && maxbits(g~) < bs, best = g; bs = maxbits(g~)));
  if (best == 0,
    my(bnf = bnfinit(K21, 1), r = bnfisprincipal(bnf, Ipi, 1 + 4));
    if (r[1] != 0, error("pr3 pr439 not principal"));
    best = zkc(nfbasistoalg(nf, nffactorback(nf, r[2]))));
  piT = red(nfbasistoalg(nf, best));
}
chk(idealval(nf, piT, pr3) == 1 && idealval(nf, piT, pr439) == 1 && abs(norm(o * piT)) == 1317, "pi generates pr3 pr439");
piInv = red(1317 / piT);
chk(den(zkc(piInv)) == 1, "1317 / pi integral");
printf("pi: zk coordinates %s (max %d bits), norm %d; %d s\n", zkl(piT), maxbits(zkl(piT)), norm(o * piT), (getabstime() - T0) \ 1000);
aT = -469;
chk(aT % 3 == 2 && (aT + 30) % 439 == 0, "aT = -1 mod 3, = -30 mod 439");
NN = 0;  \\ exponent of 14, the largest needed over both twists
Dat = vector(2);
{ for (k = 1, 2,
    my(T1 = getabstime(), fr = polrecip(if (k == 1, F0, F1)), f1, m1, F, Fd, g, U, V, ResF, A, B, e1, lcF, dq, Fi = vector(3), F2 = vector(3), A2 = vector(3), B2 = vector(3), R2 = vector(3), N1);
    chk(poldegree(fr, t) == 6, "deg fRev");
    f1 = red(subst(fr, t, aT + piT * t) / piT^6);
    m1 = lcm(vector(7, j, den(zkc(polcoef(f1, j - 1, t)))));
    chk(ok27(m1), "m1 supported on 2, 7");
    F = red(m1 * f1);
    chk(red(pollead(f1, t) - pollead(fr, t)) == 0, "lc f1 = lc fRev");
    Fd = deriv(F, t);
    g = gcdext(o * F, o * Fd);
    chk(poldegree(lift(g[3]), t) == 0, "F separable");
    U = red(g[1] / g[3]); V = red(g[2] / g[3]);
    ResF = red(polresultant(o * F, o * Fd, t));
    A = red(ResF * U); B = red(ResF * V);
    lcF = polcoef(F, 6, t);
    e1 = red(ResF / lcF);
    chk(red(A * F + B * Fd - e1 * lcF) == 0, "A F + B F' = e1 F_6");
    chk(vecmax(vector(poldegree(A, t) + 1, j, den(zkc(polcoef(A, j - 1, t))))) == 1 && vecmax(vector(poldegree(B, t) + 1, j, den(zkc(polcoef(B, j - 1, t))))) == 1 && den(zkc(e1)) == 1, "A, B, e1 integral");
    \\ e1 supported on 2 and 7: N(e1) = +-2^x 7^y
    dq = factor(abs(norm(o * e1)))[, 1]~;
    chk(#setminus(Set(dq), [2, 7]) == 0, "e1 supported on 2, 7");
    N1 = 0; while (den(zkc(red(14^N1 / e1))) != 1, N1++);
    for (i = 0, 2,
      Fi[i + 1] = red(subst(F, t, i));
      F2[i + 1] = red(polrecip(subst(F, t, t + i)));
      chk(poldegree(F2[i + 1], t) == 6 && red(polcoef(F2[i + 1], 6, t) - Fi[i + 1]) == 0, "F2 degree 6, lc F2 = F(i)");
      my(G = F2[i + 1], Gd = deriv(G, t), h = gcdext(o * G, o * Gd), U2, V2);
      chk(poldegree(lift(h[3]), t) == 0, "F2 separable");
      U2 = red(h[1] / h[3]); V2 = red(h[2] / h[3]);
      R2[i + 1] = red(polresultant(o * G, o * Gd, t));
      A2[i + 1] = red(R2[i + 1] * U2); B2[i + 1] = red(R2[i + 1] * V2);
      chk(red(A2[i + 1] * G + B2[i + 1] * Gd - R2[i + 1]) == 0, "A2 F2 + B2 F2' = R2");
      chk(vecmax(vector(poldegree(A2[i + 1], t) + 1, j, den(zkc(polcoef(A2[i + 1], j - 1, t))))) == 1 && vecmax(vector(poldegree(B2[i + 1], t) + 1, j, den(zkc(polcoef(B2[i + 1], j - 1, t))))) == 1, "A2, B2 integral"));
    Dat[k] = [m1, F, A, B, e1, N1, Fi, F2, A2, B2, R2, lcF];
    NN = max(NN, N1);
    printf("twist %d: m1 = %s, F %d bits, A %d bits (deg %d), B %d bits (deg %d), e1 %d bits, N(e1) = %s, N1 = %d; %d s\n", k - 1, factor(m1), pbits(F), pbits(A), poldegree(A, t), pbits(B), poldegree(B, t), maxbits(zkl(e1)), factor(abs(norm(o * e1))), N1, (getabstime() - T1) \ 1000);
    for (i = 0, 2, printf("  i = %d: F2 %d bits, A2 %d bits (deg %d), B2 %d bits (deg %d), R2 %d bits\n", i, pbits(F2[i + 1]), pbits(A2[i + 1]), poldegree(A2[i + 1], t), pbits(B2[i + 1]), poldegree(B2[i + 1], t), maxbits(zkl(R2[i + 1]))));
  );
}
\\ y, z with y (m1 F_6) + z (F(i) R2) = 14^N m1^2: the ideal (m1 F_6) + (F(i) R2) contains a power of 14
\\ (lc F is a non unit only at the primes above 23 and at 2, 7, and F(i) R2 is a unit at the primes above 23)
mulmat(x) = { my(v = zkc(x)); matconcat(vector(21, j, zv(nfeltmul(nf, v, vectorv(21, l, l == j))))); };
solveyz(a, b, T) = {
  my(M = matconcat([mulmat(a), mulmat(b)]), H, Uh, s, tv = zkc(T), x);
  [H, Uh] = mathnf(M, 1);
  s = matsolve(H, tv);
  if (denominator(s) != 1, return(0));
  x = Uh * concat(vectorv(#Uh - #H, j, 0), s);
  \\ (y + t b, z - t a) is again a solution: reduce z modulo the ideal (a), then y = (T - z b) / a
  my(zz = nfeltreduce(nf, x[22..42], idealhnf(nf, a)), yy = red((T - nfbasistoalg(nf, zz) * b) / a));
  if (den(zkc(yy)) != 1, error("y not integral after the reduction"));
  [yy, red(nfbasistoalg(nf, zz))];
}
YZ = vector(2, k, vector(3));
{ for (k = 1, 2,
    my(D = Dat[k], m1 = D[1], lcF = D[12], N2 = NN, r);
    for (i = 0, 2,
      my(a = red(m1 * lcF), b = red(D[7][i + 1] * D[11][i + 1]));
      r = 0;
      while (r == 0, r = solveyz(a, b, red(14^N2 * m1^2)); if (r == 0, N2++; if (N2 > NN + 60, error("no y, z"))));
      NN = max(NN, N2);
      YZ[k][i + 1] = r;
      chk(red(r[1] * a + r[2] * b - 14^N2 * m1^2) == 0, "y, z identity");
      printf("twist %d, i = %d: y %d bits, z %d bits, exponent %d\n", k - 1, i, maxbits(zkl(r[1])), maxbits(zkl(r[2])), N2)));
}
\\ one exponent for everything: redo y, z at the final NN (14^(NN - N2) times the solution)
{ for (k = 1, 2, for (i = 1, 3,
    my(D = Dat[k], m1 = D[1], a = red(m1 * D[12]), b = red(D[7][i] * D[11][i]), r = solveyz(a, b, red(14^NN * m1^2)));
    chk(r != 0, "y, z at the final exponent");
    YZ[k][i] = r;
    chk(red(r[1] * a + r[2] * b - 14^NN * m1^2) == 0, "y, z identity at NN")));
}
Ee = vector(2, k, red(14^NN / Dat[k][5]));
for (k = 1, 2, chk(den(zkc(Ee[k])) == 1 && red(Ee[k] * Dat[k][5] - 14^NN) == 0, "e integral, e1 e = 14^NN"); chk(NN >= valuation(Dat[k][1], 2) && NN >= valuation(Dat[k][1], 7), "m1 divides 14^NN"));
printf("exponent N = %d\n", NN);
\\ Lean output
pl(P, n) = vector(n, j, zkl(polcoef(P, j - 1, t)));
lst3(V) = { my(s = "["); for (i = 1, #V, s = Str(s, lstl(V[i]), if (i < #V, ",\n  ", ""))); Str(s, "]") };
lst4(V) = { my(s = "["); for (i = 1, #V, s = Str(s, lst3(V[i]), if (i < #V, ",\n  ", ""))); Str(s, "]") };
out = Str(if (#getenv("LEANOUT"), getenv("LEANOUT"), "../../FurioLombardo/Discharge/SelmerBasis/"), "SchaeferCertData.lean");
system(Str("rm -f ", out));
write(out, "/-! Certificates of the global Schaefer lemma for `fRev k` (generated by code/selmer-global-bound/schaefer_certs.gp,\nPARI/GP). Every element of K21 is a list of zk coordinates (lane M1's `zkE`); see the generator for the meaning of each\nlist. The identities are rechecked by the Lean kernel in SchaeferCertCheck.lean. -/\n\nnamespace FurioLombardo.Discharge.SelmerBasis.Cert\n\nset_option maxRecDepth 100000\n");
write(out, "/-- `π`, a generator of `pr3 pr439`, and `1317 / π`. -/\ndef piL : List Int := ", lst(zkl(piT)), "\n\ndef piInvL : List Int := ", lst(zkl(piInv)), "\n");
write(out, "/-- The exponent `N` of `14`. -/\ndef expN : Nat := ", NN, "\n");
write(out, "/-- `m1` with `F = m1 f1`. -/\ndef m1Data : List Nat := ", lst([Dat[1][1], Dat[2][1]]), "\n");
write(out, "/-- `F = m1 f1`, coefficients 0 to 6. -/\ndef FData : List (List (List Int)) :=\n  ", lst3(vector(2, k, pl(Dat[k][2], 7))), "\n");
write(out, "/-- `A` of `A F + B F' = e1 F_6`. -/\ndef AData : List (List (List Int)) :=\n  ", lst3(vector(2, k, pl(Dat[k][3], poldegree(Dat[k][3], t) + 1))), "\n");
write(out, "/-- `B` of `A F + B F' = e1 F_6`. -/\ndef BData : List (List (List Int)) :=\n  ", lst3(vector(2, k, pl(Dat[k][4], poldegree(Dat[k][4], t) + 1))), "\n");
write(out, "/-- `e1` and `e` with `e1 e = 14 ^ N`. -/\ndef e1Data : List (List Int) :=\n  ", lstl(vector(2, k, zkl(Dat[k][5]))), "\n\ndef eData : List (List Int) :=\n  ", lstl(vector(2, k, zkl(Ee[k]))), "\n");
write(out, "/-- `F2 = t^6 F(i + 1/t)` for `i = 0, 1, 2`. -/\ndef F2Data : List (List (List (List Int))) :=\n  ", lst4(vector(2, k, vector(3, i, pl(Dat[k][8][i], 7)))), "\n");
write(out, "/-- `A2` of `A2 F2 + B2 F2' = R2`. -/\ndef A2Data : List (List (List (List Int))) :=\n  ", lst4(vector(2, k, vector(3, i, pl(Dat[k][9][i], poldegree(Dat[k][9][i], t) + 1)))), "\n");
write(out, "/-- `B2` of `A2 F2 + B2 F2' = R2`. -/\ndef B2Data : List (List (List (List Int))) :=\n  ", lst4(vector(2, k, vector(3, i, pl(Dat[k][10][i], poldegree(Dat[k][10][i], t) + 1)))), "\n");
write(out, "/-- `R2 = Res(F2, F2')`. -/\ndef R2Data : List (List (List Int)) :=\n  ", lst3(vector(2, k, vector(3, i, zkl(Dat[k][11][i])))), "\n");
write(out, "/-- `y`, `z` with `y m1 F_6 + z F(i) R2 = 14 ^ N m1 ^ 2`. -/\ndef yData : List (List (List Int)) :=\n  ", lst3(vector(2, k, vector(3, i, zkl(YZ[k][i][1])))), "\n\ndef zData : List (List (List Int)) :=\n  ", lst3(vector(2, k, vector(3, i, zkl(YZ[k][i][2])))), "\n");
write(out, "end FurioLombardo.Discharge.SelmerBasis.Cert");
printf("written %s\n", out);
printf("checks %d, failures %d; total %d s\n", NCHK, NFAIL, (getabstime() - T0) \ 1000);
print(if (NFAIL == 0, "RESULT PASS", "RESULT FAIL"));
quit;
