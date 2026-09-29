\\ bruin_data.gp: writes lean/FurioLombardo/Discharge/M3a/DataBruin.lean (WP2 of the M3a discharge).
\\ All elements of K21 are given by their zk coordinates (PARI's integral basis, M1's `zkE`); every identity used in
\\ Lean is replayed here exactly in K21[t] and then rechecked by the Lean kernel (Kronecker test of M1).
\\ Data, for the twists k = 0, 1 (delta0 = d0, delta1 = d1 of code/earlier-computations/bruin_form.gp):
\\   QcData[i][j]   zk coordinates of the coefficient of Q_{i+1} on x^2, xy, xz, y^2, yz, z^2 (M1's QcZ);
\\   dData[k]       delta_k;
\\   FnData[k][j]   4 * coefficient of t^j of f_k = -delta_k det(M1 + 2t M2 + t^2 M3) (so f_k = F_k of bruin_form.gp);
\\   qData, hData   qDen * (coefficients 0, 1 of q) and hDen * (coefficients 0..3 of h), where
\\                  fRev = t^6 f(1/t) = lc(fRev) q h with q, h monic of degrees 2 and 4 (nffactor over K21);
\\   bezA, bezB, bezM   A R + B R' = bezM for R = 4 fRev (Bezout certificate of separability);
\\   dnData[k]      qDen^2 * disc(q) = (qDen q_1)^2 - 4 qDen (qDen q_0);
\\   betaData, betaDen, gamData, gamDen   beta = betaData / betaDen, gamma = gamData / gamDen with
\\                  beta^2 - disc(q) = fRev * gamma (beta = 2t + q_1 mod q, beta = e A'/B' mod h, CRT);
\\   (printed only; used literally in the Lean files) degree one primes (p, theta mod p) where 4 lc(fRev) and
\\                  qDen^2 disc(q) are non residues and 4 lc(f_k) is nonzero;
\\   liftData[i]    [r, s] with Q1(P_i) = delta r^2, Q2(P_i) = delta r s, Q3(P_i) = delta s^2 for the known points
\\                  P0 = (0:0:1), P1 = (1:1:1), P2 = (2:0:1), P3 = (-1:0:1) (twist 0 for P0, P2, twist 1 for P1, P3).
\\ Run from code/genus2-curves: gp -q bruin_data.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
LEANDIR = if (type(getenv("LEANOUT")) == "t_STR", getenv("LEANOUT"), "../../");  \\ LEANOUT=<dir>/ writes the Lean file under <dir> instead of lean/
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
den(v) = denominator(content(v));
red(g) = lift(Mod(1, K21) * g);
modp(g, m) = red(lift(Mod(Mod(1, K21) * g, Mod(1, K21) * m)));
invp(g, m) = red(lift(Mod(Mod(1, K21) * g, Mod(1, K21) * m)^(-1)));
pcoefs(g, n) = vector(n, i, polcoef(g, i - 1, t));
zkl(e) = { my(v = zkc(e)); if (den(v) != 1, error("non integral zk coordinates")); v~ };
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
M = vector(3, i, Msym(Qc[i]));
dd = [d0, d1];
DBr = polresultant(K21, K21');
resz(a, p, r) = { my(u = Mod(Dz, p)^(-1), s = Mod(0, p)); for (j = 1, 21, s += a[j] * subst(Pol(Vecrev(zkNum[j]), 'w), 'w, Mod(r, p))); lift(u * s) };
roots1(p) = if (DBr % p == 0 || Dz % p == 0, [], apply(e -> lift(e), polrootsmod(K21, p)));
firstp(a, test) = { forprime(p = 3, 10^4, foreach(roots1(p), r, if (test(resz(a, p, r), p), return([p, r])))); error("no prime"); };
isnr(v, p) = kronecker(v, p) == -1;
isnz(v, p) = v % p != 0;
lst3(V) = { my(s = "["); for (i = 1, #V, s = Str(s, lstl(V[i]), if (i < #V, ",\n  ", ""))); Str(s, "]") };
FnD = vector(2); qD = vector(2); hD = vector(2); qDn = vector(2); hDn = vector(2); bA = vector(2); bB = vector(2); bM = vector(2);
dnD = vector(2); beD = vector(2); beN = vector(2); gaD = vector(2); gaN = vector(2); rLc = vector(2); rD = vector(2); rF6 = vector(2);
{ for (k = 1, 2,
    my(f = red(-dd[k] * matdet(M[1] + 2*t*M[2] + t^2*M[3])), fr, fa, q, h, c, g, U, V, A0, B0, m, dq, dR, e, AR, BR, bh, bq, beta, gam);
    if (red(f - F0 * (k == 1) - F1 * (k == 2)) != 0, error("f_k vs F_k"));
    if (poldegree(f, t) != 6 || polcoef(f, 0, t) == 0, error("degree"));
    FnD[k] = vector(7, j, zkl(4 * polcoef(f, j - 1, t)));
    fr = polrecip(f); c = pollead(fr, t);
    fa = nffactor(nf, fr);
    if (#fa[, 1] != 2 || fa[1, 2] != 1 || fa[2, 2] != 1, error("factorization shape"));
    q = fa[1, 1]; h = fa[2, 1];
    if (poldegree(q, t) != 2 || poldegree(h, t) != 4 || pollead(q, t) != 1 || pollead(h, t) != 1, error("factor degrees"));
    if (red(fr - c * q * h) != 0, error("fRev = c q h"));
    qDn[k] = lcm(vector(2, j, den(zkc(polcoef(q, j - 1, t)))));
    hDn[k] = lcm(vector(4, j, den(zkc(polcoef(h, j - 1, t)))));
    qD[k] = vector(2, j, zkl(qDn[k] * polcoef(q, j - 1, t)));
    hD[k] = vector(4, j, zkl(hDn[k] * polcoef(h, j - 1, t)));
    \\ Bezout: U fr + V fr' = 1, then A = m U / 4, B = m V / 4 with A (4 fr) + B (4 fr)' = m
    g = gcdext(Mod(1, K21) * fr, Mod(1, K21) * deriv(fr, t));
    if (poldegree(lift(g[3]), t) != 0, error("gcd"));
    U = red(g[1] / g[3]); V = red(g[2] / g[3]);
    if (red(U * fr + V * deriv(fr, t) - 1) != 0, error("bezout"));
    A0 = red(U / 4); B0 = red(V / 4);
    m = lcm(concat(vector(poldegree(A0, t) + 1, j, den(zkc(polcoef(A0, j - 1, t)))), vector(poldegree(B0, t) + 1, j, den(zkc(polcoef(B0, j - 1, t))))));
    bM[k] = m;
    bA[k] = vector(poldegree(A0, t) + 1, j, zkl(m * polcoef(A0, j - 1, t)));
    bB[k] = vector(poldegree(B0, t) + 1, j, zkl(m * polcoef(B0, j - 1, t)));
    if (red(m * A0 * (4 * fr) + m * B0 * deriv(4 * fr, t) - m) != 0, error("scaled bezout"));
    \\ disc q, square root of disc q modulo fRev
    dq = red(polcoef(q, 1, t)^2 - 4 * polcoef(q, 0, t));
    if (#nfroots(nf, 'X^2 - dq) != 0, error("disc q is a square in K21"));
    dnD[k] = zkl(qDn[k]^2 * dq);
    my(R = RIN[k], cR = R[1], G1 = R[2], A = R[3], B = R[4]);
    dR = R[5];
    if (red(cR * G1 * (A^2 - dR * B^2) - f) != 0, error("RIN"));
    e = nfroots(nf, 'X^2 - red(dq / dR)); if (#e == 0, error("d / dR not a square"));
    AR = red(t^2 * subst(A, t, 1/t)); BR = red(t^2 * subst(B, t, 1/t));
    bh = modp(e[1] * AR * invp(BR, h), h);
    if (modp(bh^2 - dq, h) != 0, error("sqrt mod h"));
    bq = 2 * t + polcoef(q, 1, t);
    if (modp(bq^2 - dq, q) != 0, error("sqrt mod q"));
    beta = red(bq + q * modp((bh - bq) * invp(q, h), h));
    gam = red((beta^2 - dq) / fr);
    if (red(beta^2 - dq - fr * gam) != 0 || poldegree(beta, t) > 5, error("beta gamma"));
    beD[k] = lcm(vector(poldegree(beta, t) + 1, j, den(zkc(polcoef(beta, j - 1, t)))));
    gaD[k] = lcm(vector(poldegree(gam, t) + 1, j, den(zkc(polcoef(gam, j - 1, t)))));
    beN[k] = vector(poldegree(beta, t) + 1, j, zkl(beD[k] * polcoef(beta, j - 1, t)));
    gaN[k] = vector(poldegree(gam, t) + 1, j, zkl(gaD[k] * polcoef(gam, j - 1, t)));
    \\ residue primes
    rLc[k] = firstp(FnD[k][1], isnr);
    rD[k] = firstp(dnD[k], isnr);
    rF6[k] = firstp(FnD[k][7], isnz);
    printf("k = %d: F_k ok, fRev = c q h ok (qDen %d, hDen %d), Bezout ok (bezM %d digits, deg A %d, deg B %d), disc q non square, beta ok (betaDen %d digits, gamDen %d digits, deg beta %d, deg gamma %d)\n",
      k - 1, qDn[k], hDn[k], #Str(bM[k]), #bA[k] - 1, #bB[k] - 1, #Str(beD[k]), #Str(gaD[k]), #beN[k] - 1, #gaN[k] - 1);
    printf("  residue primes: 4 lc %s, qDen^2 disc %s, 4 lc(f_k) nonzero %s\n", rLc[k], rD[k], rF6[k]);
  );
}
\\ known lifts
Pts = [[0, 0, 1], [1, 1, 1], [2, 0, 1], [-1, 0, 1]];
Ev(Q, P) = red(substvec(Q, [x, y, z], P));
LD = vector(4);
{ for (i = 1, 4,
    my(P = Pts[i], k = if (i == 1 || i == 3, 1, 2), dl = dd[k], v = vector(3, j, Ev(Qs[j], P)), r, s);
    if (substvec(F, [x, y, z], P) != 0, error("point"));
    if (v[1] != 0,
      r = nfroots(nf, 'X^2 - red(v[1] / dl)); if (#r == 0, error("Q1 / delta not a square")); r = r[1]; s = red(v[2] / (dl * r)),
      r = 0; s = nfroots(nf, 'X^2 - red(v[3] / dl)); if (#s == 0, error("Q3 / delta not a square")); s = s[1]);
    if (red(v[1] - dl * r^2) != 0 || red(v[2] - dl * r * s) != 0 || red(v[3] - dl * s^2) != 0, error("lift equations"));
    LD[i] = [zkl(r), zkl(s)];
    printf("P%d = %s (twist %d): Q_i(P) zero: %s; lift ok\n", i - 1, P, k - 1, apply(e -> e == 0, v));
  );
}
out = Str(LEANDIR, "FurioLombardo/Discharge/M3a/DataBruin.lean");
system(Str("rm -f ", out));
write(out, "/-! Data of WP2 of the M3a discharge (generated by code/genus2-curves/bruin_data.gp, PARI/GP). Every\nelement of K21 is a list of zk coordinates (lane M1's `zkE`). Every identity between these data is rechecked by the\nLean kernel in `FurioLombardo.Discharge.M3a.Concrete`; see the generator for the meaning of each list. -/\n\nnamespace FurioLombardo.Discharge.M3a.Bruin\n\nset_option maxRecDepth 100000\n");
write(out, "/-- `QcData[i][j]`: coefficient of `Q_(i+1)` on `x^2, xy, xz, y^2, yz, z^2` (lane M1's `QcZ`). -/\ndef QcData : List (List (List Int)) :=\n  ", lst3(vector(3, i, vector(6, j, QcZ[i][j]~))), "\n");
write(out, "/-- `δ0`, `δ1` (`d0`, `d1` of bruin_form.gp). -/\ndef dData : List (List Int) :=\n  ", lstl([zkl(d0), zkl(d1)]), "\n");
write(out, "/-- `FnData[k][j]`: 4 times the coefficient of `t^j` of `f_k = -δ_k det(M1 + 2t M2 + t^2 M3)`. -/\ndef FnData : List (List (List Int)) :=\n  ", lst3(FnD), "\n");
write(out, "/-- Denominators of the monic factors `q`, `h` of the reversed sextic. -/\ndef qDen : List Nat := ", lst(qDn), "\n\ndef hDen : List Nat := ", lst(hDn), "\n");
write(out, "/-- `qData[k]`: `qDen * q_0, qDen * q_1` (`q = X^2 + q_1 X + q_0`). -/\ndef qData : List (List (List Int)) :=\n  ", lst3(qD), "\n");
write(out, "/-- `hData[k]`: `hDen * h_0, ..., hDen * h_3` (`h = X^4 + h_3 X^3 + ... + h_0`). -/\ndef hData : List (List (List Int)) :=\n  ", lst3(hD), "\n");
write(out, "/-- Bezout certificate `A R + B R' = bezM` for `R = 4 fRev`. -/\ndef bezM : List Int := ", lst(bM), "\n\ndef bezA : List (List (List Int)) :=\n  ", lst3(bA), "\n\ndef bezB : List (List (List Int)) :=\n  ", lst3(bB), "\n");
write(out, "/-- `qDen^2 disc(q)`. -/\ndef dnData : List (List Int) :=\n  ", lstl(dnD), "\n");
write(out, "/-- `β = betaData / betaDen`, `γ = gamData / gamDen`, `β^2 - disc(q) = fRev γ`. -/\ndef betaDen : List Nat := ", lst(beD), "\n\ndef gamDen : List Nat := ", lst(gaD), "\n\ndef betaData : List (List (List Int)) :=\n  ", lst3(beN), "\n\ndef gamData : List (List (List Int)) :=\n  ", lst3(gaN), "\n");
write(out, "/-- `liftData[i] = [r, s]` for the known point `P_i`. -/\ndef liftData : List (List (List Int)) :=\n  ", lst3(LD), "\n");
write(out, "end FurioLombardo.Discharge.M3a.Bruin");
print("written ", out);
quit;
