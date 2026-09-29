\\ local_facts_v_data.gp: writes lean/FurioLombardo/Discharge/M3a/LocalData.lean (WP5 of the M3a discharge: the local facts
\\ (irr) and (nsq) at the place v above 2 with e = 3, for sigma = M4Cert.sigma : K21 -> K_v = Q_2[X]/(E)).
\\ For the twists k = 0, 1 (q, h, c, d = disc q as in bruin_data.gp):
\\   A = X^2 + a1 X + a0, B = b1 X + b0 over K21 with h = A^2 - d B^2 (resolvent cubic, as local_facts_v_biquadratic.gp);
\\   abData[k] = zk coordinates of ma a0, ma a1, mb b0, mb b1 (maDen, mbDen);
\\   in N = K_v(w), w^2 = d: D = (a1 + b1 w)^2 - 4 (a0 + b0 w) = D0 + D1 w (discriminant of A + w B) and
\\   rho = p0^2 - p0 p1 P1 + p1^2 P0 = r0 + r1 w (P1 = a1 + b1 w, P0 = a0 + b0 w, p_i = q_i - P_i: rho = Res(q, A + w B));
\\   zData[k] = zk coordinates of m D0, m D1, m N(D), m r0, m r1, m N(rho) (N(z) = z0^2 - d z1^2), zDen[k] the m;
\\   the square root certificates: for z in {D, rho}, a triple b with b^2 = N(z) mod 2^M in Z[pi]/(E) (Hensel), the
\\   precisions M, r, P and the scalings (i, j) of the two tests (z0 +- n)/2 * (pi^i / 2^j)^2 modulo 8;
\\   dTest[k]: the scaling of the test "sigma(d) is not a square".
\\ Every certificate condition is replayed here with the exact integer arithmetic of the Lean checks
\\ (M4Cert's zres, mulZ, modT; the kernel recomputes all of it in LocalCheck.lean), and the square classes are also
\\ recomputed p-adically (sigma(theta) = theta* to 2^240, independent of the triple arithmetic).
\\ Run from code/genus2-curves: gp -q local_facts_v_data.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
LEANDIR = if (type(getenv("LEANOUT")) == "t_STR", getenv("LEANOUT"), "../../");  \\ LEANOUT=<dir>/ writes the Lean file under <dir> instead of lean/
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
chq(c, msg) = if (!c, error("check failed: ", msg));
red(g) = lift(Mod(1, K21) * g);
pr = [P | P <- idealprimedec(nf, 2), P.e == 3][1];
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
dd = [d0, d1];
lsq(a) = nfislocalpower(nf, pr, lift(Mod(a, K21)), 2);
gsq(a) = #nfroots(nf, 'y^2 - lift(Mod(a, K21))) > 0;
gsqrt(a) = nfroots(nf, 'y^2 - lift(Mod(a, K21)))[1];
vl(a) = if (a == 0, oo, nfeltval(nf, a, pr));
den(v) = denominator(content(v));
zkl(e) = { my(v = zkc(e)); chq(den(v) == 1, "non integral zk coordinates"); v~ };
chq(Dz == 168168978404922092768, "Dz of M1");
\\ ---------------------------------------------------------------- exact triple arithmetic (as M4Cert)
E0 = 17325639337422721302482; E1 = 16418729904282180494548; E2 = 37469486047374096441064;
mulZ(a, c) = { my(c0 = a[1]*c[1], c1 = a[1]*c[2] + a[2]*c[1], c2 = a[1]*c[3] + a[2]*c[2] + a[3]*c[1],
  c3 = a[2]*c[3] + a[3]*c[2], c4 = a[3]*c[3], d3 = c3 - E2*c4);
  [c0 - E0*d3, c1 - E1*d3 - E0*c4, c2 - E2*d3 - E1*c4] };
hornerZ(v, L) = { my(r = [0, 0, 0]); forstep (i = #L, 1, -1, r = [L[i], 0, 0] + mulZ(v, r)); r };
th0 = [163180991353, 3522151726, 560510631928];
combo(l) = vector(21, i, sum(j = 1, 21, l[j] * zkNum[j][i]));
uOdd = 91745367; Dodd = 5255280575153815399; chq(Dz == 32 * Dodd, "Dodd");
zresOK(l) = { my(N = hornerZ(th0, combo(l))); N[1] % 32 == 0 && N[2] % 32 == 0 && N[3] % 32 == 0 };
zres(l) = mulZ(hornerZ(th0, combo(l)) / 32, [uOdd, 0, 0]);
modT(v, n) = vector(3, i, v[i] % 2^n);
dvdT(v, m) = v[1] % m == 0 && v[2] % m == 0 && v[3] % m == 0;
pvT(k) = { my(v = [1, 0, 0]); for (i = 1, k, v = mulZ(v, [0, 1, 0])); v };
SQ = Map(); forvec (s = vector(3, i, [0, 7]), mapput(SQ, modT(mulZ(s, s), 3), 1));
chq(#SQ == 28, "28 squares modulo 8");
\\ residue of sigma(zkE l / (2^j o)) modulo 2^P, as Lean's sQres
sQok(l, j, o, oi, P) = zresOK(l) && P + j <= 28 && P >= 1 && dvdT(modT(zres(l), P + j), 2^j) && modT(mulZ([o, 0, 0], [oi, 0, 0]), P) == [1, 0, 0];
sQres(l, j, oi, P) = mulZ(modT(zres(l), P + j) / 2^j, [oi, 0, 0]);
\\ Lean's sqTest: x ~ t mod 2^P gives "x / 2^e not a square" when x pi^(2i) / 2^(2j+e) mod 8 is not a square residue
sqTest(t, i, j, e, P) = { my(u = modT(mulZ(modT(t, P), pvT(2 * i)), P));
  dvdT(u, 2^(2*j + e)) && 2*j + e + 3 <= P && !mapisdefined(SQ, modT(u / 2^(2*j + e), 3)) };
lowOK(b, s) = b[1] % 2^(s + 1) != 0 || b[2] % 2^(s + 1) != 0 || b[3] % 2^(s + 1) != 0;
\\ ---------------------------------------------------------------- p-adic K_v (independent check)
PR = 240;
EE = 'X^3 + E2*'X^2 + E1*'X + E0;
pa(c) = c + O(2^PR);
kv(v) = Mod(pa(v[1]) + pa(v[2])*'X + pa(v[3])*'X^2, EE);
cfk(e, i) = polcoef(lift(e), i, 'X);
v2(c) = if (c == 0, 10^6, valuation(c, 2));
vpi(e) = min(3 * v2(cfk(e, 0)), min(3 * v2(cfk(e, 1)) + 1, 3 * v2(cfk(e, 2)) + 2));
fK = Pol(Vec(K21), 'X);
th = kv(th0);
for (i = 1, 12, th = th - subst(fK, 'X, th) / subst(deriv(fK, 'X), 'X, th));
chq(vpi(subst(fK, 'X, th)) > 600, "theta*");
chq(vpi(th - kv(th0)) >= 99, "theta* close to theta0");
sg(a) = subst(Pol(lift(Mod(a, K21)), 'b), 'b, th);
PIK = Mod('X, EE);
usq(u) = { forvec(s = [[0, 3], [0, 3], [0, 3]], my(e = u - kv(s)^2); if (e == 0 || vpi(e) >= 7, return(1))); 0 };
ksq(w) = { if (w == 0, return(1)); my(v = vpi(w)); if (v % 2, return(0)); usq(w / PIK^v) };
ksqrt(w) = { my(v = vpi(w), u, s = 0); chq(v % 2 == 0, "odd valuation"); u = w / PIK^v;
  forvec(t = [[0, 3], [0, 3], [0, 3]], my(e = u - kv(t)^2); if (e == 0 || vpi(e) >= 7, s = kv(t); break));
  chq(s != 0, "unit not a square");
  for (i = 1, 12, s = (s + u / s) / 2); PIK^(v / 2) * s };
\\ integer triple of a p-adic element of O_v modulo 2^M
trip(e, M) = { chq(vpi(e) >= 0, "integral"); vector(3, i, lift(Mod(truncate(cfk(e, i - 1)), 2^M))) };
\\ ---------------------------------------------------------------- the data
scal(v) = { for (j = 0, 6, for (i = 0, 2, if (v + 2*i - 6*j == 0 || v + 2*i - 6*j == 2, return([i, j])))); error("scaling") };
splitm(m) = { my(j = valuation(m, 2)); [j, m / 2^j] };
oinv(o) = lift(Mod(1, 2^28) / o);
\\ certificate of "z = z0 + z1 w is not a square in N": returns [b, M, r, P, ip, jp, im, jm]
zcert(name, z0, z1, dq) = {
  my(Nz = red(z0^2 - dq * z1^2), n, Z0 = sg(z0), p, m, vp, vm, b, s, r, M, P, l0, lN, m0, mN, j0, o0, jN, oN, t0, tN);
  chq(z1 != 0, "z1 != 0");
  chq(lsq(Nz), "N(z) square at v"); chq(!gsq(Nz), "N(z) not a global square (as expected)");
  n = ksqrt(sg(Nz)); chq(vpi(n^2 - sg(Nz)) > 600, "n^2 = N(z)");
  p = (Z0 + n) / 2; m = (Z0 - n) / 2;
  chq(!ksq(p) && !ksq(m), "both (z0 +- n)/2 non-squares");
  chq(lsq(z0) == ksq(Z0), "square test agrees with nfislocalpower on z0");
  vp = vpi(p); vm = vpi(m);
  \\ scaling (i, j) with v + 2i - 6j in {0, 2} (the mod 8 test is complete for valuations 0 and 2)
  my(scp = scal(vp), scm = scal(vm));
  \\ Hensel: b = n mod 2^M; r = s + 3 with s the 2-adic valuation of the first coordinate of b not divisible by 2^(s+1)
  s = min(v2(cfk(n, 0)), min(v2(cfk(n, 1)), v2(cfk(n, 2))));
  r = s + 3;
  P = max(2 * scp[2] + 4, 2 * scm[2] + 4);
  M = max(P + r, 2 * r + 1);
  b = trip(n, M);
  chq(lowOK(b, s), "lowOK");
  l0 = zkl(den(zkc(z0)) * z0); m0 = den(zkc(z0)); lN = zkl(den(zkc(Nz)) * Nz); mN = den(zkc(Nz));
  [j0, o0] = splitm(m0); [jN, oN] = splitm(mN);
  chq(sQok(l0, j0, o0, oinv(o0), P), "sQok z0"); chq(sQok(lN, jN, oN, oinv(oN), M), "sQok N");
  t0 = sQres(l0, j0, oinv(o0), P); tN = sQres(lN, jN, oinv(oN), M);
  chq(modT(t0, P) == trip(Z0, P), "t0 agrees with the p-adic sigma(z0)");
  chq(modT(tN, M) == trip(sg(Nz), M), "tN agrees with the p-adic sigma(N)");
  chq(modT(mulZ(b, b), M) == modT(tN, M), "b^2 = N mod 2^M");
  chq(r >= 3 && 2 * r < M && P + r <= M, "precisions");
  chq(sqTest(t0 + b, scp[1], scp[2], 1, P), "test (z0 + n)/2");
  chq(sqTest(t0 - b, scm[1], scm[2], 1, P), "test (z0 - n)/2");
  printf("  %s: v(z0) = %d, v(z1) = %d, v(N) = %d, v(n) = %d; v((z0+n)/2) = %d scaled by %s, v((z0-n)/2) = %d scaled by %s; b = %s, M = %d, r = %d, P = %d; denominators z0 %d, N %d\n",
    name, vl(z0), vl(z1), vl(Nz), vpi(n), vp, scp, vm, scm, b, M, r, P, m0, mN);
  [b, M, r, P, scp[1], scp[2], scm[1], scm[2]]
};
AB = vector(2); MA = vector(2); MB = vector(2); ZD = vector(2); ZM = vector(2); CD = vector(2); CR = vector(2); DT = vector(2);
{ for (k = 1, 2,
    my(f = red(-dd[k] * matdet(Msym(Qc[1]) + 2*t*Msym(Qc[2]) + t^2*Msym(Qc[3]))), fr, fa, q, h, c, dq, u, wV, cub, A, B, rts);
    fr = polrecip(f); c = pollead(fr, t);
    fa = nffactor(nf, fr); q = fa[1, 1]; h = fa[2, 1];
    chq(poldegree(q, t) == 2 && poldegree(h, t) == 4 && red(fr - c * q * h) == 0, "fRev = c q h");
    dq = red(polcoef(q, 1, t)^2 - 4 * polcoef(q, 0, t));
    u = polcoef(h, 3, t) / 2;
    wV = (polcoef(h, 2, t) - u^2 + dq * 'a) / 2;
    cub = red(dq * 'a * wV^2 - (u * wV - polcoef(h, 1, t) / 2)^2 - polcoef(h, 0, t) * dq * 'a);
    rts = nfroots(nf, cub); A = 0;
    foreach(rts, V0, if (V0 != 0 && gsq(V0),
      my(v0 = gsqrt(V0), w0 = red(subst(wV, 'a, V0)), z0);
      z0 = red((u * w0 - polcoef(h, 1, t) / 2) / (dq * v0));
      if (red((t^2 + u*t + w0)^2 - dq * (v0*t + z0)^2 - h) == 0, A = red(t^2 + u*t + w0); B = red(v0*t + z0); break)));
    chq(A != 0, "A, B");
    chq(red(A^2 - dq * B^2 - h) == 0, "h = A^2 - d B^2");
    my(a1 = polcoef(A, 1, t), a0 = polcoef(A, 0, t), b1 = polcoef(B, 1, t), b0 = polcoef(B, 0, t), q1 = polcoef(q, 1, t), q0 = polcoef(q, 0, t));
    chq(b1 != 0, "b1 != 0");
    MA[k] = lcm(den(zkc(a0)), den(zkc(a1))); MB[k] = lcm(den(zkc(b0)), den(zkc(b1)));
    AB[k] = [zkl(MA[k] * a0), zkl(MA[k] * a1), zkl(MB[k] * b0), zkl(MB[k] * b1)];
    printf("k = %d: h = A^2 - d B^2, denominators of a: %d, of b: %d; v(d) = %d, d square at v: %d\n", k - 1, MA[k], MB[k], vl(dq), lsq(dq));
    \\ sigma(b1) != 0: the residue of sigma(mb b1) modulo 8 is nonzero
    chq(zresOK(AB[k][4]) && modT(zres(AB[k][4]), 3) != [0, 0, 0], "sigma(mb b1) != 0 mod 8");
    \\ sigma(d) not a square: d = zkE(dnL) / 46^2, test sigma(zkE dnL) / 2^2 / 529
    my(ld = zkl(46^2 * dq), vd = vl(46^2 * dq), dsc = [0, 0], Pd);
    for (j = 0, 6, for (i = 0, 2, if (dsc == [0, 0] && (vd + 2*i - 6*j == 0 || vd + 2*i - 6*j == 2), dsc = [i, j])));
    Pd = 2 * dsc[2] + 3;
    chq(zresOK(ld) && Pd <= 28 && sqTest(zres(ld), dsc[1], dsc[2], 0, Pd), "sigma(d) not a square (test)");
    chq(!ksq(sg(dq)) && !lsq(dq), "sigma(d) not a square (p-adic and nfislocalpower)");
    DT[k] = [dsc[1], dsc[2], Pd];
    printf("  sigma(46^2 d): v = %d, test scaling %s at precision %d\n", vd, dsc, Pd);
    \\ D and rho
    my(D0 = red(a1^2 + dq * b1^2 - 4 * a0), D1 = red(2 * a1 * b1 - 4 * b0));
    my(P1 = a1 + b1 * 'w, P0 = a0 + b0 * 'w, p1 = q1 - P1, p0 = q0 - P0, rho, r0, r1);
    rho = lift(Mod(Mod(1, K21) * (p0^2 - p0 * p1 * P1 + p1^2 * P0), 'w^2 - dq));
    r0 = red(polcoef(rho, 0, 'w)); r1 = red(polcoef(rho, 1, 'w));
    my(ND = red(D0^2 - dq * D1^2), NR = red(r0^2 - dq * r1^2), els = [D0, D1, ND, r0, r1, NR]);
    ZM[k] = vector(6, i, den(zkc(els[i])));
    ZD[k] = vector(6, i, zkl(ZM[k][i] * els[i]));
    CD[k] = zcert("D", D0, D1, dq);
    CR[k] = zcert("rho", r0, r1, dq);
  );
}
\\ ---------------------------------------------------------------- output
out = Str(LEANDIR, "FurioLombardo/Discharge/M3a/LocalData.lean");
system(Str("rm -f ", out));
lst3(V) = { my(s = "["); for (i = 1, #V, s = Str(s, lstl(V[i]), if (i < #V, ",\n  ", ""))); Str(s, "]") };
tri(v) = Str("(", v[1], ", ", v[2], ", ", v[3], ")");
certS(C) = Str("⟨", tri(C[1]), ", ", C[2], ", ", C[3], ", ", C[4], ", ", C[5], ", ", C[6], ", ", C[7], ", ", C[8], "⟩");
write(out, "/-! Data of WP5 of the M3a discharge (generated by code/genus2-curves/local_facts_v_data.gp, PARI/GP): the local facts\n(irr) and (nsq) at the place above 2 with e = 3. Every element of K21 is a list of zk coordinates (lane M1's `zkE`)\nwith a denominator. Every identity and every residue condition is rechecked by the Lean kernel in\n`FurioLombardo.Discharge.M3a.Bruin` (LocalCheck.lean); see the generator for the meaning of each list. -/\n\nnamespace FurioLombardo.Discharge.M3a.Bruin\n\nset_option maxRecDepth 100000\n");
write(out, "/-- `abData[k]`: zk coordinates of `ma a0, ma a1, mb b0, mb b1`, where `h = A² - d B²`, `A = X² + a1 X + a0`,\n`B = b1 X + b0`. -/\ndef abData : List (List (List Int)) :=\n  ", lst3(AB), "\n");
write(out, "/-- Denominators `ma` of `a0, a1` and `mb` of `b0, b1`. -/\ndef maDen : List Nat := ", lst(MA), "\n\ndef mbDen : List Nat := ", lst(MB), "\n");
write(out, "/-- `zData[k]`: zk coordinates of `m D0, m D1, m N(D), m ρ0, m ρ1, m N(ρ)` (denominators `zDen[k]`), where\n`D = (a1 + b1 ω)² - 4 (a0 + b0 ω) = D0 + D1 ω`, `ρ = p0² - p0 p1 P1 + p1² P0 = ρ0 + ρ1 ω` (`P1 = a1 + b1 ω`,\n`P0 = a0 + b0 ω`, `p_i = q_i - P_i`), `ω² = d` and `N(z) = z0² - d z1²`. -/\ndef zData : List (List (List Int)) :=\n  ", lst3(ZD), "\n");
write(out, "def zDen : List (List Nat) := ", lstl(ZM), "\n");
write(out, "/-- Square root certificates `⟨b, M, r, P, ip, jp, im, jm⟩` for `D` (`certD`) and `ρ` (`certR`). -/\ndef certD : List (Int × Int × Int) × List (List Nat) :=\n  ([", tri(CD[1][1]), ", ", tri(CD[2][1]), "], [", lst(CD[1][2..8]), ", ", lst(CD[2][2..8]), "])\n");
write(out, "def certR : List (Int × Int × Int) × List (List Nat) :=\n  ([", tri(CR[1][1]), ", ", tri(CR[2][1]), "], [", lst(CR[1][2..8]), ", ", lst(CR[2][2..8]), "])\n");
write(out, "/-- Scaling `[i, j, P]` of the test that `σ d` is not a square. -/\ndef dTest : List (List Nat) := ", lstl(DT), "\n");
write(out, "end FurioLombardo.Discharge.M3a.Bruin");
print("written ", out);
quit;
