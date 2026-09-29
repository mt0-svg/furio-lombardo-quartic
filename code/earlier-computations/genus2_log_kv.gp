\\ genus2_log_kv.gp: group law and logarithm on the Jacobian of a genus 2 curve y^2 = f(x) (deg f = 6) over a completion
\\ K_v of a number field K, with K_v elements represented by elements of K (approximations modulo pr^MRED).
\\ Selmer group Chabauty at 2: the logarithm lattice log J(K_v) and the classes of the disc series.
\\
\\ Points of J: [u, v] with u monic of degree <= 2, deg v < deg u, u | v^2 - f (approximately), the class of
\\ P1 + P2 - Dinf (Dinf = inf+ + inf-, P_i = (x_i, v(x_i)), u(x_i) = 0); [1, 0] is the origin.
\\ Addition (generic case: gcd(u1, u2) = 1, or doubling with u1 coprime to v1): composition u = u1 u2, v the CRT lift of
\\ degree <= 3 with v^2 = f mod u, then div(y - v) = D1 + D2 + E - 3 Dinf gives D1 + D2 - 2 Dinf ~ iota(E) - Dinf,
\\ u3 = (f - v^2)/u (degree 2 when lc(v)^2 != lc(f)), v3 = -v mod u3.
\\ Logarithm with respect to (dx/y, x dx/y): for D = [P1 + P2 - Dinf] with P2 close to iota(P1),
\\   log D = int_{iota P1}^{P2} (1, x) dx / y = -(1/y1) int_0^s (x1 + z)^k (f(x1 + z)/f(x1))^(-1/2) dz,  s = x2 - x1,
\\ computed in the algebra B = K[th]/(u(th)) (th = x1, the conjugate root = x2), and log D = log(N D)/N in general.
\\ The value must be fixed by the conjugation of B (checked). Approximations: every result is reduced modulo pr^MRED
\\ (redK below); precision is estimated by recomputing at two working precisions.
\\
\\ Requires: nfK (maximal at 2), pr, LV = td2_lvinit(nfK, pr) with LV["IM"] = pr^MRED (as in p21_33_disc2.gp).


J2ZZ = varhigher("j2zz");     \\ series variable of higher priority than x (coefficients in B = K[x]/(u))
redK(LV, a) = {
  my(nfK = mapget(LV, "nfK"), c, dn, j, dodd, N, cz);
  if (type(a) == "t_INT" || a == 0, return(a));
  c = nfalgtobasis(nfK, a); dn = denominator(c); j = valuation(dn, 2); dodd = dn / 2^j;
  N = ceil(MRED / mapget(LV, "e")) + j + 2;
  cz = c * dn * lift(Mod(dodd, 2^N)^-1);
  nfbasistoalg(nfK, nfeltreduce(nfK, cz, idealmul(nfK, 2^j, mapget(LV, "IM")))) / 2^j;
}
redKx(LV, g) = if (type(g) != "t_POL", redK(LV, g), Pol(apply(c -> redK(LV, c), Vec(g)), variable(g)));
kval(LV, a) = if (a == 0, oo, nfeltval(mapget(LV, "nfK"), a, mapget(LV, "pr")));
\\ minimal valuation of the coefficients of a polynomial over K
kvalx(LV, g) = { my(m = oo); if (type(g) != "t_POL", return(kval(LV, g))); foreach (Vec(g), c, m = min(m, kval(LV, c))); m; }

\\ ---------------------------------------------------------------- group law
j2_red(LV, f, u, v) = {
  my(u3, v3);
  my(qr = divrem(f - v^2, u)); u3 = qr[1];
  chq(kvalx(LV, qr[2]) - kvalx(LV, u3) > MRED / 3, "j2_red: u does not divide f - v^2 to the working precision");
  chq(poldegree(u3) == 2, "j2_red: degree of u3 (lc(v)^2 = lc(f)?)");
  u3 = redKx(LV, u3 / pollead(u3)); v3 = redKx(LV, (-v) % u3);
  [u3, v3];
}
j2_add(LV, f, D1, D2) = {
  my(u1 = D1[1], v1 = D1[2], u2 = D2[1], v2 = D2[2], g, u, v);
  if (poldegree(u1) == 0, return(D2)); if (poldegree(u2) == 0, return(D1));
  chq(poldegree(u1) == 2 && poldegree(u2) == 2, "j2_add: reduced divisors of degree 2 expected");
  if (u1 == u2, return(j2_dbl(LV, f, D1)));
  g = gcdext(u1, u2); chq(poldegree(g[3]) == 0, "j2_add: u1, u2 not coprime");
  \\ v = v1 + u1 * ((v2 - v1) * inv(u1 mod u2) mod u2)
  v = v1 + u1 * (((v2 - v1) * g[1] / g[3]) % u2);
  u = u1 * u2;
  j2_red(LV, f, u, redKx(LV, v));
}
j2_dbl(LV, f, D) = {
  my(u1 = D[1], v1 = D[2], w, g, k, v);
  if (poldegree(u1) == 0, return(D));
  w = divrem(f - v1^2, u1)[1];
  g = gcdext(2 * v1, u1); chq(poldegree(g[3]) == 0, "j2_dbl: v1 and u1 not coprime (2-torsion)");
  k = (w * g[1] / g[3]) % u1;
  v = v1 + k * u1;
  j2_red(LV, f, u1^2, redKx(LV, v));
}
j2_neg(D) = [D[1], -D[2]];
j2_mul(LV, f, n, D) = {
  my(R = [1, 0], bn);
  if (n < 0, return(j2_mul(LV, f, -n, j2_neg(D))));
  if (n == 0, return(R));
  bn = binary(n);
  for (i = 1, #bn, R = j2_dbl(LV, f, R); if (bn[i], R = j2_add(LV, f, R, D)));
  R;
}

\\ ---------------------------------------------------------------- logarithm near the origin
\\ closeness of D = [u, v] to the origin: the valuation of s = x2 - x1 relative to the roots (v(disc u) / 2) and of
\\ y1 + y2 (both small near the origin in the chart of a non-Weierstrass point); returned as [v(disc u)/2, v(y1 + y2)]
j2_near0(LV, D) = {
  my(u = D[1], v = D[2], u1, u0, dsc, sy);
  if (poldegree(u) == 0, return([oo, oo]));
  u1 = polcoef(u, 1); u0 = polcoef(u, 0); dsc = u1^2 - 4 * u0;
  \\ y1 + y2 = v(x1) + v(x2) = 2 v0 + v1 (x1 + x2) = 2 v0 - v1 u1
  sy = 2 * polcoef(v, 0) - polcoef(v, 1) * u1;
  [kval(LV, dsc) / 2, kval(LV, sy)];
}
\\ log of D close to the origin in the chart of x. With x1 = th, s = x2 - x1, E(z) = f(x1 + z)/f(x1) - 1,
\\ e_j = E_j s^j and h_n = g_n s^n (g = (1 + E)^(-1/2) = sum g_n z^n), the scaled recursion
\\   2 n h_n = - sum_{j=1..min(6,n)} (2 (n - j) + j) e_j h_{n-j},  h_0 = 1,
\\ keeps every reduced quantity of moderate size (the unscaled g_n are large and s^n small: reducing s^n modulo pr^MRED
\\ and multiplying by g_n loses precision). Then int_0^s g dz = sum h_n s/(n+1), int_0^s (x1 + z) g dz =
\\ sum h_n (x1 s/(n+1) + s^2/(n+2)), and log D = -(1/y1) (these two integrals).
\\ Validity (p = 2): the z-series of (1 + E)^(-1/2) converges at s when v(E(z)) > 2 v(2) on |z| <= |s|; this is tested
\\ a posteriori: the h_n must fall below the noise level of the reductions (valuation >= MRED - 3 (3 + log2 n), measured)
\\ for 6 consecutive n before nmax (the series is then truncated there; exploratory, no tail bound yet),
\\ the branch must be the one of P2 (y1 + y2 g(s) = 0, y2 the conjugate of y1), and the value must be fixed by the
\\ conjugation of B. Returns [ok, [log1, log2], diagnostics]; ok = 0 when a test fails (then the value is meaningless).
j2_tinylog_x(LV, f, D, nmax) = {
  my(u = D[1], v = D[2], th, s, y1, y2, fx1, E, e, h, res, zz = J2ZZ, redB, nz = 0, n = 0, gs, I1, I2, thr = MRED / 2, bad = List());
  if (poldegree(u) == 0, return([1, [0, 0], []]));
  redB = (a -> if (type(a) == "t_POLMOD", Mod(redKx(LV, lift(a)), u), redK(LV, a)));
  th = Mod('x, u);
  s = redB(-polcoef(u, 1) - 2 * th);
  y1 = redB(subst(v, 'x, th)); y2 = redB(subst(v, 'x, -polcoef(u, 1) - th));
  fx1 = redB(subst(f, 'x, th));
  E = subst(f, 'x, th + zz);
  e = vector(6, j, redB(polcoef(E, j, zz) / fx1 * s^j));
  h = List([Mod(1, u)]);
  while (nz < 6 && n < nmax,
    n++;
    my(acc = 0); for (j = 1, min(6, n), acc += (2 * (n - j) + j) * e[j] * h[n - j + 1]);
    my(hn = redB(-acc / (2 * n))); listput(h, hn);
    if (kvalx(LV, lift(hn)) >= MRED - 3 * (3 + #binary(n)), nz++, nz = 0));
  if (nz < 6, listput(bad, "series"));
  gs = 0; I1 = 0; I2 = 0;
  for (k = 0, #h - 1, gs += h[k + 1]; I1 += h[k + 1] * s / (k + 1); I2 += h[k + 1] * (th * s / (k + 1) + s^2 / (k + 2)));
  if (kvalx(LV, lift(redB(y1 + y2 * gs))) <= thr, listput(bad, "branch"));
  res = [redB(-I1 / y1), redB(-I2 / y1)];
  res = apply(r -> Pol(lift(r), 'x), res);
  for (k = 1, 2, if (kvalx(LV, polcoef(res[k], 1, 'x)) <= thr, listput(bad, "conjugation")); res[k] = redK(LV, polcoef(res[k], 0, 'x)));
  [#bad == 0, res, [n, Vec(bad)]];
}
\\ the same in the chart at infinity: X = 1/x, Y = y/x^3, Y^2 = F(X) = X^6 f(1/X); D = [P1 + P2 - Dinf] becomes
\\ [P1' + P2' - Dinf'] (Q+ + Q- ~ Dinf' by div(X)), and (dx/y, x dx/y) = (-X dX/Y, -dX/Y), so log = (-l'_2, -l'_1)
j2_tinylog_inf(LV, f, D, nmax) = {
  my(u = D[1], v = D[2], u0, up, vp, F, r);
  if (poldegree(u) == 0, return([1, [0, 0], []]));
  u0 = polcoef(u, 0); if (u0 == 0 || kval(LV, u0) > MRED / 2, return([0, [0, 0], ["u(0) = 0"]]));
  chq(poldegree(f) == 6, "j2_tinylog_inf: deg f = 6");
  up = redKx(LV, 'x^2 + polcoef(u, 1) / u0 * 'x + 1 / u0);
  vp = redKx(LV, (polcoef(v, 0) * 'x^3 + polcoef(v, 1) * 'x^2) % up);
  F = Polrev(Vec(f), 'x);
  r = j2_tinylog_x(LV, F, [up, vp], nmax);
  [r[1], [-r[2][2], -r[2][1]], r[3]];
}
\\ log of D close to the origin: the chart of x, else the chart at infinity; with both = 1, both charts are computed
\\ and compared when both are valid (a consistency test). Errors out when no chart is valid.
j2_tinylog(LV, f, D, nmax, both = 0) = {
  my(rx = j2_tinylog_x(LV, f, D, nmax), ri);
  if (rx[1] && !both, return(rx[2]));
  ri = j2_tinylog_inf(LV, f, D, nmax);
  if (rx[1] && ri[1], chq(vecmin(vector(2, k, kval(LV, rx[2][k] - ri[2][k]))) > MRED / 2, "j2_tinylog: the two charts disagree"));
  if (rx[1], return(rx[2]));
  chq(ri[1], Str("j2_tinylog: no valid chart (x: ", rx[3], ", infinity: ", ri[3], ")"));
  ri[2];
}
\\ log D = log(N D) / N
j2_log(LV, f, D, N, nmax) = { my(ND = j2_mul(LV, f, N, D)); j2_tinylog(LV, f, ND, nmax) / N; }
\\ refine a certified divisor [u, v] (f = v^2 (1 + rho) mod u with v(rho) > 2 v(2)) to the working precision by Newton
\\ for the square root of f in B = K[x]/(u): v <- (v + f / v) / 2 mod u; u is kept (it is exact)
j2_refine(LV, f, D) = {
  my(u = D[1], v = D[2], it = 0, r);
  if (poldegree(u) == 0, return(D));
  while (1,
    r = (v^2 - f) % u;
    if (kvalx(LV, r) - kvalx(LV, v^2 % u) >= MRED - 3 * mapget(LV, "e") - 8, break);
    my(Bv = Mod(v, u), fv = Mod(f, u)); v = redKx(LV, lift((Bv + fv / Bv) / 2));
    it++; chq(it < 40, "j2_refine converged"));
  [u, v];
}
