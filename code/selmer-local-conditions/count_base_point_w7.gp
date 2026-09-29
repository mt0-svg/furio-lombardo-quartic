\\ count_base_point_w7.gp: a base point of C_1 : y^2 = fRev 1(x) over K_7 (the place above 7, e = 7, f = 3), for R7's chart.
\\ The six roots of fRev 1 cluster at P7 (count_points_w7.out), so x is taken next to the root r of q in K_7 (d = disc q
\\ is a square at P7, count_local_facts.out): x = r + eps with eps = f'(r) pi7^(2m), so that f(x) = f'(r)^2 pi7^(2m)
\\ (1 + O(pi7)). Everything is reduced mod P7^N7 (small heights). For each m: v(f(x)), whether f(x) is a square in K_7
\\ (nfislocalpower), the square certificate s = f'(r) pi7^m (v(f(x)/s^2 - 1) > 0 suffices
\\ since 2 is a unit), and tN0 of the coefficients of f(X + x) (R7's numerator of R0: nonzero means w0(0) != 0).
\\ Run from code/selmer-local-conditions: gp -q count_base_point_w7.gp < /dev/null > count_base_point_w7.out 2>&1
default(parisizemax, 10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
o = Mod(1, K21); red(g) = lift(o * g);
p7 = idealprimedec(nf, 7)[1];
unif7() = {my(B = idealhnf(nf, p7), r = 0); for (i = 1, #B, my(g = lift(nfbasistoalg(nf, B[, i]))); if (idealval(nf, g, p7) == 1, r = g; break)); if (r == 0, error("no uniformizer in the HNF basis")); r};
pi7 = unif7();
modpr = nfmodprinit(nf, p7);
N7 = 60; I7 = idealpow(nf, p7, N7); M7 = N7 \ 7 + 2;
\\ redN: a P7-integral x (denominator prime to 7 in the integral basis) replaced by an integral element of small
\\ height congruent to it mod P7^N7 (7^M7 lies in P7^N7): coordinates times D, times D^-1 mod 7^M7, then reduced mod P7^N7.
redN(x) = {my(z = nfalgtobasis(nf, x), D = denominator(z));
  if (D % 7 == 0, error("redN: not P7-integral"));
  z = apply(c -> centerlift(Mod(c * D, 7^M7) / D), z);
  lift(nfbasistoalg(nf, nfeltreduce(nf, z, I7)))};
issq7(x) = nfislocalpower(nf, p7, x, 2);
sqrtN(d) = {
  my(v = idealval(nf, d, p7), u, s);
  if (v % 2, error("odd valuation"));
  u = red(d / pi7^v);
  s = lift(nfbasistoalg(nf, nfmodprlift(nf, sqrt(nfmodpr(nf, u, modpr)), modpr)));
  for (i = 1, 7, s = redN(red((s + u / s) / 2)));
  if (idealval(nf, red(s^2 - u), p7) < N7 / 2, error("sqrt did not converge"));
  red(s * pi7^(v / 2));
}
tN0(c0, c1, c2, c3, c4) = 64*c0^3*c4 - 16*c0^2*c2^2 - 32*c0^2*c1*c3 + 24*c0*c1^2*c2 - 5*c1^4;
height(x) = vecmax(apply(c -> abs(c), nfalgtobasis(nf, x)));
print("v(pi7) = ", idealval(nf, pi7, p7), ", pi7 = ", pi7);
{
  my(k = 1, fr = polrecip(F1), fa = nffactor(nf, fr), q, d, sd, r, fp);
  q = fa[1, 1]; if (poldegree(q, t) != 2, q = fa[2, 1]);
  d = red(poldisc(o * q)); sd = sqrtN(d);
  r = redN(red((-polcoef(q, 1, t) + sd) / 2));
  fp = redN(red(subst(deriv(fr, t), t, r)));
  printf("twist %d: v(q(r)) = %d, v(f(r)) = %d, v(f'(r)) = %d\n", k, idealval(nf, red(subst(q, t, r)), p7),
    idealval(nf, red(subst(fr, t, r)), p7), idealval(nf, fp, p7));
  for (m = 1, 6,
    my(x = redN(red(r + fp * pi7^(2 * m))), fT, f0, s, e, N0);
    fT = red(subst(fr, t, t + x)); f0 = polcoef(fT, 0, t);
    s = redN(red(fp * pi7^m));
    e = if (f0 == 0, oo, idealval(nf, red(f0 / s^2 - 1), p7));
    N0 = red(tN0(polcoef(fT, 0, t), polcoef(fT, 1, t), polcoef(fT, 2, t), polcoef(fT, 3, t), polcoef(fT, 4, t)));
    printf("  m = %d: v(x - r) = %d, v(f(x)) = %d, square %d, v(f(x)/s^2 - 1) = %d, tN0 != 0: %d, v(tN0) = %d, height(x) = %d digits\n",
      m, idealval(nf, red(x - r), p7), idealval(nf, f0, p7), issq7(f0), e, N0 != 0, if (N0 == 0, oo, idealval(nf, N0, p7)),
      #Str(height(x)));
    if (m == 1, print("  chosen: m = 1, x and s in the integral basis nf.zk: x = ", nfalgtobasis(nf, x), ", s = ", nfalgtobasis(nf, s))));
}
print("DONE");
