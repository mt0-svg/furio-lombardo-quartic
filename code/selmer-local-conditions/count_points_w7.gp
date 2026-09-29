\\ count_points_w7.gp: K_7-points of C_k : y^2 = fRev k(x) (the place above 7, e = 7, f = 3) for R7's base point.
\\ fRev k = pi^7-content times g (every coefficient has valuation 7), so f(x) is a square iff pi^7 g(x) is: x must be
\\ close to a root of g mod P7. The roots rbar of g mod P7 in F_343 are lifted (nfmodprlift) and x = lift(rbar) + sum of
\\ c_i pi^i (c_i in {0..6}, i = 1..m) is tested: f(x) a local square, r4 != 0, r6 != 0 (as count_local_facts.gp (b)).
\\ Run from code/selmer-local-conditions: gp -q count_points_w7.gp < /dev/null > count_points_w7.out 2>&1
default(parisizemax, 2*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
o = Mod(1, K21); red(g) = lift(o * g);
p7 = idealprimedec(nf, 7)[1];
unif7() = {my(B = idealhnf(nf, p7), r = 0); for (i = 1, #B, my(g = lift(nfbasistoalg(nf, B[, i]))); if (idealval(nf, g, p7) == 1, r = g; break)); if (r == 0, error("no uniformizer in the HNF basis")); r};
pi7 = unif7();
print("v(pi7) = ", idealval(nf, pi7, p7));
modpr = nfmodprinit(nf, p7);
sq(x) = nfislocalpower(nf, p7, x, 2);
{
  for (k = 0, 1,
    my(fr = polrecip(if (k == 0, F0, F1)), c7, g, gb, fa, roots = List(), hits = List());
    \\ g = pi7^-7 fRev (integral, primitive at P7)
    g = red(fr / pi7^7);
    gb = Pol(apply(c -> nfmodpr(nf, c, modpr), Vec(g)), 'z);
    fa = factor(gb);
    print("twist ", k, ": g mod P7 factors of degrees ", apply(poldegree, fa[, 1]~), " multiplicities ", fa[, 2]~);
    for (i = 1, #fa~, if (poldegree(fa[i, 1]) == 1, listput(roots, -polcoef(fa[i, 1], 0) / polcoef(fa[i, 1], 1))));
    foreach(roots, rb,
      my(r0 = lift(nfbasistoalg(nf, nfmodprlift(nf, rb, modpr))), found = 0);
      forvec(c = vector(3, i, [0, 6]),
        my(x = red(r0 + sum(i = 1, 3, c[i] * pi7^i)), fT, f0, P, R);
        fT = red(subst(fr, t, t + x)); f0 = polcoef(fT, 0, t);
        if (f0 == 0 || !sq(f0), next);
        P = red(truncate(sqrt(Ser(o * fT / f0, t, 4)))); R = red(fT - f0 * P^2);
        if (polcoef(R, 4, t) == 0 || polcoef(R, 6, t) == 0, next);
        listput(hits, [rb, c, idealval(nf, f0, p7)]); found++;
        if (found >= 2, break)));
    print("  hits [root mod P7, digits c1..c3 of x - lift(root) on pi7^1..3, v(f0)]: ", Vec(hits)));
}
print("DONE");
\\ Second attempt: g mod P7 = unit (X - rbar)^6, so the roots cluster; the roots of q in K_7 are (-q1 +- sqrt d)/2 with
\\ d = disc(q) a square at P7 (count_local_facts.out). sqrt d to P7-adic precision N by Newton's iteration in K21 (reduced
\\ mod P7^N), r = (-q1 + sqrt d)/2, then x = r + eps with eps = f'(r) pi7^(2m): f(x) = f'(r)^2 pi7^(2m) (1 + ...).
N7 = 100; I7 = idealpow(nf, p7, N7);
redN(x) = lift(nfbasistoalg(nf, nfeltreduce(nf, x, I7)));
sqrtN(d) = {
  my(v = idealval(nf, d, p7), u, ub, s);
  if (v % 2, error("odd valuation"));
  u = red(d / pi7^v);
  ub = nfmodpr(nf, u, modpr);
  s = lift(nfbasistoalg(nf, nfmodprlift(nf, sqrt(ub), modpr)));
  for (i = 1, 7, s = redN(red((s + u / s) / 2)));
  if (idealval(nf, red(s^2 - u), p7) < N7 / 2, error("sqrt did not converge"));
  red(s * pi7^(v / 2));
}
{
  for (k = 0, 1,
    my(fr = polrecip(if (k == 0, F0, F1)), fa = nffactor(nf, fr), q, d, sd, r, hits = List());
    q = fa[1, 1]; if (poldegree(q, t) != 2, q = fa[2, 1]);
    d = red(poldisc(o * q)); sd = sqrtN(d);
    r = redN(red((-polcoef(q, 1, t) + sd) / 2));
    printf("twist %d: v(f(r)) = %d, v(q(r)) = %d (precision of the root), v(f'(r)) = %d\n", k, idealval(nf, red(subst(fr, t, r)), p7), idealval(nf, red(subst(q, t, r)), p7),
      idealval(nf, red(subst(deriv(fr, t), t, r)), p7));
    for (m = 1, 12,
      my(eps = redN(red(subst(deriv(fr, t), t, r) * pi7^(2 * m))), x = redN(red(r + eps)), fT, f0, P, R);
      fT = red(subst(fr, t, t + x)); f0 = polcoef(fT, 0, t);
      if (f0 == 0 || !sq(f0), next);
      P = red(truncate(sqrt(Ser(o * fT / f0, t, 4)))); R = red(fT - f0 * P^2);
      if (polcoef(R, 4, t) == 0 || polcoef(R, 6, t) == 0, next);
      listput(hits, [m, idealval(nf, f0, p7)]));
    print("  base points x = r + f'(r) pi7^(2m) with f(x) a square in K_7 and r4, r6 != 0: [m, v(f0)] ", Vec(hits)));
}
print("DONE 2");
