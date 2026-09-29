\\ Step 6 of the 2-descent: independent checks of the local square class maps cl2, cl7, clinf
\\ against PARI's nfislocalpower (a separate code path) and against splitting in quadratic extensions.
\\ Run from code/jacobian-over-q:
\\   gp -q -D parisizemax=4000000000 two_descent_lib.gp two_descent_local_images.gp fake_selmer_group.gp square_class_map_checks.gp
chk(b, s) = if (!b, error("CHECK FAILED: ", s), print("ok  ", s));
issq2(c) = nfislocalpower(bnf, P2, c, 2);
issq7a(c) = nfislocalpower(bnf, P7a, c, 2);
issq7b(c) = nfislocalpower(bnf, P7b, c, 2);
Z10 = vector(10, i, 0);

print("== rational square classes in L = A3 (x) Q_2");
{
  my(ok = 1, sq = List());
  foreach ([-1, 2, 5, -2, -5, 10, -10, 3, 7, 14, -7, 6], d,
    my(t = issq2(d));
    if (t != (cl2(d) == Z10), ok = 0);
    if (t, listput(sq, d)));
  chk(ok, "cl2(d) = 0 iff d is a square in L (nfislocalpower), for 12 rational d");
  print("   rational d among them that are squares in L: ", Vec(sq));
}
{
  \\ the same through the degree 16 field A3(sqrt d): P2 splits iff d is a square in L
  my(ok = 1);
  foreach ([-1, 2, 5, -2, -5, 10, -10], d,
    my(rnf = rnfinit(bnf, x^2 - d), s = #rnfidealprimedec(rnf, P2));
    if ((s == 2) != (cl2(d) == Z10), ok = 0));
  chk(ok, "same answer from the splitting of P2 in A3(sqrt d) for d in {-1, 2, 5, -2, -5, 10, -10}");
}

print("== all 256 classes of O_S^x / squares");
{
  my(ok2 = 1, ok7 = 1, oki = 1, nsq2 = 0);
  forvec (e = vector(8, i, [0, 1]),
    my(c = prod(i = 1, 8, Sgens[i]^e[i]), v2 = cl2(c), v7 = cl7(c));
    if (issq2(c) != (v2 == Z10), ok2 = 0);
    if (issq2(c), nsq2++);
    if (issq7a(c) != (v7[1] == 0 && v7[2] == 0), ok7 = 0);
    if (issq7b(c) != (v7[3] == 0 && v7[4] == 0), ok7 = 0);
    my(s = nfeltsign(bnf, c)); if (clinf(c) != vector(2, i, s[i] < 0), oki = 0));
  chk(ok2, "cl2(c) = 0 iff c is a square at P2, for all 256 S-unit classes");
  chk(ok7, "cl7 agrees with nfislocalpower at P7a and P7b, for all 256 S-unit classes");
  chk(oki, "clinf agrees with nfeltsign");
  print("   S-unit classes that are squares in L: ", nsq2);
}

print("== the three sampled generators of Im(delta_2) are independent modulo squares and Q_2^x");
{
  my(val(P) = my(x0 = P[1], yP = P[2], k = max(0, max(-valuation(x0, 2), -valuation(yP, 2))));
               substvec(GA, [x,y,z], [x0 * 2^k, truncate(yP * 2^k), 2^k]),
     bb = substvec(GA, [x,y,z], [1,1,1]), g, nsq = 0, tot = 0);
  g = vector(#Im2pts, i, val(Im2pts[i]) / bb);
  forvec (e = vector(#g, i, [0, 1]),
    foreach ([1, -1, 2, -2], d,
      my(c = d * prod(i = 1, #g, g[i]^e[i]));
      tot++;
      if (issq2(c), nsq++; if (e != vector(#g, i, 0) || d != 1, error("unexpected local square")))));
  chk(nsq == 1, Str("among the ", tot, " products d * g^e (d in {1,-1,2,-2}), only the trivial one is a square in L"));
  print("   (5 is a square in L, so Q_2^x maps onto <-1, 2> modulo L^x2): the sampled span has dimension 3 by an independent test");
  \\ precision: the generators were accepted only with v_P(G_A(Ptilde)) + 9 <= 4 * precision; recheck here
  for (i = 1, #Im2pts, my(P = Im2pts[i], k = max(0, max(-valuation(P[1], 2), -valuation(P[2], 2))));
    chk(nfeltval(bnf, val(P), P2) + 9 <= 4 * padicprec(P[2] * 2^k, 2), "precision of a generator point"));
}

print("== sanity: degree 2 divisors over Q_2 also land in Im(delta_2)");
\\ For x0 in Q and an irreducible quadratic factor of F(x0, y, 1) over Q_2, the orbit {Q, Qbar} minus 2 P1 is a
\\ divisor of J(Q_2); its class is Res_y(q, G_A(x0, y, 1)) / G_A(P1)^2 (points rescaled by 2^k to make q integral,
\\ which only changes the value by a rational factor).  Same precision criterion as in step 3.
{
  my(cnt = 0, out = 0, cb = cl2(substvec(GA, [x,y,z], [1,1,1])), r0 = f2rank(Im2), prec = 60);
  for (x0 = -80, 80,
    my(f = subst(subst(F, z, 1), x, x0), fa = factorpadic(f, 2, prec));
    for (i = 1, #fa~, my(q = fa[i, 1]);
      if (poldegree(q, y) != 2, next);
      q = q / polcoef(q, 2, y);
      my(b = polcoef(q, 1, y), c = polcoef(q, 0, y), k = 0);
      while (valuation(2^k * b, 2) < 0 || valuation(4^k * c, 2) < 0, k++);
      b = 2^k * b; c = 4^k * c;
      my(pr = min(padicprec(b, 2), padicprec(c, 2)), qt = y^2 + truncate(b)*y + truncate(c), v);
      v = polresultant(qt, substvec(GA, [x, z], [x0 * 2^k, 2^k]), y);
      if (v == 0, next);
      if (nfeltval(bnf, v, P2) + 9 > 4 * pr, next);
      cnt++;
      if (f2rank(matconcat([Im2, ((cl2(v) - 2 * cb) % 2)~])) > r0, out++)));
  chk(cnt > 100 && out == 0, Str(cnt, " quadratic Q_2-orbits: every one lies in Im(delta_2) (consistent with dim Im(delta_2) = 3)"));
}
print("step 6 done");
