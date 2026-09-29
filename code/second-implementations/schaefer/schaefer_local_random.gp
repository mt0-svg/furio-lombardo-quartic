\\ schaefer_local_random.gp: independent test of the local Schaefer lemma (frozen form schaefer_local_sq
\\ of the Lean files) over M = Q_p, p = 2, 3, 5, theta = 0, on random data, and control runs with one
\\ hypothesis dropped (the test must then find parity failures, else it is vacuous).
\\ Data: f integral of degree 6, f(0) = 0; V = p^e V0 (e from -3 to 2, V0 integral of degree <= 1); w and u from the
\\ p-adic factorization of V^2 - f: u runs over the products of local factors of total degree 2, scaled by p^m * unit
\\ (u not monic). c = p^(min v(coefficients of u)). Claim tested: v(u(0)) - v(c) is even.
\\ Modes: "lemma" (lc(f) unit, f'(0) unit), "no f'" (f'(0) = 0 mod p, lc unit), "no lc" (lc = 0 mod p, f'(0) unit).
\\ Run from code/second-implementations/schaefer: gp -q schaefer_local_random.gp > schaefer_local_random.out 2>&1
setrand(20260928);
PREC = 60;
unitp(p) = { my(a); until (a % p, a = random(2 * p^3) - p^3); a; };
rnd(p) = random(2 * p^3 + 1) - p^3;
run(p, mode, NT) = {
  my(ntest = 0, nodd = 0, nskip = 0);
  for (trial = 1, NT,
    my(f, a1, a6, V, e, g, fa, facs = List(), us = List());
    a6 = if (mode == "no lc", p * rnd(p), unitp(p));
    a1 = if (mode == "no f'", p * rnd(p), unitp(p));
    f = a6 * x^6 + sum(j = 2, 5, rnd(p) * x^j) + a1 * x;
    if (poldegree(f) != 6 || a1 == 0, nskip++; next);
    e = random(6) - 3;
    V = p^e * (rnd(p) * x + rnd(p));
    if (V == 0, nskip++; next);
    g = V^2 - f;
    fa = factorpadic(g, p, PREC);
    for (i = 1, #fa~, for (m = 1, fa[i, 2], listput(facs, fa[i, 1])));
    for (i = 1, #facs, if (poldegree(facs[i]) == 2, listput(us, facs[i]));
      for (j = i + 1, #facs, if (poldegree(facs[i]) == 1 && poldegree(facs[j]) == 1, listput(us, facs[i] * facs[j]))));
    foreach(us, u0,
      my(u = p^(random(7) - 3) * unitp(p) * u0, vc, vu);
      vc = vecmin(apply(cc -> if (cc == 0, oo, valuation(cc, p)), Vec(u)));
      vu = valuation(polcoef(u, 0), p);
      if (vu >= PREC / 2, nskip++; next);
      ntest++;
      if ((vu - vc) % 2, nodd++)));
  printf("p = %d, mode %s: %d trials, %d (u, theta) tests, %d odd v(u(0)/c), %d skipped\n", p, mode, NT, ntest, nodd, nskip);
  [ntest, nodd];
}
{
  my(ok = 1, r);
  foreach([2, 3, 5], p,
    r = run(p, "lemma", 3000); if (r[2] != 0 || r[1] < 500, ok = 0);
    r = run(p, "no f'", 1500); if (r[2] == 0, print("  control without f'(theta) unit found no failure"));
    r = run(p, "no lc", 1500); if (r[2] == 0, print("  control without lc unit found no failure")));
  print(if (ok, "RESULT PASS (no odd valuation under the lemma's hypotheses)", "RESULT FAIL"));
}
quit;
