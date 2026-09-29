\\ descent_set_bad_primes_probe.gp: feasibility probe (not a proof step). Run after the sieve:
\\   gp -q descent_set_sieve_probe.gp descent_set_bad_primes_probe.gp < /dev/null
\\ Adds the local conditions at the primes of S (2, 3, 7, 439) to the survivors of the good-prime sieve.
\\ The local image delta(C(Q_p)) is SAMPLED (points with enumerated coordinate mod p^m, Hensel-lifted), so a
\\ class is removed only if no sampled point matches it; with a sampled image this can wrongly remove a class
\\ only if the sampling misses part of the image. KAT: the known classes delta(P0), delta(P1) must survive.
lp = 60;   \\ p-adic precision of the lifted points
BAD = if (type(BAD) == "t_VEC", BAD, [[2, 8], [3, 5], [7, 3], [439, 1]]);   \\ [p, m] pairs
INDEP = if (type(INDEP) == "t_INT", INDEP, 0);   \\ 1: test each prime against the good-prime survivors separately
lift1(r) = if (type(r) == "t_PADIC", truncate(r), r);
cel(c) = { my(e = Mod(1, K21)); for (j = 1, dimK, if (bittest(c, j-1), e *= nfbasistoalg(nf, G[j]))); e };
survE = vector(#surv, i, cel(surv[i]));
\\ points of C(Q_p) with integral coordinates, one of them 1; free coordinate enumerated mod p^m
padpts(p, m) = {
  my(L = List(), N = p^m);
  for (s = 0, N - 1,
    \\ z = 1, x = s, solve y in Z_p
    foreach(polrootspadic(substvec(F, [x, z], [s, 1]), p, lp), r, if (valuation(r, p) >= 0, listput(L, apply(lift1, [s, r, 1]))));
    \\ x = 1, z = p*s, solve y in Z_p
    foreach(polrootspadic(substvec(F, [x, z], [1, p*s]), p, lp), r, if (valuation(r, p) >= 0, listput(L, apply(lift1, [1, r, p*s]))));
    \\ y = 1, x = p*s, solve z in p Z_p
    foreach(polrootspadic(substvec(F, [x, y], [p*s, 1]), p, lp), r, if (valuation(r, p) >= 1, listput(L, apply(lift1, [p*s, 1, r])))));
  Vec(L);
}

dec = vector(4, k, idealprimedec(nf, [2, 3, 7, 439][k]));
{
foreach(BAD, pm,
  my(p = pm[1], m = pm[2], prs = idealprimedec(nf, p), pts = padpts(p, m), ok = vector(#surv), nused = 0);
  foreach(pts, P,
    my(P1 = apply(lift1, P), q = Mod(ev(Q1, P1), K21), bad = 0);
    for (i = 1, #prs, if (nfeltval(nf, lift(q), prs[i]) > 8 * prs[i].e, bad = 1));
    if (bad, q = Mod(ev(Q3, P1), K21); bad = 0; for (i = 1, #prs, if (nfeltval(nf, lift(q), prs[i]) > 8 * prs[i].e, bad = 1)));
    if (bad, next);
    nused++;
    for (k = 1, #surv, if (!ok[k],
      my(a = survE[k] * q, all = 1);
      for (i = 1, #prs, if (!nfislocalpower(nf, prs[i], lift(a), 2), all = 0; break));
      if (all, ok[k] = 1))));
  my(ns = select(k -> ok[k], [1 .. #surv]));
  print("p = ", p, " (m = ", m, "): ", #pts, " sampled points, ", nused, " used; survivors ", #ns, " of ", #surv, ": ", vector(#ns, k, surv[ns[k]]));
  if (#setminus(known, Set(vector(#ns, k, surv[ns[k]]))) > 0, error("KAT: a known class was removed at p = ", p));
  if (!INDEP, surv = vector(#ns, k, surv[ns[k]]); survE = vector(#ns, k, survE[ns[k]]));
);
}
print("survivors after the conditions at 2, 3, 7, 439: ", #surv, " ", surv, "; known among them: ", #setintersect(known, Set(surv)));
print("done: ", (getwalltime() - T0) / 1000., " s");
