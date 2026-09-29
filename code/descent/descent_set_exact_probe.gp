\\ descent_set_exact_probe.gp: feasibility probe (not a proof step). Run after the sieve:
\\   gp -q descent_set_sieve_probe.gp descent_set_exact_probe.gp < /dev/null
\\ With SELSET6_P='[3]' in the environment only the condition at 3 is applied, to all 8 survivors
\\ (output descent_set_exact_probe_p3.out).
\\ Replaces the sampled local images at p = 2 and p = 3 of descent_set_bad_primes_probe.gp by an over-approximation that is
\\ sound for exclusion. C(Q_p) is covered by the residue classes of normalized triples (three charts:
\\ (x, y, 1); (1, y, z) with p | z; (x, 1, z) with p | x, p | z) modulo p^m with F = 0 mod p^m, refined
\\ adaptively. On a class mod p^m, for a prime pr | p (ramification e, v(2) = e if p = 2, else 0) and Q in
\\ {Q1, Q3} (integral, trivial content), if v = v_pr(Q(P)) satisfies m e >= v + 2 v_pr(2) + 1 at the chosen
\\ representative P, then every point P' of the class has Q(P') = Q(P)(1 + t) with v_pr(t) >= 2 v_pr(2) + 1, so
\\ Q(P') and Q(P) have the same square class at pr (1 + pr^(2 v(2) + 1) consists of squares). On C, Q1 Q3 = Q2^2,
\\ so Q1 and Q3 give the same class at every pr where both are nonzero. A survivor c of the good-prime sieve is
\\ kept at p when some determined class makes c Q(P) a local square at every pr | p; classes of triples that
\\ contain no point of C(Q_p) are included too, which can only keep more survivors.
MAXDEPTH = 40;
cel(c) = { my(e = Mod(1, K21)); for (j = 1, dimK, if (bittest(c, j-1), e *= nfbasistoalg(nf, G[j]))); e };
survE = vector(#surv, i, cel(surv[i]));
Fi(P) = substvec(F, [x, y, z], P);
\\ class data of a triple mod p^m: [1, vector of per-prime elements] if determined, [0] otherwise
det_class(P, p, m, prs) = {
  my(q1 = Mod(ev(Q1, P), K21), q3 = Mod(ev(Q3, P), K21), out = vector(#prs));
  for (i = 1, #prs, my(pr = prs[i], e = pr.e, s = if (p == 2, 2 * e + 1, 1), ok = 0);
    foreach([q1, q3], q, if (!ok && q != 0, my(v = nfeltval(nf, lift(q), pr)); if (m * e >= v + s, out[i] = q; ok = 1)));
    if (!ok, return([0])));
  [1, out];
}
{
foreach(if (#getenv("SELSET6_P"), eval(getenv("SELSET6_P")), [2, 3]), p,
  my(prs = idealprimedec(nf, p), keep = vector(#surv), nleaf = 0, nref = 0, maxm = 0, stack = List());
  \\ level-1 seeds in the three charts: [triple, m, free-coordinate indices, fixed-coordinate]
  for (s1 = 0, p - 1, for (s2 = 0, p - 1,
    listput(stack, [[s1, s2, 1], 1, [1, 2]]);
    if (s2 % p == 0, listput(stack, [[1, s1, s2], 1, [2, 3]]));
    if (s1 % p == 0 && s2 % p == 0, listput(stack, [[s1, 1, s2], 1, [1, 3]]))));
  while (#stack,
    my(it = stack[#stack], P = it[1], m = it[2], fr = it[3]); listpop(stack);
    if (Fi(P) % p^m != 0, next);
    if (m > maxm, maxm = m);
    my(dc = det_class(P, p, m, prs));
    if (dc[1],
      nleaf++;
      for (k = 1, #surv, if (!keep[k],
        my(all = 1); for (i = 1, #prs, if (!nfislocalpower(nf, prs[i], lift(survE[k] * dc[2][i]), 2), all = 0; break));
        if (all, keep[k] = 1)));
      next);
    if (m >= MAXDEPTH, error("depth limit at ", P, " mod ", p, "^", m));
    nref++;
    for (d1 = 0, p - 1, for (d2 = 0, p - 1,
      my(Q = P); Q[fr[1]] += d1 * p^m; Q[fr[2]] += d2 * p^m;
      listput(stack, [Q, m + 1, fr]))));
  my(ns = select(k -> keep[k], [1 .. #surv]));
  print("p = ", p, ": ", nleaf, " determined classes, ", nref, " refinements, max m = ", maxm, "; survivors kept: ", vector(#ns, k, surv[ns[k]]));
  if (#setminus(known, Set(vector(#ns, k, surv[ns[k]]))) > 0, error("KAT: a known class was removed at p = ", p));
  surv = vector(#ns, k, surv[ns[k]]); survE = vector(#ns, k, survE[ns[k]]);
);
}
print("survivors after the exact (over-approximated) conditions at ", if (#getenv("SELSET6_P"), getenv("SELSET6_P"), "2 and 3"), ": ", #surv, " ", surv, "; known among them: ", #setintersect(known, Set(surv)));
print("done: ", (getwalltime() - T0) / 1000., " s");
