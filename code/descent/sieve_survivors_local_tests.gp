\\ sieve_survivors_local_tests.gp: which local tests at 2 and 3 exclude the 8 good-prime survivors (Lean M1 planning).
\\ Run from code/descent: gp -q ../descent/descent_set_sieve_probe.gp sieve_survivors_local_tests.gp < /dev/null
MAXDEPTH = 40;
cel(c) = { my(e = Mod(1, K21)); for (j = 1, dimK, if (bittest(c, j-1), e *= nfbasistoalg(nf, G[j]))); e };
survE = vector(#surv, i, cel(surv[i]));
Fi(P) = substvec(F, [x, y, z], P);
print("valuations of generators at S: ", matrix(#S, dimK, i, j, nfeltval(nf, G[j], S[i])));
\\ square class of a nonzero element at pr: [v mod 2, unit part is local square]
{
foreach([2, 3], p,
  my(prs = idealprimedec(nf, p), stack = List(), leaves = List());
  print("p = ", p, ": primes ", vector(#prs, i, [prs[i].e, prs[i].f]));
  for (s1 = 0, p - 1, for (s2 = 0, p - 1,
    listput(stack, [[s1, s2, 1], 1, [1, 2]]);
    if (s2 % p == 0, listput(stack, [[1, s1, s2], 1, [2, 3]]));
    if (s1 % p == 0 && s2 % p == 0, listput(stack, [[s1, 1, s2], 1, [1, 3]]))));
  while (#stack,
    my(it = stack[#stack], P = it[1], m = it[2], fr = it[3]); listpop(stack);
    if (Fi(P) % p^m != 0, next);
    my(q1 = Mod(ev(Q1, P), K21), q3 = Mod(ev(Q3, P), K21), ok = 1, vals = vector(#prs), which = vector(#prs));
    for (i = 1, #prs, my(pr = prs[i], e = pr.e, s = if (p == 2, 2 * e + 1, 1), got = 0);
      foreach([[q1,1], [q3,3]], qq, my(q = qq[1]); if (!got && q != 0, my(v = nfeltval(nf, lift(q), pr)); if (m * e >= v + s, vals[i] = v; which[i] = qq[2]; got = 1)));
      if (!got, ok = 0));
    if (ok, listput(leaves, [P, m, vals, which]); next);
    for (d1 = 0, p - 1, for (d2 = 0, p - 1,
      my(Q = P); Q[fr[1]] += d1 * p^m; Q[fr[2]] += d2 * p^m;
      listput(stack, [Q, m + 1, fr]))));
  print("  ", #leaves, " leaves");
  \\ for each survivor and leaf: per prime, the parity of v(c Q) and whether c Q is a local square
  for (k = 1, #surv,
    my(c = survE[k], nparity = 0, nres = 0, allowed = 0, detail = List());
    foreach(leaves, L,
      my(P = L[1], par = 0, res = 0, sq = 1);
      for (i = 1, #prs, my(q = if (L[4][i] == 1, ev(Q1, P), ev(Q3, P)), w = lift(c * Mod(q, K21)), v = nfeltval(nf, w, prs[i]));
        if (v % 2, par = 1; sq = 0, if (!nfislocalpower(nf, prs[i], w, 2), res = 1; sq = 0)));
      if (sq, allowed++, if (par, nparity++, nres++)));
    print("  survivor ", surv[k], ": leaves allowing it ", allowed, ", killed by a parity ", nparity, ", killed only by residues ", nres));
);
}
