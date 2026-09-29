\\ sieve_survivors_obstructions.gp: per-prime obstruction detail (Lean M1 planning). Run after sieve_survivors_local_tests.gp's setup:
\\   gp -q ../descent/descent_set_sieve_probe.gp sieve_survivors_obstructions.gp < /dev/null
cel(c) = { my(e = Mod(1, K21)); for (j = 1, dimK, if (bittest(c, j-1), e *= nfbasistoalg(nf, G[j]))); e };
Fi(P) = substvec(F, [x, y, z], P);
\\ local square test at pr of w (nonzero): level N at which the unit part is shown non-square
lsq(w, pr) = { my(v = nfeltval(nf, w, pr)); if (v % 2, return([v, -1])); if (nfislocalpower(nf, pr, w, 2), return([v, 0])); [v, 1] };
leavesof(p) = {
  my(prs = idealprimedec(nf, p), stack = List(), leaves = List());
  for (s1 = 0, p - 1, for (s2 = 0, p - 1,
    listput(stack, [[s1, s2, 1], 1, [1, 2]]);
    if (s2 % p == 0, listput(stack, [[1, s1, s2], 1, [2, 3]]));
    if (s1 % p == 0 && s2 % p == 0, listput(stack, [[s1, 1, s2], 1, [1, 3]]))));
  while (#stack,
    my(it = stack[#stack], P = it[1], m = it[2], fr = it[3]); listpop(stack);
    if (Fi(P) % p^m != 0, next);
    my(q1 = Mod(ev(Q1, P), K21), q3 = Mod(ev(Q3, P), K21), ok = 1, which = vector(#prs));
    for (i = 1, #prs, my(pr = prs[i], e = pr.e, s = if (p == 2, 2 * e + 1, 1), got = 0);
      foreach([[q1,1], [q3,3]], qq, my(q = qq[1]); if (!got && q != 0, my(v = nfeltval(nf, lift(q), pr)); if (m * e >= v + s, which[i] = qq[2]; got = 1)));
      if (!got, ok = 0));
    if (ok, listput(leaves, [P, m, which]); next);
    for (d1 = 0, p - 1, for (d2 = 0, p - 1,
      my(Q = P); Q[fr[1]] += d1 * p^m; Q[fr[2]] += d2 * p^m;
      listput(stack, [Q, m + 1, fr]))));
  [prs, Vec(leaves)];
}
{
foreach([2, 3], p,
  my(LL = leavesof(p), prs = LL[1], leaves = LL[2]);
  print("p = ", p);
  foreach(surv, c0, my(c = cel(c0));
    print(" survivor ", c0);
    foreach(leaves, L, my(P = L[1], row = vector(#prs));
      for (i = 1, #prs, my(q = if (L[3][i] == 1, ev(Q1, P), ev(Q3, P))); row[i] = lsq(lift(c * Mod(q, K21)), prs[i]));
      print("   ", P, " m=", L[2], " Q", L[3], " [v, nonsq(1)/sq(0)/odd(-1)]: ", row))));
}
