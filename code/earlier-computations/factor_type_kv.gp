\\ factor_type_kv.gp: factorization type of f_k over K_v (v the place above 2 with e = 3), for dim J(K_v)[2] = 1
\\ (see the paper). Independent of td2loc's local model: the primes above pr in the relative field
\\ fields L_j = K21[x]/(G_j) for the irreducible factors G_j of g_k over K21 (g_k the monic integral rescaling of f_k, same
\\ splitting type), from rnfidealprimedec with the relative order maximal at 2 (rnfinit with [G_j, [2]]). The factors of
\\ G_j over K_v correspond to the primes P | pr of L_j, of relative degree e(P/pr) f(P/pr) = (absolute e f)/3 (PARI reports e, f over Q). Expected: f_k = c G_2 G_4 over K21 and one
\\ prime above pr in each L_j, so f_k has exactly two irreducible factors over K_v, of degrees 2 and 4. Second check for
\\ G_2: its discriminant is not a square in K_v (nfislocalpower, exact).
\\ Run from code/earlier-computations: gp -q factor_type_kv.gp > factor_type_kv.out
default(parisizemax, 7 * 10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
nfK = nfinit([K21, [2, 7]]);
pr = [q | q <- idealprimedec(nfK, 2), q.e == 3][1];
{
  for (k = 0, 1,
    my(t0 = getabstime(), f = subst(if (k == 0, F0, F1), t, 'x) * Mod(1, K21), f6 = pollead(f), d = 1, g, fa, rnf, dec);
    for (i = 0, 5, d = lcm(d, denominator(nfalgtobasis(nfK, polcoef(f, i) / f6))));
    g = 'x^6 + sum(i = 0, 5, polcoef(f, i) / f6 * d^(6 - i) * 'x^i);
    for (i = 0, 5, if (denominator(nfalgtobasis(nfK, polcoef(g, i))) != 1, error("g not integral")));
    fa = nffactor(nfK, g);
    printf("k = %d: g_k over K21 factors with degrees %s (%d ms)\n", k, apply(poldegree, fa[, 1]~), getabstime() - t0);
    for (j = 1, #fa~, my(G = fa[j, 1]);
      rnf = rnfinit(nfK, [G, [2]]);
      dec = rnfidealprimedec(rnf, pr);
      printf("  factor of degree %d: primes of L_j above pr: %d; absolute [e, f] over Q = %s; relative degrees e(P/pr) f(P/pr) = %s (%d ms)\n", poldegree(G), #dec, apply(P -> [P.e, P.f], dec), apply(P -> P.e * P.f / (pr.e * pr.f), dec), getabstime() - t0);
      if (#dec != 1 || dec[1].e * dec[1].f != poldegree(G) * pr.e * pr.f, error("factor not irreducible over K_v"));
      if (poldegree(G) == 2, my(dsc = poldisc(G)); printf("  factor of degree 2: discriminant a square in K_v: %d\n", nfislocalpower(nfK, pr, dsc, 2)))));
}
quit;
