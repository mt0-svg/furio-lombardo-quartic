\\ two_torsion_image_resultant.gp: a sufficient condition for hypothesis (b) of
\\ FurioLombardo.Discharge.M3a.localTwoTorsion_route_of_factors on the reversed Prym sextics f = F_k^rev.
\\ If (q - r)(T) = c y^2 in L_v = K_v[T]/(q r), then taking norms to K_v in K_v[T]/(q) and K_v[T]/(r) gives
\\ Res(q, r) = N(-r(alpha)) = c^2 N(y)^2, a square in K_v. So Res(q, r) not a square at v implies (b).
\\ Also rechecks the factor degrees of F_k^rev over K21 and the leading coefficient condition at v.
\\ Run from code/genus2-curves: gp -q two_torsion_image_resultant.gp
default(parisizemax, 4 * 10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../earlier-computations/bruin_form.gp");
nfK = nfinit([K21, [2, 7]]);
pr = [P | P <- idealprimedec(nfK, 2), P.e == 3][1];
printf("v: e = %d, f = %d\n", pr.e, pr.f);
{
  for (k = 0, 1,
    my(f = subst(if (k == 0, F0, F1), t, 'x) * Mod(1, K21), fr, fa, q, r, R, degs);
    fr = polrecip(f);
    if (poldegree(fr) != 6, error("reversed sextic has degree < 6"));
    fa = nffactor(nfK, fr);
    degs = apply(poldegree, fa[, 1]~);
    printf("k = %d: f^rev over K21 has factors of degrees %s, multiplicities %s\n", k, degs, fa[, 2]~);
    q = [g | g <- fa[, 1]~, poldegree(g) == 2][1];
    if (pollead(q) != 1, error("q not monic"));
    r = fr / q;
    if (poldegree(r) != 4 || fr != q * r, error("bad factorization"));
    printf("  lc(f^rev) = f(0) a square at v: %d\n", nfislocalpower(nfK, pr, lift(pollead(fr)), 2));
    R = polresultant(q, r);
    printf("  valuation of Res(q, r) at v: %d\n", nfeltval(nfK, lift(R), pr));
    printf("  Res(q, r) a square at v: %d\n", nfislocalpower(nfK, pr, lift(R), 2));
    printf("  disc(q) a square at v: %d\n", nfislocalpower(nfK, pr, lift(poldisc(q)), 2));
  );
}
quit;
