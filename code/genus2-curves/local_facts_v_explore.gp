\\ local_facts_v_explore.gp: exploration for the three local facts at v (the place above 2 with e = 3) of the M3a discharge:
\\ (lead) lc(fRev_k) = f_k(0) not a square in K_v; (irr) h_k irreducible over K_v; (nsq) (q - c h)(T) not in
\\ K_v^x (L_v^x)^2. For (irr): Newton polygons of h(x + t) at pr for shifts t, looking for a single side of slope
\\ m/2 with m odd (then Ore: irreducible with e = 2, and the residual polynomial y^2 + y + 1 over F_2 gives f = 2).
\\ For (nsq): the sufficient condition "Res(q, h) not a square in K_v" (norm argument on the q-component).
\\ Run from code/genus2-curves: gp -q local_facts_v_explore.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
red(g) = lift(Mod(1, K21) * g);
pr = [P | P <- idealprimedec(nf, 2), P.e == 3][1];
PI = nfbasistoalg(nf, pr.gen[2]);
printf("pr: e = %d, f = %d, v(PI) = %d\n", pr.e, pr.f, nfeltval(nf, PI, pr));
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
dd = [d0, d1];
vl(a) = if (a == 0, oo, nfeltval(nf, a, pr));
{ for (k = 1, 2,
    my(f = red(-dd[k] * matdet(Msym(Qc[1]) + 2*t*Msym(Qc[2]) + t^2*Msym(Qc[3]))), fr, fa, q, h, c, V, best);
    fr = polrecip(f); c = pollead(fr, t);
    fa = nffactor(nf, fr); q = fa[1, 1]; h = fa[2, 1];
    if (poldegree(q, t) != 2 || poldegree(h, t) != 4, error("shape"));
    printf("k = %d: v(c) = %d, c square at v: %d, disc q square at v: %d, v(disc q) = %d\n", k - 1, vl(c),
      nfislocalpower(nf, pr, c, 2), nfislocalpower(nf, pr, poldisc(q), 2), vl(poldisc(q)));
    my(R = polresultant(Mod(1, K21) * q, Mod(1, K21) * h, t));
    printf("  Res(q, h): v = %d, square at v: %d\n", vl(lift(R)), nfislocalpower(nf, pr, lift(R), 2));
    printf("  v of the coefficients of q: %s, of h: %s\n", vector(3, i, vl(polcoef(q, i - 1, t))), vector(5, i, vl(polcoef(h, i - 1, t))));
    \\ shifts t = sum eps_i PI^i, i < 6, eps_i in {0, 1}
    best = [];
    forvec(e = vector(6, i, [0, 1]),
      my(s = red(sum(i = 1, 6, e[i] * PI^(i - 1))), g = red(subst(h, t, t + s)), w = vector(5, i, vl(polcoef(g, i - 1, t))));
      \\ single side from (0, w0) to (4, 0) with w0 = 2m, m odd, all points on or above
      if (w[1] % 2 == 0 && (w[1] / 2) % 2 == 1 && w[3] == w[1] / 2 && 2 * w[2] > 3 * w[1] / 2 && 2 * w[4] > w[1] / 2,
        best = concat(best, [[e, w]])));
    printf("  shifts with a single side of slope m/2, m odd, through (2, m): %d found\n", #best);
    for (i = 1, min(#best, 4), printf("    eps = %s, valuations of h(x + t): %s\n", best[i][1], best[i][2]));
    if (#best == 0,
      forvec(e = vector(4, i, [0, 1]),
        my(s = red(sum(i = 1, 4, e[i] * PI^(i - 1))), g = red(subst(h, t, t + s)));
        printf("    eps = %s: %s\n", e, vector(5, i, vl(polcoef(g, i - 1, t)))))));
}
quit;
