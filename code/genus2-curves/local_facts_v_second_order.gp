\\ local_facts_v_second_order.gp: second order data for (irr) h_k irreducible over K_v, and the location of the obstruction of
\\ (nsq). H(y) = h(PI y) / PI^4 (PI = pr.gen[2], a uniformizer at pr); valuations of H_i; phi = y^2 + y + 1 and the
\\ remainder of H modulo phi (valuation 1 exactly excludes a factorization into two monic quadratics over K_v).
\\ nsq: N = K_v[T]/(q) (q irreducible over K_v), nu = -c h(T) mod q; N(nu) a square in K_v means nu in K_v^x N^x2
\\ (the obstruction then lives in M = K_v[T]/(h)); printed for the record.
\\ Run from code/genus2-curves: gp -q local_facts_v_second_order.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
red(g) = lift(Mod(1, K21) * g);
pr = [P | P <- idealprimedec(nf, 2), P.e == 3][1];
PI = nfbasistoalg(nf, pr.gen[2]);
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
dd = [d0, d1];
vl(a) = if (a == 0, oo, nfeltval(nf, a, pr));
{ for (k = 1, 2,
    my(f = red(-dd[k] * matdet(Msym(Qc[1]) + 2*t*Msym(Qc[2]) + t^2*Msym(Qc[3]))), fr, fa, q, h, c, H, rm, nu);
    fr = polrecip(f); c = pollead(fr, t);
    fa = nffactor(nf, fr); q = fa[1, 1]; h = fa[2, 1];
    H = red(subst(h, t, PI * t) / PI^4);
    printf("k = %d: valuations of H_i (i = 0..4): %s\n", k - 1, vector(5, i, vl(polcoef(H, i - 1, t))));
    printf("  H(y) has a root mod pr (y = 0, 1): %s\n", [vl(subst(H, t, 0)) > 0, vl(subst(H, t, 1)) > 0]);
    rm = red(lift(Mod(Mod(1, K21) * H, Mod(1, K21) * (t^2 + t + 1))));
    printf("  remainder of H mod y^2 + y + 1: valuations of the coefficients [y^0, y^1] = %s\n", [vl(polcoef(rm, 0, t)), vl(polcoef(rm, 1, t))]);
    printf("  1 - H2 + H1: v = %d; H3 - H2 + H0: v = %d\n", vl(1 - polcoef(H, 2, t) + polcoef(H, 1, t)), vl(polcoef(H, 3, t) - polcoef(H, 2, t) + polcoef(H, 0, t)));
    nu = red(lift(Mod(Mod(1, K21) * (-c * h), Mod(1, K21) * q)));
    my(Nnu = red(polresultant(Mod(1, K21) * q, Mod(1, K21) * nu, t)));
    printf("  nsq: N_{N/K_v}(nu) square at v: %d (then nu in K_v^x N^x2, obstruction in M)\n", nfislocalpower(nf, pr, lift(Nnu), 2)));
}
quit;
