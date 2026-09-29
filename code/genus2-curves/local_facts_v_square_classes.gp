\\ local_facts_v_square_classes.gp: square classes in N = K21(sqrt d)_w (w the prime of N above v) of the elements of local_facts_v_biquadratic.gp:
\\ D = disc(A + sqrt(d) B) (irr: must be a non-square) and rho = N_{M/N}(w) (nsq: a non-square suffices), for both
\\ embeddings. N is realised as K21[x]/(q), sqrt(d) = 2x + q1; absolute field of degree 42, maximal at 2.
\\ Run from code/genus2-curves: gp -q local_facts_v_square_classes.gp
default(parisizemax, 6*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
red(g) = lift(Mod(1, K21) * g);
pr = [P | P <- idealprimedec(nf, 2), P.e == 3][1];
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
dd = [d0, d1];
gsq(a) = #nfroots(nf, 'y^2 - lift(Mod(a, K21))) > 0;
gsqrt(a) = nfroots(nf, 'y^2 - lift(Mod(a, K21)))[1];
{ for (k = 1, 2,
    my(T0 = getabstime(), f = red(-dd[k] * matdet(Msym(Qc[1]) + 2*t*Msym(Qc[2]) + t^2*Msym(Qc[3]))), fr, fa, q, h, c, dq, u, wV, cub, A, B, rts, rnf, nfN, PN, toN, isqN);
    fr = polrecip(f); c = pollead(fr, t);
    fa = nffactor(nf, fr); q = fa[1, 1]; h = fa[2, 1];
    dq = red(polcoef(q, 1, t)^2 - 4 * polcoef(q, 0, t));
    u = polcoef(h, 3, t) / 2;
    wV = (polcoef(h, 2, t) - u^2 + dq * 'a) / 2;
    cub = red(dq * 'a * wV^2 - (u * wV - polcoef(h, 1, t) / 2)^2 - polcoef(h, 0, t) * dq * 'a);
    rts = nfroots(nf, cub); A = 0;
    foreach(rts, V0, if (V0 != 0 && gsq(V0),
      my(v0 = gsqrt(V0), w0 = red(subst(wV, 'a, V0)), z0);
      z0 = red((u * w0 - polcoef(h, 1, t) / 2) / (dq * v0));
      if (red((t^2 + u*t + w0)^2 - dq * (v0*t + z0)^2 - h) == 0, A = red(t^2 + u*t + w0); B = red(v0*t + z0); break)));
    my(qm = 46, qi = red(subst(q, t, 'x / qm) * qm^2));
    if (denominator(content(apply(e -> content(nfalgtobasis(nf, e)), Vec(qi)))) != 1, error("q not integral after scaling"));
    rnf = rnfinit(nf, [qi, [2]]);
    nfN = nfinit([rnf.polabs, [2]]);
    my(g2 = rnfeltreltoabs(rnf, nfbasistoalg(nf, pr.gen[2])));
    PN = [P | P <- idealprimedec(nfN, 2), nfeltval(nfN, g2, P) > 0 && nfeltval(nfN, rnfeltreltoabs(rnf, 2), P) == 6];
    printf("k = %d: primes of N above v: %d, [e, f] = %s (%d ms)\n", k - 1, #PN, apply(P -> [P.e, P.f], PN), getabstime() - T0);
    PN = PN[1];
    toN = ((z0, z1) -> rnfeltreltoabs(rnf, Mod(1, K21) * (z0 + z1 * (2 * 'x / 46 + polcoef(q, 1, t)))));
    isqN = ((z0, z1) -> nfislocalpower(nfN, PN, toN(z0, z1), 2));
    printf("  -3 square in N_w: %d; d square in N_w: %d (expected 1)\n", isqN(-3, 0), isqN(dq, 0));
    my(a1 = polcoef(A, 1, t), a0 = polcoef(A, 0, t), b1 = polcoef(B, 1, t), b0 = polcoef(B, 0, t), D0, D1);
    D0 = red(a1^2 + dq * b1^2 - 4 * a0); D1 = red(2 * a1 * b1 - 4 * b0);
    printf("  (irr) D square in N_w: %d, -3 D square in N_w: %d\n", isqN(D0, D1), isqN(-3 * D0, -3 * D1));
    my(Bi = red(lift(Mod(Mod(1, K21) * B, Mod(1, K21) * h)^(-1))), s, tau, htau, w, wr, P1, P0, w0, w1, rho, r0, r1);
    s = red(lift(Mod(-A * Bi, h)));
    for (sg = 0, 1,
      my(e = 1 - 2 * sg);
      tau = red((-polcoef(q, 1, t) + e * s) / 2);
      htau = red(lift(Mod(Mod(1, K21) * subst(h, t, tau), Mod(1, K21) * h)));
      w = red(lift(Mod(Mod(1, K21) * q, Mod(1, K21) * h) / Mod(Mod(1, K21) * (-c * htau), Mod(1, K21) * h)));
      P1 = a1 + e * 'z * b1; P0 = a0 + e * 'z * b0;
      wr = lift(Mod(Mod(Mod(1, K21) * subst(w, t, 'X), Mod(1, K21) * ('z^2 - dq)), 'X^2 + P1 * 'X + P0));
      w0 = polcoef(wr, 0, 'X); w1 = polcoef(wr, 1, 'X);
      rho = lift(Mod(Mod(1, K21) * (w0^2 - P1 * w0 * w1 + P0 * w1^2), 'z^2 - dq));
      r0 = red(polcoef(rho, 0, 'z)); r1 = red(polcoef(rho, 1, 'z));
      printf("  (nsq, sign %d) rho square in N_w: %d, -3 rho square in N_w: %d\n", e, isqN(r0, r1), isqN(-3 * r0, -3 * r1))));
}
quit;
