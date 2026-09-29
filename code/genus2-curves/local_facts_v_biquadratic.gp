\\ local_facts_v_biquadratic.gp: the local facts (irr) and (nsq) at v through N = K_v(sqrt d), d = disc q.
\\ h = A^2 - d B^2 over K21 (A monic quadratic, B linear; resolvent cubic as in bruin_data_check.sage), so
\\ M = K_v[x]/(h) = N[X]/(A + sqrt(d) B) contains N.
\\ (irr) h irreducible over K_v  <=  d non-square in K_v and D = disc(A + sqrt(d) B) = D0 + D1 sqrt(d) non-square in N.
\\ (nsq) (q - c h)(T) = c' y^2 in L_v gives, in M, w = q(x) / (-c h(tau)) a square (tau = (-q1 + s)/2, s = -A/B mod h
\\ the image of sqrt(d)), so rho = N_{M/N}(w) = rho0 + rho1 sqrt(d) is a square in N.
\\ Non-square test in N for z = z0 + z1 sqrt(d), z1 != 0: z = (a + b sqrt d)^2 forces N(z) = z0^2 - d z1^2 = n^2 in K_v
\\ and a^2 = (z0 + n)/2 or (z0 - n)/2. So z non-square in N if N(z) non-square in K_v, or if N(z) = n^2 and
\\ (z0 + n)/2, (z0 - n)/2 are non-squares in K_v.
\\ Run from code/genus2-curves: gp -q local_facts_v_biquadratic.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
red(g) = lift(Mod(1, K21) * g);
pr = [P | P <- idealprimedec(nf, 2), P.e == 3][1];
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
dd = [d0, d1];
vl(a) = if (a == 0, oo, nfeltval(nf, a, pr));
lsq(a) = nfislocalpower(nf, pr, lift(Mod(a, K21)), 2);
gsq(a) = #nfroots(nf, 'y^2 - lift(Mod(a, K21))) > 0;
gsqrt(a) = nfroots(nf, 'y^2 - lift(Mod(a, K21)))[1];
\\ N-elements as polynomials in 'z (sqrt d) modulo r^2 - dq
{ for (k = 1, 2,
    my(f = red(-dd[k] * matdet(Msym(Qc[1]) + 2*t*Msym(Qc[2]) + t^2*Msym(Qc[3]))), fr, fa, q, h, c, dq, u, Vv, wV, cub, A, B, rts);
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
    if (A == 0, error("no A, B"));
    printf("k = %d: h = A^2 - d B^2 found; d non-square at v: %d; -3 square at v: %d; -3d square at v: %d\n", k - 1, !lsq(dq), lsq(-3), lsq(-3 * dq));
    \\ (irr)
    my(a1 = polcoef(A, 1, t), a0 = polcoef(A, 0, t), b1 = polcoef(B, 1, t), b0 = polcoef(B, 0, t), D0, D1, ND);
    D0 = red(a1^2 + dq * b1^2 - 4 * a0); D1 = red(2 * a1 * b1 - 4 * b0); ND = red(D0^2 - dq * D1^2);
    printf("  (irr) D1 != 0: %d; N(D) square at v: %d, global square: %d\n", D1 != 0, lsq(ND), gsq(ND));
    if (gsq(ND), my(n = gsqrt(ND)); printf("    (D0 + n)/2 square at v: %d, (D0 - n)/2 square at v: %d\n", lsq((D0 + n) / 2), lsq((D0 - n) / 2)));
    \\ (nsq)
    my(Bi = red(lift(Mod(Mod(1, K21) * B, Mod(1, K21) * h)^(-1))), s, tau, htau, w, wr, P1, P0, w0, w1, rho, r0, r1, Nr);
    s = red(lift(Mod(-A * Bi, h)));
    if (red(lift(Mod(Mod(1, K21) * (s^2 - dq), Mod(1, K21) * h))) != 0, error("s^2 != d mod h"));
    for (sg = 0, 1,
      tau = red((-polcoef(q, 1, t) + (1 - 2 * sg) * s) / 2);
      if (red(lift(Mod(Mod(1, K21) * subst(q, t, tau), Mod(1, K21) * h))) != 0, error("q(tau) != 0 mod h"));
      htau = red(lift(Mod(Mod(1, K21) * subst(h, t, tau), Mod(1, K21) * h)));
      w = red(lift(Mod(Mod(1, K21) * q, Mod(1, K21) * h) / Mod(Mod(1, K21) * (-c * htau), Mod(1, K21) * h)));
      \\ reduce w(X) modulo X^2 + P1 X + P0 over K21[r]/(r^2 - d), P1 = a1 + (1 - 2 sg) r b1, P0 = a0 + (1 - 2 sg) r b0
      \\ (the embedding sends r to (1 - 2 sg) s, so that tau is the image of (-q1 + r)/2)
      my(e = 1 - 2 * sg);
      P1 = a1 + e * 'z * b1; P0 = a0 + e * 'z * b0;
      wr = lift(Mod(Mod(Mod(1, K21) * subst(w, t, 'X), Mod(1, K21) * ('z^2 - dq)), 'X^2 + P1 * 'X + P0));
      w0 = polcoef(wr, 0, 'X); w1 = polcoef(wr, 1, 'X);
      rho = lift(Mod(Mod(1, K21) * (w0^2 - P1 * w0 * w1 + P0 * w1^2), 'z^2 - dq));
      r0 = red(polcoef(rho, 0, 'z)); r1 = red(polcoef(rho, 1, 'z)); Nr = red(r0^2 - dq * r1^2);
      printf("  (nsq, sign %d) rho1 != 0: %d; N(rho) square at v: %d, global square: %d\n", e, r1 != 0, lsq(Nr), gsq(Nr));
      if (gsq(Nr), my(n = gsqrt(Nr)); printf("    (rho0 + n)/2 square at v: %d, (rho0 - n)/2 square at v: %d\n", lsq((r0 + n) / 2), lsq((r0 - n) / 2)))));
}
quit;
