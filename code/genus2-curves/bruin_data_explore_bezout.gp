\\ bruin_data_explore_bezout.gp: WP2 exploration, part 2: Bezout certificate of fRev, disc(q), square root of d modulo h and
\\ modulo fRev, residue primes of degree one, the known lifts. Run from code/genus2-curves: gp -q bruin_data_explore_bezout.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
dig(v) = { my(m = vecmax(apply(e -> abs(e), Vec(v)))); if (m == 0, 0, #Str(m)); };
den(v) = denominator(content(v));
pden(g) = lcm(vector(poldegree(g, t) + 1, i, den(zkc(polcoef(g, i - 1, t)))));
pdig(g) = vecmax(vector(poldegree(g, t) + 1, i, dig(zkc(polcoef(g, i - 1, t)))));
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
M = vector(3, i, Msym(Qc[i]));
dd = [d0, d1];
fd = vector(2, k, lift(-Mod(dd[k], K21) * matdet(M[1] + 2*t*M[2] + t^2*M[3])));
fr = vector(2, k, polrecip(fd[k]));
\\ reduction modulo K21 of a polynomial in t with polmod coefficients
red(g) = lift(Mod(1, K21) * g);
DBf = poldisc(K21) * pollead(K21);
DBr = polresultant(K21, K21');
printf("resultant(fZ, fZ') = %s, factor: %s\n", DBr, factor(DBr));
\\ residue of zk coordinates a at (p, theta - r)
resz(a, p, r) = { my(u = Mod(Dz, p)^(-1), s = Mod(0, p)); for (j = 1, 21, s += a[j] * subst(Pol(Vecrev(zkNum[j]), 'w), 'w, Mod(r, p))); lift(u * s) };
roots1(p) = if (DBr % p == 0 || Dz % p == 0, [], apply(e -> lift(e), polrootsmod(K21, p)));
\\ first primes of degree one where the element with zk coordinates a is a non-residue
nonres(a, nmax) = { my(L = List()); forprime(p = 3, 10^4, foreach(roots1(p), r, if (kronecker(resz(a, p, r), p) == -1, listput(L, [p, r]); if (#L >= nmax, return(Vec(L)))))); Vec(L) };
{ for (k = 1, 2,
    my(f = fr[k], fa = nffactor(nf, f), q, h, c, bb, cc, dq, dR, e, AR, BR, Arev, Brev, bh, bq, beta, gam, U, V, g);
    q = fa[1, 1]; h = fa[2, 1]; c = pollead(f, t);
    if (poldegree(q, t) != 2 || poldegree(h, t) != 4, error("factor degrees"));
    if (red(f - c * q * h) != 0, error("factorization"));
    printf("k = %d: fRev = c q h: ok\n", k - 1);
    \\ Bezout certificate of fRev and its derivative
    g = gcdext(Mod(1, K21) * f, Mod(1, K21) * deriv(f, t));
    U = red(g[1]); V = red(g[2]);
    if (red(U * f + V * deriv(f, t) - lift(g[3])) != 0 || poldegree(lift(g[3]), t) != 0, error("bezout"));
    my(g3 = red(g[3]), U1 = red(U / g3), V1 = red(V / g3));
    printf("  Bezout a f + b f' = 1: deg a %d, deg b %d, dens %s %s, digits %s %s\n", poldegree(U1, t), poldegree(V1, t),
      pden(U1), pden(V1), pdig(U1 * pden(U1)), pdig(V1 * pden(V1)));
    \\ discriminant of q
    bb = polcoef(q, 1, t); cc = polcoef(q, 0, t); dq = red(bb^2 - 4 * cc);
    printf("  d = disc q: den %s, digits %s, square in K21: %d\n", den(zkc(dq)), dig(zkc(dq)), #nfroots(nf, 'X^2 - dq) > 0);
    \\ RIN data: F_k = cR G1 (A^2 - dR B^2) in t (unreversed)
    my(R = RIN[k], cR = R[1], G1 = R[2], A = R[3], B = R[4]);
    dR = R[5];
    if (red(cR * G1 * (A^2 - dR * B^2) - fd[k]) != 0, error("RIN"));
    printf("  RIN: F_k = cR G1 (A^2 - dR B^2): ok; deg A %d, deg B %d\n", poldegree(A, t), poldegree(B, t));
    e = nfroots(nf, 'X^2 - red(dq / dR));
    printf("  d / dR square in K21: %d\n", #e > 0);
    Arev = t^2 * subst(A, t, 1/t); Brev = t^2 * subst(B, t, 1/t);
    Arev = red(Arev); Brev = red(Brev);
    my(hr = red(Arev^2 - dR * Brev^2));
    if (red(hr - pollead(hr, t) * h) != 0, error("h vs Arev^2 - dR Brev^2"));
    \\ square root of d modulo h
    my(Bi = lift(Mod(1, K21) * lift(Mod(Mod(1, K21) * Brev, Mod(1, K21) * h)^(-1))));
    bh = red(lift(Mod(Mod(1, K21) * e[1] * Arev * Bi, Mod(1, K21) * h)));
    if (red(lift(Mod(Mod(1, K21) * (bh^2 - dq), Mod(1, K21) * h))) != 0, error("sqrt d mod h"));
    printf("  beta_h^2 = d mod h: ok; beta_h dens %s digits %s\n", pden(bh), pdig(bh * pden(bh)));
    \\ CRT with 2T + b modulo q
    bq = 2 * t + bb;
    my(qi = lift(Mod(Mod(1, K21) * q, Mod(1, K21) * h)^(-1)));
    beta = red(bq + q * lift(Mod(Mod(1, K21) * (bh - bq) * qi, Mod(1, K21) * h)));
    if (poldegree(beta, t) > 5, error("deg beta"));
    gam = red((beta^2 - dq) / f);
    if (red(beta^2 - dq - f * gam) != 0, error("beta gamma"));
    printf("  beta^2 - d = fRev gamma: ok; deg beta %d, deg gamma %d, dens %s %s, digits %s %s\n", poldegree(beta, t),
      poldegree(gam, t), pden(beta), pden(gam), pdig(beta * pden(beta)), pdig(gam * pden(gam)));
    \\ residue primes: lc numerator 4 c, d numerator
    my(cn = zkc(4 * c), dn = zkc(dq * den(zkc(dq))^2));
    printf("  non-residue primes for 4 lc: %s\n", nonres(cn, 3));
    printf("  non-residue primes for den^2 d: %s\n", nonres(dn, 3));
  );
}
\\ the known lifts
Pts = [[0, 0, 1], [2, 0, 1], [1, 1, 1], [-1, 0, 1]];
Ev(Q, P) = red(substvec(Q, [x, y, z], P));
{ for (i = 1, 4,
    my(P = Pts[i], k = if (i <= 2, 1, 2), dl = dd[k], v = vector(3, j, Ev(Qs[j], P)), r, s);
    if (subst(subst(subst(F, x, P[1]), y, P[2]), z, P[3]) != 0, error("point"));
    if (v[1] != 0,
      r = nfroots(nf, 'X^2 - red(v[1] / dl)); if (#r == 0, error("Q1/delta non square"));
      r = r[1]; s = red(v[2] / (dl * r)),
      r = 0; s = nfroots(nf, 'X^2 - red(v[3] / dl)); if (#s == 0, error("Q3/delta non square")); s = s[1]);
    if (red(v[1] - dl * r^2) != 0 || red(v[2] - dl * r * s) != 0 || red(v[3] - dl * s^2) != 0, error("lift equations"));
    printf("P = %s, twist %d: Q(P) = 0? %s; r den %s digits %s, s den %s digits %s\n", P, k - 1, apply(e -> e == 0, v),
      den(zkc(r)), dig(zkc(r)), den(zkc(s)), dig(zkc(s)));
  );
}
quit;
