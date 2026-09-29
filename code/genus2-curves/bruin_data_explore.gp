\\ bruin_data_explore.gp: WP2 data exploration (discharge of the M3a hypotheses).
\\ Bruin matrices, twists, f_delta = -delta det(M1 + 2t M2 + t^2 M3), the reversed sextic, its factorization over K21,
\\ integrality and sizes of the zk coordinates. Run from code/genus2-curves: gp -q bruin_data_explore.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
dig(v) = { my(m = vecmax(apply(e -> abs(e), Vec(v)))); if (m == 0, 0, #Str(m)); };
den(v) = denominator(content(v));
printf("Dz = %s = %s\n", Dz, factor(Dz));
\\ quadric coefficients: integrality and sizes
for (i = 1, 3, printf("Q%d: dens %s, digits %s\n", i, vector(6, j, den(QcZ[i][j])), vector(6, j, dig(QcZ[i][j]))));
dc = [zkc(d0), zkc(d1)];
for (k = 1, 2, printf("d%d: den %s, digits %s\n", k - 1, den(dc[k]), dig(dc[k])));
\\ symmetric matrices
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
M = vector(3, i, Msym(Qc[i]));
\\ check p M p^T = Q
{ for (i = 1, 3, my(p = [x, y, z], v = p * M[i] * p~);
    if (lift(v - Mod(Qs[i], K21)) != 0, error("matrix of Q", i))); }
print("p M_i p^T = Q_i: ok");
FF = [F0, F1]; dd = [d0, d1];
fd = vector(2, k, -Mod(dd[k], K21) * matdet(M[1] + 2*t*M[2] + t^2*M[3]));
{ for (k = 1, 2, if (lift(fd[k] - Mod(FF[k], K21)) != 0, error("f_delta vs F", k - 1))); }
print("f_delta_k = -d_k det(M1 + 2t M2 + t^2 M3) = F_k (bruin_form.gp): ok for k = 0, 1");
{ for (k = 1, 2, my(f = lift(fd[k]), cs = vector(7, j, zkc(polcoef(f, j - 1, t))));
    printf("F%d: deg %d, coef dens %s, digits %s\n", k - 1, poldegree(f, t), vector(7, j, den(cs[j])), vector(7, j, dig(cs[j]))));
}
\\ reversed sextic and its factorization
{ for (k = 1, 2,
    my(f = lift(fd[k]), fr = polrecip(f), fa, c);
    if (poldegree(fr, t) != 6, error("reversed degree"));
    c = pollead(fr, t);
    printf("k = %d: lc(fRev) = F_k(0), den %s, digits %s\n", k - 1, den(zkc(c)), dig(zkc(c)));
    fa = nffactor(nf, fr);
    printf("  nffactor of fRev over K21: degrees %s, multiplicities %s\n", apply(g -> poldegree(g, t), fa[, 1]~), fa[, 2]~);
    for (j = 1, #fa[, 1], my(g = fa[j, 1]);
      printf("  factor %d: monic %d, coefficient dens %s, digits %s\n", j, pollead(g, t) == 1,
        vector(poldegree(g, t) + 1, i, den(zkc(polcoef(g, i - 1, t)))), vector(poldegree(g, t) + 1, i, dig(zkc(polcoef(g, i - 1, t))))));
  );
}
quit;
