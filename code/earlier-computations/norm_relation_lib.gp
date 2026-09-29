\\ norm_relation_lib.gp: functions of sunits_n84.gp (S-units of N through a generalised norm relation), also used by
\\ p21_25_kat.gp. See the header of sunits_n84.gp for the method.
\\ the caller sets parisizemax and nbthreads (a default(parisizemax) inside a file being read stops the read)
[t, x, y, z, X, u, w, a, s, b];
\\ the caller reads field_l42_polynomial.gp, field_n84_polynomial.gp, field_k13_polynomial.gp first
DIR = "/tmp/k21c/nr/";
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
fexists(f) = #externstr(Str("ls ", f, " 2>/dev/null")) > 0;
\\ writebin appends to an existing file (and read then returns the vector of all objects): remove the file first
wbin(fn, obj) = { system(Str("rm -f ", fn)); writebin(fn, obj); }

\\ S-units of F in compact form, each checked to be an S-unit: returns [nf, list of famats (base as polynomials
\\ g(x) in Q[x]), torsion generator]
sunits_of(pol, name) = {
  my(t0 = getabstime(), bnf = bnfinit(nfinit([pol, [2, 7]]), 1), nf = bnf.nf, S, U, fams = List(), base = Map(), bl = List(), nb);
  S = concat(idealprimedec(nf, 2), idealprimedec(nf, 7));
  U = bnfunits(bnf, S)[1];
  printf("%s: bnfinit + bnfunits %d ms, signature %s, #S = %d, %d generators (last = torsion %s)\n", name, getabstime() - t0, nf.sign, #S, #U, U[#U]);
  chk(#U == nf.sign[1] + nf.sign[2] + #S, Str(name, ": number of generators = r1 + r2 + #S"));
  for (i = 1, #U - 1, my(F = U[i], fm = List());
    for (k = 1, #F~, my(g = F[k, 1], key, idx);
      g = if (type(g) == "t_INT", g, nfbasistoalg(nf, g));
      key = Str(lift(g));
      if (!mapisdefined(base, key, &idx), listput(bl, g); idx = #bl; mapput(base, key, idx));
      listput(fm, [idx, F[k, 2]]));
    listput(fams, Vec(fm)));
  nb = #bl;
  \\ exact S-unit check: valuation of each famat at every prime factor of every base element
  my(facs = vector(nb, k, idealfactor(nf, bl[k])), bad = 0);
  for (i = 1, #fams, my(fm = fams[i], vals = Map());
    for (k = 1, #fm, my(fa = facs[fm[k][1]]);
      for (l = 1, #fa~, my(pr = fa[l, 1], key = Str([pr.p, pr.e, pr.f, pr.gen[2]]), v0 = 0);
        if (pr.p == 2 || pr.p == 7, next);
        mapisdefined(vals, key, &v0); mapput(vals, key, v0 + fm[k][2] * fa[l, 2])));
    my(mv = Mat(vals));
    for (l = 1, #mv~, if (mv[l, 2] != 0, bad++)));
  chk(bad == 0, Str(name, ": every generator (product of ", nb, " distinct small elements) is an S-unit (exact valuations)"));
  printf("%s: %d ms\n", name, getabstime() - t0);
  [nf, Vec(fams), apply(g -> subst(lift(g), y, x), Vec(bl)), U[#U]];
}

\\ Arithmetic in N is done on the integral basis nfN.zk (LLL-reduced, small coordinates), never with polmods modulo
\\ the defining polynomial PN (whose coefficients are about 10^30, which makes polmod arithmetic very slow).
mul(nf, a, c) = nfalgtobasis(nf, nfeltmul(nf, a, c));   \\ always a column (nfeltmul returns a scalar on scalar columns)
mulmat(nf, c) = { my(n = poldegree(nf.pol), Id = matid(n)); matconcat(vector(n, i, nfeltmul(nf, c, Id[, i]))); }
\\ data of a monic factor p = X^d + sum c_k X^k over N: [d, multiplication matrices of c_0..c_{d-1}, X^i mod p for
\\ i = 0..imax as vectors of d columns]
factordata(nf, p, imax) = {
  my(d = poldegree(p), n = poldegree(nf.pol), Mc, Xp = vector(imax + 1), cur, nxt, z0 = vectorv(n));
  Mc = vector(d, k, mulmat(nf, nfalgtobasis(nf, polcoef(p, k - 1))));
  cur = vector(d, k, z0); cur[1] = matid(n)[, 1]; Xp[1] = cur;
  for (i = 1, imax, nxt = vector(d, k, if (k == 1, z0, cur[k - 1]));
    for (k = 1, d, nxt[k] -= Mc[k] * cur[d]);
    cur = nxt; Xp[i + 1] = cur);
  [d, Mc, Xp];
}
shiftX(fd, v) = { my(d = fd[1], nxt = vector(d, k, if (k == 1, 0 * v[1], v[k - 1]))); for (k = 1, d, nxt[k] -= fd[2][k] * v[d]); nxt; }
\\ N_{C/N}(g(X)) for g given by its power coefficients gv (g = sum gv[i+1] X^i)
compaction(nf, fd, gv) = {
  my(d = fd[1], z = vector(d, k, 0 * fd[3][1][1]), A, m12, m34, pr, s, dt);
  for (i = 1, #gv, if (gv[i], z += gv[i] * fd[3][i]));
  if (d == 1, return(z[1]));
  if (d == 2, return(mul(nf, z[1], z[1]) - fd[2][2] * mul(nf, z[1], z[2]) + fd[2][1] * mul(nf, z[2], z[2])));
  if (d != 4, error("factor degree ", d, " not implemented"));
  A = vector(4); A[1] = z; for (k = 2, 4, A[k] = shiftX(fd, A[k - 1]));   \\ A[k][r] = coefficient of X^(r-1) in z X^(k-1)
  pr = [[1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]];
  m12 = vector(6, q, my(i = pr[q][1], j = pr[q][2]); mul(nf, A[i][1], A[j][2]) - mul(nf, A[j][1], A[i][2]));
  m34 = vector(6, q, my(i = pr[q][1], j = pr[q][2]); mul(nf, A[i][3], A[j][4]) - mul(nf, A[j][3], A[i][4]));
  \\ Laplace expansion along rows 1, 2: det = sum over column pairs (i<j) of sign * minor12(i,j) * minor34(complement)
  dt = 0 * z[1];
  for (q = 1, 6, my(i = pr[q][1], j = pr[q][2], cq = setminus([1, 2, 3, 4], [i, j]), q2 = 7 - q);
    if (pr[q2] != cq, error("pairing"));
    s = (-1)^(i + j + 1 + 2);
    dt += s * mul(nf, m12[q], m34[q2]));
  dt;
}
\\ degree one primes P = (p, y - r) of N, one per rational prime p, p not dividing the index nor the zk denominators:
\\ [p, zk values mod p]
charprimes(nf, nprimes, p0) = {
  my(L = List(), p = p0, den = lcm(apply(zz -> denominator(content(zz)), nf.zk)) * nf.index);   \\ content of each zk polynomial separately (content of the vector is a polynomial)
  while (#L < nprimes, p = nextprime(p + 1);
    if (den % p == 0, next);
    my(rts = polrootsmod(nf.pol, p));
    \\ one root per p: characters at several primes above the same p are strongly correlated
    if (#rts > 0, listput(L, [p, apply(zz -> subst(zz, variable(nf.pol), rts[1]), nf.zk)])));
  Vec(L);
}
chi(P, v) = { my(r = sum(i = 1, #v, v[i] * P[2][i])); if (r == 0, error("element divisible by a character prime")); kronecker(lift(r), P[1]) < 0; }
