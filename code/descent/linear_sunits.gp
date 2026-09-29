\\ linear_sunits.gp: linear S-units a*b - k of K21 (norm -F(k,a), F the homogenized f21), Lean M1 planning.
default(parisizemax, 2*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
nf = nfinit(K21);
print("roots mod 3: ", polrootsmod(K21, 3), "  roots mod 439: ", polrootsmod(K21, 439));
print("factor mod 3: ", factormod(K21, 3)); print("factor mod 7: ", factormod(K21, 7));
print("factor mod 439 degrees: ", vector(#factormod(K21,439)~, i, poldegree(factormod(K21,439)[i,1])));
\\ which roots mod 3, 439 are the S primes (support of cB)
fa = idealfactor(nf, cB); print("cB: ", vector(#fa~, i, [fa[i,1].p, fa[i,1].f, fa[i,1].e, fa[i,2], if (fa[i,1].f == 1, lift(-polcoef(nfbasistoalg(nf, fa[i,1].gen[2]) , 0)), 0)]));
{
for (i = 1, #fa~, my(pr = fa[i,1]); if (pr.f == 1, my(r = [z | z <- polrootsmod(K21, pr.p), idealval(nf, b - lift(z), pr) > 0]); print("S prime above ", pr.p, " has root ", r)));
}
Fh(k, m) = subst(K21 * 1, b, k/m) * m^21;
sm(n) = { my(r = abs(n)); foreach([2,3,7,439], p, r /= p^valuation(r, p)); r == 1 };
L = List();
{
for (m = 1, 60, for (k = -400, 400, if (gcd(k, m) != 1, next);
  my(N = -Fh(k, m));
  if (N != 0 && sm(N), listput(L, [k, m, factor(N)]))));
}
print(#L, " smooth linear elements");
foreach(L, e, print(e));
