\\ field_two_power_index_search.gp: search theta in O_K21 whose order Z[theta] has index a power of 2 (Lean M1 planning).
default(parisizemax, 2*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
nf = nfinit(K21); dK = nf.disc;
best = 10^100; setrand(1);
odd(n) = n / 2^valuation(n, 2);
{
for (trial = 1, 20000,
  my(v = vector(21, i, if (i == 1, 0, random(5) - 2)), th = nfbasistoalg(nf, v~), cp = charpoly(th, 'X));
  if (poldegree(cp) != 21 || !issquarefree(cp), next);
  my(ind2 = poldisc(cp) / dK); if (denominator(ind2) != 1, next);
  my(o = odd(sqrtint(abs(ind2))));
  if (o < best, best = o; print("trial ", trial, ": odd part of index ", factor(o), " v2 ", valuation(ind2,2)/2, " maxcoef ", vecmax(abs(Vec(cp))), " v = ", v));
  if (o == 1, break));
}
