\\ dyadic_least_precision.gp: least k such that u c^2 = a^2 - d' b^2 has no solution modulo P3^k with one of a, b, c equal
\\ to 1, for u = zk[19] - 1 (a unit of K21 with (u, d)_P3 = -1, small_units_symbols.out) and d' = d / pi3^18.
\\ Residues modulo P3^k: sum_{i < k} e_i pi3^i, e_i in {0, 1} (f = 1). Run from code/selmer-global-bound.
default(parisizemax, 4*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../earlier-computations/bruin_form.gp");
read("../earlier-computations/richelot_data.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
d = Mod(RIN[1][5], K21);
d = d * denominator(content(lift(d)))^2;
nfK = nfinit([K21, [2, 7]]);
ram = idealfactor(nfK, rnfdisc(nfK, u^2 - lift(d))[1]);
P3 = 0; for (j = 1, #ram~, if (ram[j, 1].e == 3, P3 = ram[j, 1]));
pi3 = nfbasistoalg(nfK, P3.gen[2]);
v3 = idealval(nfK, lift(d), P3);
dp = d / pi3^v3;
uu = Mod(nfK.zk[19] - 1, K21);
chk(abs(norm(uu)) == 1, "u is a unit");
chk(nfhilbert(nfK, lift(uu), lift(d), P3) == -1, "(u, d)_P3 = -1");
\\ exact arithmetic modulo P3^k in coordinates: map O -> O/P3^k by nfmodpr is only for k = 1, so use valuations.
zmod(el, k) = (el == 0) || idealval(nfK, lift(el), P3) >= k;
\\ digits of a residue class: r = sum e_i pi^i; build all 2^k residues
reps(k) = {
  my(R = vector(2^k));
  for (n = 0, 2^k - 1, R[n + 1] = sum(i = 0, k - 1, bittest(n, i) * pi3^i));
  R;
}
{
for (k = 1, 10,
  my(R = reps(k), t0 = getabstime(), sol = 0);
  for (ia = 1, #R, for (ib = 1, #R, if (sol, break);
    my(A = R[ia], B = R[ib]);
    if (zmod(uu - A^2 + dp * B^2, k), sol = [1, A, B, "c = 1"]);
    if (!sol && zmod(uu * A^2 - 1 + dp * B^2, k), sol = [2, A, B, "a = 1"]);
    if (!sol && zmod(uu * B^2 - A^2 + dp, k), sol = [3, A, B, "b = 1"])));
  printf("k = %d: %s (%d ms)\n", k, if (sol, Str("normalised solution with ", sol[4]), "NO normalised solution"), getabstime() - t0);
  if (!sol, break));
}
quit;
