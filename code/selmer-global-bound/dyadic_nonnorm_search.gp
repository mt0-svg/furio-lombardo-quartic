\\ dyadic_nonnorm_search.gp: a small dyadic non-norm certificate for L = K21(sqrt d) at the prime P3 above 2 with e = 3 (f = 1).
\\ (a) small units of K21 (polynomials in b of degree <= 2 with coefficients in [-3, 3]) and their symbols (u, d)_P3;
\\ (b) a representative d' of the square class of d with v_P3(d') = 0;
\\ (c) the least k such that u c^2 = a^2 - d' b^2 has no solution modulo P3^k with a, b or c equal to 1
\\     (the normalisation that a valuation ring allows: divide by the coordinate of least valuation).
\\ Run from code/selmer-global-bound: gp -q dyadic_nonnorm_search.gp < /dev/null
default(parisizemax, 4*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../earlier-computations/bruin_form.gp");
read("../earlier-computations/richelot_data.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
d = Mod(RIN[1][5], K21);
d = d * denominator(content(lift(d)))^2;
nfK = nfinit([K21, [2, 7]]);
ram = idealfactor(nfK, rnfdisc(nfK, u^2 - lift(d))[1]);
P3 = 0; P6 = 0; for (j = 1, #ram~, if (ram[j, 1].e == 3, P3 = ram[j, 1]); if (ram[j, 1].e == 6, P6 = ram[j, 1]));
chk(P3 != 0 && P6 != 0, "the two ramified primes P3 (e = 3) and P6 (e = 6)");
print("K21 polynomial constant term ", polcoef(K21, 0, b), ", N(b) = ", norm(Mod(b, K21)));
\\ (a) small units
cands = List();
{
forvec(c = vector(3, i, [-3, 3]), my(el = Mod(c[1] + c[2] * b + c[3] * b^2, K21));
  if (c[2] == 0 && c[3] == 0, next);
  if (abs(norm(el)) == 1, listput(cands, [lift(el), nfhilbert(nfK, lift(el), lift(d), P3), nfhilbert(nfK, lift(el), lift(d), P6), nfeltsign(nfK, lift(el))])));
}
print("small units of K21 (degree <= 2, |coeff| <= 3): ", #cands);
foreach (cands, c, print("  ", c));
\\ (b) unit representative of d at P3: divide by the square of pi^(v/2), pi a uniformizer of P3 (from the two element form)
v3 = idealval(nfK, lift(d), P3);
pi3 = nfbasistoalg(nfK, P3.gen[2]);
chk(idealval(nfK, lift(pi3), P3) == 1, "pi3 is a uniformizer at P3");
dp = d / pi3^v3;
chk(idealval(nfK, lift(dp), P3) == 0, Str("d' = d / pi3^", v3, " is a unit at P3"));
chk(nfhilbert(nfK, lift(-1), lift(dp), P3) == nfhilbert(nfK, lift(-1), lift(d), P3), "same square class check (sanity)");
\\ (c) least k: residues modulo P3^k, represented by sum_{i < k} e_i pi3^i with e_i in {0, 1} (f = 1)
modpk(el, k) = el;   \\ test divisibility with idealval
zero_mod(el, k) = (el == 0) || idealval(nfK, lift(el), P3) >= k;
reps(k) = vector(2^k, n, my(bits = binary(n - 1), r = Mod(0, K21)); for (i = 1, #bits, r = 2 * r); sum(i = 0, k - 1, bittest(n - 1, i) * pi3^i));
leastk(uu, kmax) = {
  for (k = 1, kmax, my(R = reps(k), found = 0, cnt = 0);
    \\ normalisation: one of a, b, c equals 1
    for (ia = 1, #R, for (ib = 1, #R, if (found, break);
      my(A = R[ia], B = R[ib]);
      \\ c = 1
      if (zero_mod(uu - A^2 + dp * B^2, k), found = 1; cnt++);
      \\ a = 1 (A plays c)
      if (!found && zero_mod(uu * A^2 - 1 + dp * B^2, k), found = 1);
      \\ b = 1 (A plays a, B plays c)
      if (!found && zero_mod(uu * B^2 - A^2 + dp, k), found = 1)));
    printf("  k = %d: %s\n", k, if (found, "a normalised solution exists", "no normalised solution"));
    if (!found, return(k)));
  -1;
}
{
foreach (cands, c, if (c[2] == -1, my(uu = Mod(c[1], K21)); print("unit ", c[1], ": least k = ", leastk(uu, 9)); break));
}
quit;
