\\ small_units_symbols.gp: small units of K21 in the (LLL reduced) integral basis, their symbols at P3, P6 and signs.
\\ Run from code/selmer-global-bound: gp -q small_units_symbols.gp < /dev/null
default(parisizemax, 4*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../earlier-computations/bruin_form.gp");
read("../earlier-computations/richelot_data.gp");
d = Mod(RIN[1][5], K21);
d = d * denominator(content(lift(d)))^2;
nfK = nfinit([K21, [2, 7]]);
ram = idealfactor(nfK, rnfdisc(nfK, u^2 - lift(d))[1]);
P3 = 0; P6 = 0; for (j = 1, #ram~, if (ram[j, 1].e == 3, P3 = ram[j, 1]); if (ram[j, 1].e == 6, P6 = ram[j, 1]));
zk = nfK.zk;
print("integral basis: ", #zk, " elements; max height of numerators ", vecmax(apply(p -> if (type(p) == "t_POL", vecmax(abs(Vec(p * denominator(content(p))))), abs(p)), zk)));
found = List();
{
for (i = 1, 21, for (j = i, 21, for (k = j, 21, forvec(c = [[-2, 2], [-2, 2], [-2, 2]],
  my(el = c[1] * zk[i] + if (j > i, c[2] * zk[j], 0) + if (k > j, c[3] * zk[k], 0));
  if (el == 0 || type(el) != "t_POL", next);
  if (abs(norm(Mod(el, K21))) == 1,
    my(h3 = nfhilbert(nfK, el, lift(d), P3));
    if (h3 == -1, listput(found, [el, [i, j, k], c, nfeltsign(nfK, el)]))))));
  if (#found >= 40, break));
}
print("units with (u, d)_P3 = -1 found: ", #found);
for (n = 1, min(#found, 40), print("  ", found[n][2], " ", found[n][3], " signs ", found[n][4], " : ", found[n][1]));
quit;
