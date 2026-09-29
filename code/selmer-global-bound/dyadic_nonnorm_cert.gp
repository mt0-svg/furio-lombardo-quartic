\\ dyadic_nonnorm_cert.gp: the dyadic non-norm certificate for L/K21 as data for Lean.
\\ R = O_v / pi^6 = (Z/4)[pi]/(E(pi)) (v the place of K21 above 2 with e = 3, K_v = Q_2(pi), E Eisenstein; completion_kv.gp).
\\ U = image of u = zk[19] - 1 and D = image of d' = d / PI^18 (PI = pr.gen[2], mapped to a uniformizer) in R.
\\ Check, by arithmetic in R only (independent of the idealval search of dyadic_least_precision.gp): no a, b, c in R with one of
\\ them equal to 1 satisfies U c^2 = a^2 - D b^2. Output: E, U, D as coefficient vectors on 1, pi, pi^2 (entries mod 4).
\\ Run from code/selmer-global-bound: gp -q dyadic_nonnorm_cert.gp < /dev/null
default(parisizemax, 4*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../earlier-computations/bruin_form.gp");
read("../earlier-computations/richelot_data.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
d = Mod(RIN[1][5], K21);
d = d * denominator(content(lift(d)))^2;
nfK = nfinit([K21, [2, 7]]);
ram = idealfactor(nfK, rnfdisc(nfK, u^2 - lift(d))[1]);
pr = 0; for (j = 1, #ram~, if (ram[j, 1].e == 3, pr = ram[j, 1]));
PI = nfbasistoalg(nfK, pr.gen[2]);
v3 = idealval(nfK, lift(d), pr);
read("../earlier-computations/completion_kv.gp");
kvres = kv_init(200);
E = kvres[1];
print("E = ", E, " (Eisenstein at 2), root precision ", kvres[2]);
uu = Mod(nfK.zk[19] - 1, K21);
ku = kv(uu); kd = kv(d); kpi = kv(PI);
chk(pb_vc(kpi[1]) == 1, "PI maps to a uniformizer");
kpv = pb_one; for (i = 1, v3, kpv = pb_mul(kpv, kpi));
kdp = pb_div(kd, kpv);
chk(kdp[2] >= 6 && ku[2] >= 6, Str("precision of the images: u ", ku[2], ", d' ", kdp[2]));
\\ coefficients on 1, pi, pi^2 of an element of Z_2[pi], reduced mod 4 (valid when the centre has v >= 0 coefficients)
co4(c) = { my(L = lift(c)); vector(3, i, my(q = polcoef(L, i - 1)); if (denominator(q) % 2 == 0, error("non integral coefficient")); lift(Mod(q, 4))); }
U = co4(ku[1]); D = co4(kdp[1]);
print("U = ", U, "; D = ", D);
\\ arithmetic in R = (Z/4)[pi]/(E): elements as vectors [a0, a1, a2] mod 4
Er = Mod(E, 4);
rmul(p, q) = { my(r = lift(lift(Mod(Pol(Mod(Vecrev(p), 4), 'x) * Pol(Mod(Vecrev(q), 4), 'x), subst(Er, variable(E), 'x))))); vector(3, i, lift(Mod(polcoef(r, i - 1, 'x), 4))); }
radd(p, q) = vector(3, i, (p[i] + q[i]) % 4);
rneg(p) = vector(3, i, (4 - p[i]) % 4);
one = [1, 0, 0];
R = List(); forvec(c = [[0, 3], [0, 3], [0, 3]], listput(R, c)); R = Vec(R);
chk(#R == 64, "R has 64 elements");
sq = vector(64, i, rmul(R[i], R[i]));
Usq = vector(64, i, rmul(U, sq[i]));
Dsq = vector(64, i, rmul(D, sq[i]));
isone(i) = (R[i] == one);
cnt = 0;
{
for (ia = 1, 64, for (ib = 1, 64, for (ic = 1, 64,
  if (isone(ia) || isone(ib) || isone(ic),
    if (Usq[ic] == radd(sq[ia], rneg(Dsq[ib])), cnt++)))));
}
chk(cnt == 0, "no (a, b, c) in R^3 with a, b or c equal to 1 and U c^2 = a^2 - D b^2");
\\ sanity: the same check with u replaced by 1 (a norm) must find solutions
cnt1 = 0;
{
for (ia = 1, 64, for (ib = 1, 64, for (ic = 1, 64,
  if (isone(ia) || isone(ib) || isone(ic), if (sq[ic] == radd(sq[ia], rneg(Dsq[ib])), cnt1++)))));
}
chk(cnt1 > 0, Str("known answer: with u = 1 there are ", cnt1, " normalised solutions"));
print("E coefficients mod 4 (constant first): ", vector(4, i, lift(Mod(polcoef(E, i - 1), 4))));
quit;
