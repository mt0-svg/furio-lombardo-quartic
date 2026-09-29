\\ chart_lib.gp: shared setup for the "Concrete" part of R7.
\\ K21 = Q[b]/(K21(b)) (code/earlier-computations/bruin_form.gp, Lean: AdjoinRoot fQ, theta = class of X = b);
\\ nf = nfinit(K21) and its integral basis zk (M1's zkE; Dz, zkNum as in code/descent/descent_data_lib.gp);
\\ the twists f_k = -delta_k det(M1 + 2t M2 + t^2 M3) (k = 0, 1) and fRev_k = t^6 f_k(1/t) (Lean: fRev k);
\\ the T3 arithmetic of M4Cert (Z[pi]/(E), coordinates on 1, pi, pi^2) and zres (Lean: M4Cert.zres),
\\ the residue modulo 2^n of sigma(zkE a) computed from theta0 exactly as the Lean kernel does.
\\ The caller sets parisizemax and nbthreads and runs from code/local-group.
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
chq(c, msg) = if (!c, error("check failed: ", msg));
nf = nfinit(K21);
zk = nf.zk;
Dz = lcm(vector(21, j, denominator(content(zk[j]))));
chq(Dz == 168168978404922092768, "Dz as in Lean M1/DataField.lean");
zkNum = vector(21, j, Vecrev(zk[j] * Dz, 21));
zkc(e) = nfalgtobasis(nf, lift(Mod(e, K21)));
zkr(v) = nfbasistoalg(nf, if (type(v) == "t_VEC", v~, v));
zkl(e) = { my(v = zkc(e)); chq(denominator(v) == 1, "integral zk coordinates"); v~ };
red(g) = lift(Mod(1, K21) * g);
\\ ---- the twists (as in code/genus2-curves/bruin_data.gp) ----
mons2 = [[2,0,0], [1,1,0], [1,0,1], [0,2,0], [0,1,1], [0,0,2]];
cf(Q, i, j, k) = polcoef(polcoef(polcoef(Q, i, x), j, y), k, z);
coefs2(Q) = vector(6, j, Mod(cf(Q, mons2[j][1], mons2[j][2], mons2[j][3]), K21));
Qc = vector(3, i, coefs2([Q1, Q2, Q3][i]));
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
MM = vector(3, i, Msym(Qc[i]));
dd = [d0, d1];
fk = vector(2, k, red(-dd[k] * matdet(MM[1] + 2*t*MM[2] + t^2*MM[3])));
for (k = 1, 2, chq(red(fk[k] - [F0, F1][k]) == 0, "f_k = F_k of bruin_form.gp"));
frev = vector(2, k, polrecip(fk[k]));
for (k = 1, 2, chq(poldegree(frev[k], t) == 6, "degree of fRev"));
\\ FnData of Lean (DataBruin.lean): FnD[k][j+1] = zk coordinates of 4 * coefficient of t^j of f_k
FnD = vector(2, k, vector(7, j, zkl(4 * polcoef(fk[k], j - 1, t))));
\\ ---- the place v and T3 arithmetic (as in code/covering/exclusion_residues_data.gp) ----
pr = [q | q <- idealprimedec(nf, 2), q.e == 3][1];
PI = nfbasistoalg(nf, pr.gen[2]);
vl(e) = if (e == 0, oo, nfeltval(nf, e, pr));
EE = 'X^3 + 37469486047374096441064*'X^2 + 16418729904282180494548*'X + 17325639337422721302482;
tr(P) = { my(L = lift(Mod(P, EE))); vector(3, i, polcoef(L, i - 1, 'X)); }
tp(v) = v[1] + v[2]*'X + v[3]*'X^2;
tmod(v, n) = vector(3, i, v[i] % 2^n);
tmul(a1, a2, n) = tmod(tr(tp(a1) * tp(a2)), n);
th0 = [163180991353, 3522151726, 560510631928];
hornerT(L, v, n) = { my(r = [0, 0, 0]); forstep (i = #L, 1, -1, r = tmul(r, v, n); r[1] = (r[1] + L[i]) % 2^n); r; }
chq(hornerT(Vecrev(K21), th0, 40) == [0, 0, 0], "theta0");
Dodd = Dz / 32; chq(Dodd % 2 == 1, "Dodd odd");
uOdd = lift(Mod(1, 2^28) / Dodd);
chq(uOdd == 91745367, "uOdd as in Lean M4Cert/DataRes.lean");
\\ combo a zkNum (Lean Kron.combo), then zres a mod 2^n (n <= 28), with the Div32 check (Lean zresOK)
comboL(av) = vector(21, k, sum(j = 1, 21, av[j] * zkNum[j][k]));
resZK(av, n) = {
  my(v = hornerT(comboL(av), th0, n + 5));
  foreach (v, c, chq(c % 32 == 0, "zresOK: divisible by 32"));
  tmod(v / 32 * uOdd, n);
}
\\ valuation at v of a residue triple known modulo 2^n (oo if zero modulo 2^n)
tval(r, n) = { my(m = oo); for (i = 1, 3, if (r[i] % 2^n != 0, m = min(m, 3 * valuation(r[i] % 2^n, 2) + i - 1))); m; }
\\ place check: sigma(PI) has valuation 1
chq(tval(resZK(zkl(PI), 10), 10) == 1, "sigma is the place pr");
