\\ exclusion_data.gp: exact data for the Lean certificates of lean/FurioLombardo/Discharge/M4Cert (HExcl of M4).
\\ The model of K_v is Q_2[x]/(E), E the Eisenstein cubic of code/earlier-computations/completion_kv.gp, pi = x; elements of
\\ Z[pi] are integer triples [a0, a1, a2]. Everything below is exact integer arithmetic modulo E and modulo
\\ powers of 2, the same computation the Lean kernel repeats:
\\ (1) theta0 = a triple with fQ(theta0) = 0 mod 2^KT and v_pi(fQ'(theta0)) = 17 (Hensel data of the embedding);
\\ (2) the zk coordinates (nfinit(K21).zk, the basis of M1's zkE) of the coefficients of Q1, Q2, Q3 and of
\\     delta0, delta1; the residues of their images modulo 2^n;
\\ (3) for every excluded box (disc, c, s) of M4 (FurioLombardo.M4.T0.excluded, T1.excluded): the least m
\\     such that, for every residue pair (Xr, Yr) modulo 2^m with Xr = c mod 2^s and F(disc point) = 0 mod
\\     2^(m+1), Q(p) * delta^(-1) modulo 2^(m+1) is not a square in (Z/2^(m+1))[pi]/(E), for Q = Q1 or Q3.
\\ Run from code/earlier-computations:  gp -q ../covering/exclusion_data.gp < /dev/null > ../covering/exclusion_data.out
default(parisizemax, 4*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
chq(c, msg) = if (!c, error("check failed: ", msg));
nfK = nfinit([K21, [2, 7]]);
pr = [q | q <- idealprimedec(nfK, 2), q.e == 3][1];
read("completion_kv.gp");
r = kv_init(300);
E = subst(r[1], 'x, 'X);
chq(E == 'X^3 + 37469486047374096441064*'X^2 + 16418729904282180494548*'X + 17325639337422721302482, "E");
\\ triples
tr(P) = { my(L = lift(Mod(P, E))); vector(3, i, polcoef(L, i - 1, 'X)); }
tp(v) = v[1] + v[2]*'X + v[3]*'X^2;
tmod(v, n) = vector(3, i, v[i] % 2^n);
tmul(a1, a2, n) = tmod(tr(tp(a1) * tp(a2)), n);
vpi(v) = { my(m = oo); for (i = 1, 3, if (v[i] != 0, m = min(m, 3 * valuation(v[i], 2) + i - 1))); m; }
\\ (1) theta0
KT = 40;
th = lift(KV_TH[1]); th3 = vector(3, i, polcoef(th, i - 1, PBV));
foreach (th3, c, chq(denominator(c) % 2 == 1, "theta coordinates 2-integral"));
th0 = vector(3, i, lift(Mod(th3[i], 2^KT)));
hornerT(L, v, n) = { my(r = [0, 0, 0]); forstep (i = #L, 1, -1, r = tmul(r, v, n); r[1] = (r[1] + L[i]) % 2^n); r; }
fL = Vecrev(K21);   \\ constant first
fT = hornerT(fL, th0, KT);
chq(fT == [0, 0, 0], "fQ(theta0) = 0 mod 2^KT");
dfL = Vecrev(deriv(K21));
dfT = hornerT(dfL, th0, KT);
print("theta0 = ", th0);
print("fQ'(theta0) mod 2^40 = ", dfT, "  v_pi = ", vpi(dfT));
\\ (2) zk coordinates and residues
Dz = 168168978404922092768;
zkNum = [Vecrev(nfK.zk[j] * Dz) | j <- [1 .. 21]];   \\ power basis numerators (constant first), length <= 21
foreach (zkNum, v, foreach (v, c, chq(denominator(c) == 1, "zkNum integral")));
chq(Dz == 2^5 * 5255280575153815399, "Dz");
Dodd = Dz / 32; DoddInv(n) = lift(Mod(1, 2^n) / Dodd);
zkco(c) = { my(v = nfalgtobasis(nfK, Mod(c, K21))); chq(denominator(v) == 1, "integral"); v~; };
\\ residue of sigma(zkE a) modulo 2^n: N_a(theta0) mod 2^(n+5), divided by 32, times Dodd^(-1)
resZK(av, n) = {
  my(NL = vector(21, k, sum(j = 1, 21, av[j] * if (k <= #zkNum[j], zkNum[j][k], 0))), v);
  v = hornerT(NL, th0, n + 5);
  foreach (v, c, chq(c % 32 == 0, "divisible by 32"));
  tmod(v / 32 * DoddInv(n), n);
}
\\ quadrics: coefficient of monomial x_i x_j (i <= j) of Q in (x, y, z)
VV = [x, y, z];
qcoef(Q, i, j) = { my(c); if (i == j, c = polcoef(polcoef(Q, 2, VV[i]), 0, VV[i]), c = polcoef(polcoef(Q, 1, VV[i]), 1, VV[j]));
  substvec(c, [x, y, z], [0, 0, 0]); }
QQ = [Q1, Q2, Q3];
\\ check the monomial extraction: rebuild each Q
for (q = 1, 3, chq(QQ[q] == sum(i = 1, 3, sum(j = i, 3, qcoef(QQ[q], i, j) * VV[i] * VV[j])), "Q rebuild"));
QZK = vector(3, q, vector(3, i, vector(3, j, if (i <= j, zkco(qcoef(QQ[q], i, j)), vector(21, k, 0)))));
DZK = [zkco(d0), zkco(d1)];
print("delta valuations at v: ", [nfeltval(nfK, d0, pr), nfeltval(nfK, d1, pr)]);
\\ inverse of delta modulo 2^n as a triple: solve by Newton in (Z/2^n)[pi]/(E)
tinv(a1, n) = { my(z = [lift(Mod(1, 2^n) / a1[1]), 0, 0], k = 1); chq(a1[1] % 2 == 1, "unit");
  for (it = 1, 3 * n + 3, z = tmod(tr(tp(z) * (2 - tp(a1) * tp(z))), n)); chq(tmul(z, a1, n) == [1, 0, 0], "inverse"); z; }
\\ discs of p21_37: [chart, a0, b0]; chart 1: (a0 + 2X, b0 + 2Y, 1); chart 2: (a0 + 2X, 1, b0 + 2Y)
DISCS = [[1, 0, 0], [1, 1, 0], [1, 1, 1], [2, 0, 0], [2, 1, 0]];
dpt(d, Xr, Yr) = { my(D = DISCS[d]); if (D[1] == 1, [D[2] + 2 * Xr, D[3] + 2 * Yr, 1], [D[2] + 2 * Xr, 1, D[3] + 2 * Yr]); }
Fq(p) = substvec(x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3, [x, y, z], p);
\\ squares of (Z/2^n)[pi]/(E), as a map
SQ = Map();
squares(n) = { if (mapisdefined(SQ, n), return(mapget(SQ, n)));
  my(S = Map()); forvec (v = vectorv(3, i, [0, 2^n - 1]), mapput(S, tmul(v~, v~, n), 1)); mapput(SQ, n, S); S; }
qres(QR, p, n) = { my(r = [0, 0, 0]); for (i = 1, 3, for (j = i, 3, r = tmod(r + tmul(QR[i][j], [p[i] * p[j], 0, 0], n), n))); r; }
BOXES = [[[5, 0, 1], [4, 3, 2], [4, 1, 2], [4, 2, 2], [4, 0, 2], [3, 3, 2], [3, 1, 2], [3, 2, 2], [3, 0, 2], [2, 1, 1], [2, 0, 1]], [[5, 1, 1], [5, 0, 1], [4, 3, 2], [4, 1, 2], [4, 2, 2], [4, 0, 2], [3, 3, 2], [3, 1, 2], [3, 2, 2], [2, 0, 1], [1, 1, 1], [1, 0, 1]]];
boxcert(k, bx, q, m) = {
  my(n = m + 1, QR = vector(3, i, vector(3, j, resZK(QZK[q][i][j], n))), di = tinv(resZK(DZK[k + 1], n), n), S = squares(n), cnt = 0, d = bx[1]);
  for (Xr = 0, 2^m - 1, if (Xr % 2^bx[3] != bx[2] % 2^bx[3], next);
    for (Yr = 0, 2^m - 1, my(p = dpt(d, Xr, Yr)); if (Fq(p) % 2^n != 0, next); cnt++;
      my(qq = tmul(qres(QR, p, n), di, n)); if (mapisdefined(S, qq), return(-1))));
  cnt;
}
{for (k = 0, 1,
  foreach (BOXES[k + 1], bx,
    my(done = 0);
    for (m = 2, 5, if (done, break); foreach ([1, 3], q, if (done, break); my(c = boxcert(k, bx, q, m)); if (c >= 0, printf("twist %d box %s: Q%d, m = %d, %d residue points\n", k, bx, q, m, c); done = 1)));
    if (!done, printf("twist %d box %s: NO CERTIFICATE up to m = 5\n", k, bx))));}
quit;
