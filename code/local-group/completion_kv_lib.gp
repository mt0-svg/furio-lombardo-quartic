\\ completion_kv_lib.gp: the completion K_v = Q_2[X]/(E) of M4Cert (lean/FurioLombardo/Discharge/M4Cert) in PARI, two ways:
\\ (1) the exact integer triple arithmetic of the Lean checks (mulZ, hornerZ, zres from theta0 modulo 2^28, modT,
\\     sqTest, lowOK), copied from code/genus2-curves/local_facts_v_data.gp (WP5 of the M3a discharge);
\\ (2) an independent p-adic model (sigma(theta) = theta* to 2^240) with valuations vpi in pi units (v(2) = 3), square
\\     tests ksq and square roots ksqrt, integer triples trip(e, M) of elements of O_v modulo 2^M.
\\ The caller reads ../descent/descent_data_lib.gp first (K21, nf, zkNum, Dz, zkc) and sets parisizemax, nbthreads.
chq(c, msg) = if (!c, error("check failed: ", msg));
red(g) = lift(Mod(1, K21) * g);
den(v) = denominator(content(v));
zkl(e) = { my(v = zkc(e)); chq(den(v) == 1, "non integral zk coordinates"); v~ };
pr = [P | P <- idealprimedec(nf, 2), P.e == 3][1];
lsq(a) = nfislocalpower(nf, pr, lift(Mod(a, K21)), 2);
vl(a) = if (a == 0, oo, nfeltval(nf, a, pr));
chq(Dz == 168168978404922092768, "Dz of M1");
E0 = 17325639337422721302482; E1 = 16418729904282180494548; E2 = 37469486047374096441064;
mulZ(a, c) = { my(c0 = a[1]*c[1], c1 = a[1]*c[2] + a[2]*c[1], c2 = a[1]*c[3] + a[2]*c[2] + a[3]*c[1],
  c3 = a[2]*c[3] + a[3]*c[2], c4 = a[3]*c[3], d3 = c3 - E2*c4);
  [c0 - E0*d3, c1 - E1*d3 - E0*c4, c2 - E2*d3 - E1*c4] };
hornerZ(v, L) = { my(r = [0, 0, 0]); forstep (i = #L, 1, -1, r = [L[i], 0, 0] + mulZ(v, r)); r };
th0 = [163180991353, 3522151726, 560510631928];
combo(l) = vector(21, i, sum(j = 1, 21, l[j] * zkNum[j][i]));
uOdd = 91745367; Dodd = 5255280575153815399; chq(Dz == 32 * Dodd, "Dodd");
zresOK(l) = { my(N = hornerZ(th0, combo(l))); N[1] % 32 == 0 && N[2] % 32 == 0 && N[3] % 32 == 0 };
zres(l) = mulZ(hornerZ(th0, combo(l)) / 32, [uOdd, 0, 0]);
modT(v, n) = vector(3, i, v[i] % 2^n);
dvdT(v, m) = v[1] % m == 0 && v[2] % m == 0 && v[3] % m == 0;
pvT(k) = { my(v = [1, 0, 0]); for (i = 1, k, v = mulZ(v, [0, 1, 0])); v };
SQ = Map(); forvec (s = vector(3, i, [0, 7]), mapput(SQ, modT(mulZ(s, s), 3), 1));
chq(#SQ == 28, "28 squares modulo 8");
sQok(l, j, o, oi, P) = zresOK(l) && P + j <= 28 && P >= 1 && dvdT(modT(zres(l), P + j), 2^j) && modT(mulZ([o, 0, 0], [oi, 0, 0]), P) == [1, 0, 0];
sQres(l, j, oi, P) = mulZ(modT(zres(l), P + j) / 2^j, [oi, 0, 0]);
sqTest(t, i, j, e, P) = { my(u = modT(mulZ(modT(t, P), pvT(2 * i)), P));
  dvdT(u, 2^(2*j + e)) && 2*j + e + 3 <= P && !mapisdefined(SQ, modT(u / 2^(2*j + e), 3)) };
lowOK(b, s) = b[1] % 2^(s + 1) != 0 || b[2] % 2^(s + 1) != 0 || b[3] % 2^(s + 1) != 0;
splitm(m) = { my(j = valuation(m, 2)); [j, m / 2^j] };
oinv(o) = lift(Mod(1, 2^28) / o);
PR = 3000;  \\ the power basis coefficients of the D_i data have large 2-adic denominators
EE = 'X^3 + E2*'X^2 + E1*'X + E0;
pa(c) = c + O(2^PR);
kv(v) = Mod(pa(v[1]) + pa(v[2])*'X + pa(v[3])*'X^2, EE);
cfk(e, i) = polcoef(lift(e), i, 'X);
v2(c) = if (c == 0, 10^6, valuation(c, 2));
vpi(e) = min(3 * v2(cfk(e, 0)), min(3 * v2(cfk(e, 1)) + 1, 3 * v2(cfk(e, 2)) + 2));
fK = Pol(Vec(K21), 'X);
th = kv(th0);
for (i = 1, 12, th = th - subst(fK, 'X, th) / subst(deriv(fK, 'X), 'X, th));
chq(vpi(subst(fK, 'X, th)) > 6000, "theta*");
chq(vpi(th - kv(th0)) >= 99, "theta* close to theta0");
sg(a) = subst(Pol(lift(Mod(a, K21)), 'b), 'b, th);
PIK = Mod('X, EE);
usq(u) = { forvec(s = [[0, 3], [0, 3], [0, 3]], my(e = u - kv(s)^2); if (e == 0 || vpi(e) >= 7, return(1))); 0 };
ksq(w) = { if (w == 0, return(1)); my(v = vpi(w)); if (v % 2, return(0)); usq(w / PIK^v) };
ksqrt(w) = { my(v = vpi(w), u, s = 0); chq(v % 2 == 0, "odd valuation"); u = w / PIK^v;
  forvec(t = [[0, 3], [0, 3], [0, 3]], my(e = u - kv(t)^2); if (e == 0 || vpi(e) >= 7, s = kv(t); break));
  chq(s != 0, "unit not a square");
  for (i = 1, 12, s = (s + u / s) / 2); PIK^(v / 2) * s };
trip(e, M) = { chq(vpi(e) >= 0, "integral"); vector(3, i, lift(Mod(truncate(cfk(e, i - 1)), 2^M))) };
scal(v) = { for (j = 0, 6, for (i = 0, 2, if (v + 2*i - 6*j == 0 || v + 2*i - 6*j == 2, return([i, j])))); error("scaling") };
