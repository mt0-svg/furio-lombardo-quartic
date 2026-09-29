\\ lattice_cert.gp: certified lattice data of the Selmer group Chabauty chain (see the paper).
\\ Ball arithmetic with proved error bounds (code/lib/pball.gp) in
\\ the completion K_v (completion_kv.gp); nothing below uses a heuristic precision estimate.
\\ For each twist k:
\\ (1) exact points: D_1..D_7 = [u_i, V_i] with u_i the exact local divisors of local_images_twist<k>_e3.bin (their x - T
\\     classes, which depend on u_i only, are the certified basis of J(K_v)/2J(K_v) of selmer_image_v.gp) and V_i the exact
\\     square root of f modulo u_i near the stored approximation (pbj_genuine); phi_a, phi_b exact over K21 (phi_known_lifts.gp);
\\ (2) logarithms log D_i, log phi_a, log phi_b as balls (pbj_log: group law with certified branches, tiny logarithm with
\\     the proved tail of Lemma T); two values of N as a known-answer test (they must agree within the balls);
\\ (3) Lambda exactly (Nakayama): with l_i the centres, if pi^M O^2 is contained in sum Z_2 l_i + pi^(M+3) O^2 and every
\\     log D_i is known modulo pi^(M+3), then pi^M O^2 is in Lambda and Lambda = sum Z_2 l_i + pi^M O^2; m_Lambda = the least m
\\     with pi^m O^2 in Lambda (exact test on the exact Lambda);
\\ (4) W = rho(sigma_v(Sel)) from the exact coordinates SelCoef (SEL/selmer_image_v_twist<k>.bin) and rho(D_i) = log D_i mod 2 Lambda;
\\     known-answer tests: rho(T) = 0, rho(phi_a), rho(phi_b) from the logarithms = from the x - T classes;
\\ (5) Gsat = (Q_2 log phi_a + Q_2 log phi_b) meet Lambda modulo 2^r Lambda with r = (precision of the coordinates of
\\     log phi_a, log phi_b in Lambda) - d2 (d2 the larger elementary divisor exponent; see the paper),
\\     pr : Lambda -> Lambda/Gsat, pr(W), and the classes e1 of pr(2^k c_1) at the known lifts (c_1 exact).
\\ Saves data/lattice_twist<k>.bin and prints a summary. Run from code/earlier-computations:
\\   gp -q lattice_cert.gp > lattice_cert.out
default(parisizemax, 5 * 10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("phi_known_lifts.gp"); read("pullback_known_lifts.gp");
chq(c, msg) = if (!c, error("check failed: ", msg));
nfK = nfinit([K21, [2, 7]]);
pr = [q | q <- idealprimedec(nfK, 2), q.e == 3][1];
read("completion_kv.gp");
MW = if (type(MW0) == "t_INT", MW0, 3000);
SEL = "data/";  \\ selmer_image_v_twist<k>.bin: [.., SelCoef, KnownCoef] written by selmer_image_v.gp (cache copied into the repository; content equals selmer_image_v.out)
NM = 4 * 3^2 * 5 * 7 * 11 * 13;
TGT = 150;  \\ target precision of the tiny logarithms
kvc(c) = if (type(c) == "t_COL", kv(nfbasistoalg(nfK, c)), kv(c));
kvxx(P) = { my(v = if (type(P) == "t_POL" && variable(P) == 'x, Vecrev(P), [P])); vector(#v, i, kvc(v[i])); }
\\ Q_2 coordinates on 1, pi, pi^2 of a ball: [centre coordinates, 2-adic precisions]
qco(l) = { my(L = lift(l[1])); [vector(3, i, polcoef(L, i - 1, PBV)), vector(3, i, ceil((l[2] - (i - 1)) / 3))]; }
lvec(L) = { my(a = qco(L[1]), c = qco(L[2])); [concat(a[1], c[1])~, concat(a[2], c[2])]; }
\\ the Z_2-lattice of the columns of G (rational, 2-adic denominators) plus pi^m O^2, as an integral HNF over Z after
\\ scaling by 2^sc (membership is tested 2-adically: odd denominators allowed)
pim(m) = matdiagonal(concat(vector(3, i, 2^max(0, ceil((m - (i - 1)) / 3))), vector(3, i, 2^max(0, ceil((m - (i - 1)) / 3)))));
lat(G, m) = { my(sc = denominator(G)); chq(sc == 2^valuation(sc, 2), "dyadic centres"); [mathnf(matconcat([G * sc, pim(m) * sc])), sc]; }
\\ reduction Z_(2) -> Z/2^j (entrywise; odd denominators)
red2(c, j) = {
  if (type(c) == "t_VEC" || type(c) == "t_COL" || type(c) == "t_MAT", return(apply(e -> red2(e, j), c)));
  chq(denominator(c) % 2 == 1, "red2: 2-integral");
  lift(Mod(numerator(c), 2^j) / denominator(c));
}
inlat(Lt, v) = { my(c = matsolve(Lt[1], v * Lt[2])); denominator(c) % 2 == 1; }
subl(Lt, m) = { my(P = pim(m)); for (j = 1, 6, if (!inlat(Lt, P[, j]), return(0))); 1; }
v2(c) = if (c == 0, oo, valuation(c, 2));
v2vec(v) = vecmin(apply(v2, Vec(v)));
f2rank(M) = matrank(Mod(M, 2));
f2in(W, v) = f2rank(matconcat([W, v])) == f2rank(W);

run(k) = {
  my(t0 = getabstime(), res = Map(), f, R, Ds, phis, Lphi, logs, logs2, prec, M, Lt, LtM, mL, H, Hi, co, RhoD, S, SC, KC, W);
  f = kvxx(subst(if (k == 0, F0, F1), t, 'x));
  chq(#f == 7, "deg f = 6");
  R = read(Str("local_images_twist", k, "_e3.bin"));
  \\ (1) exact points
  Ds = vector(#R[7], i, my(U = kvxx(R[7][i][1]), V0 = kvxx(R[7][i][2]), Vr, D);
    chq(U[3][1] == 1 && #U == 3, "u_i monic of degree 2");
    V0 = apply(c -> pb(c[1], MW), pbx_pad(V0, 2));
    Vr = pbj_refine(f, U, V0, 12);
    D = pbj_genuine(f, U, Vr); chq(D != 0, Str("D_", i, " is certified (Hensel)")); D);
  printf("k = %d: D_1..D_%d certified, precisions of V: %s (%d ms)\n", k, #Ds, vector(#Ds, i, pbj_prec(Ds[i])), getabstime() - t0);
  phis = [ph | ph <- PHI, ph[2] == k];
  Lphi = vector(2, j, my(U = subst(phis[j][4], t, 'x) * Mod(1, K21), V = subst(phis[j][5], t, 'x) * Mod(1, K21), uu, vv);
    uu = U / pollead(U); vv = V % uu; chq((vv^2 - subst(if (k == 0, F0, F1), t, 'x)) % uu == 0, "phi(x_i) is a point of J(K21)");
    [kvxx(uu), pbx_pad(kvxx(vv), 2)]);
  \\ (2) logarithms, two values of N
  my(lg = ((D, a) -> my(r = pbj_log(f, D, 2^a * NM, TGT)); r[1]), cmp);
  logs = vector(#Ds + 2, i, lg(if (i <= #Ds, Ds[i], Lphi[i - #Ds]), 4));
  logs2 = vector(#Ds + 2, i, lg(if (i <= #Ds, Ds[i], Lphi[i - #Ds]), 5));
  for (i = 1, #logs, for (c = 1, 2, chq(!pb_nz(pb_sub(logs[i][c], logs2[i][c])), Str("KAT: log with N = 2^4 NM and 2^5 NM agree (entry ", i, ")"))));
  prec = vector(#logs, i, min(logs[i][1][2], logs[i][2][2]));
  printf("  logarithms: precisions %s (D_1..D_7, phi_a, phi_b); N = 2^4 NM and 2^5 NM agree within the balls (%d ms)\n", prec, getabstime() - t0);
  \\ (3) Lambda
  co = vector(#logs, i, lvec(logs[i]));
  my(G = Mat(vector(#Ds, i, co[i][1])));
  M = 6; while (!subl(lat(G, M + 3), M), M++; chq(M < vecmin(prec[1 .. #Ds]) - 3, "Nakayama test within the precision"));
  chq(vecmin(prec[1 .. #Ds]) >= M + 3, "log D_i known modulo pi^(M+3)");
  LtM = lat(G, M);
  mL = M; while (mL > 0 && subl(LtM, mL - 1), mL--);
  H = LtM[1] / LtM[2]; Hi = H^-1;
  printf("  Lambda: pi^%d O^2 is contained in Lambda (Nakayama, certified); m_Lambda = %d; HNF diagonal 2-valuations %s\n", M, mL, vector(6, i, v2(H[i, i])));
  \\ coordinates in Lambda modulo 2^j, j = floor((prec - m_Lambda)/3)
  my(crd = (i -> my(c = Hi * co[i][1]); chq(denominator(c) % 2 == 1, "vector in Lambda"); [c, floor((prec[i] - mL) / 3)]));
  RhoD = red2(Mat(vector(#Ds, i, crd(i)[1])), 1);
  chq(f2rank(RhoD) == 6, "rho is onto Lambda/2Lambda");
  S = read(Str(SEL, "selmer_image_v_twist", k, ".bin")); SC = S[2]; KC = S[3];
  chq(RhoD * KC[, 1] % 2 == 0, "KAT: rho(T) = 0");
  W = lift(matimage(Mod(RhoD * SC, 2)));
  my(ya = crd(#Ds + 1), yb = crd(#Ds + 2));
  chq(red2(ya[1], 1) == RhoD * KC[, 2] % 2, "KAT: rho(phi_a) from the logarithm = from the x - T class");
  chq(red2(yb[1], 1) == RhoD * KC[, 3] % 2, "KAT: rho(phi_b) from the logarithm = from the x - T class");
  printf("  dim W = %d; coordinates of log phi_a, log phi_b in Lambda known modulo 2^%d, 2^%d\n", #W, ya[2], yb[2]);
  \\ (5) Gsat modulo 2^r Lambda
  my(jj = min(ya[2], yb[2]), Y = red2(matconcat([ya[1], yb[1]]), jj), sn = matsnf(Y, 1), U = sn[1], dd = sn[3], nzr, d1, d2, r, Gs, orow, prj, prW);
  nzr = [i | i <- [1 .. 6], dd[i, ] != 0];
  chq(#nzr == 2, "log phi_a, log phi_b independent modulo 2^j");
  my(dv = vecsort(apply(v2, [dd[nzr[1], ]* [1, 1]~, dd[nzr[2], ] * [1, 1]~])));
  d1 = dv[1]; d2 = dv[2];
  chq(d2 < jj, "elementary divisors below the precision");
  r = jj - d2;
  orow = [i | i <- [1 .. 6], i != nzr[1] && i != nzr[2]];
  prj = (v -> my(c = U * v); vector(4, i, c[orow[i]])~);
  prW = lift(matimage(Mod(Mat(vector(#W, j, prj(W[, j]))), 2)));
  printf("  <log phi_a, log phi_b>: elementary divisors 2^%d, 2^%d; Gsat and pr known modulo 2^%d Lambda; dim pr(W) = %d\n", d1, d2, r, #prW);
  \\ classes e1 at the known lifts: g0 proportional to c_1 = (w0_0, w1_0) (exact)
  my(E1 = List());
  foreach (phis, ph, my(ii = ph[1], TT = [tt | tt <- TINY, tt[1] == ii][1], c1 = [kv(Mod(TT[4][1], K21)), kv(Mod(TT[5][1], K21))], y1v = Hi * lvec(c1)[1], pv, nu1, e1);
    pv = prj(y1v); nu1 = v2vec(pv);
    my(tt = max(0, -v2vec(y1v)));
    chq(nu1 + 1 + tt <= r, "the class of pr(c_1) is within the precision of pr");
    chq(nu1 + 1 <= floor((min(c1[1][2], c1[2][2]) - mL) / 3), "the class of pr(c_1) is within the precision of the ball of c_1");
    e1 = red2(pv / 2^nu1, 1);
    listput(E1, [ii, nu1, e1~, f2in(prW, e1)]);
    printf("  x_%d: nu(pr c_1) = %d, class e1 = %s, e1 in pr(W): %d\n", ii, nu1, e1~, f2in(prW, e1)));
  mapput(res, "M", M); mapput(res, "mL", mL); mapput(res, "H", H); mapput(res, "W", W); mapput(res, "RhoD", RhoD);
  mapput(res, "U", U); mapput(res, "nzr", nzr); mapput(res, "orow", orow); mapput(res, "r", r); mapput(res, "prW", prW);
  mapput(res, "d", [d1, d2]); mapput(res, "E1", Vec(E1)); mapput(res, "logs", logs); mapput(res, "prec", prec); mapput(res, "E", PB_EP); mapput(res, "MW", MW);
  printf("  (%d ms)\n", getabstime() - t0);
  res;
}
{
  my(r0 = kv_init(MW));
  printf("K_v = Q_2(pi), E = %s; theta certified to pi^%d (v K21(theta) = %d, v K21'(theta) = %d); valuation KAT failures: %d\n", r0[1], r0[2], r0[3], r0[4], kv_kat(40));
  for (k = 0, 1, my(res = run(k)); system(Str("rm -f data/lattice_twist", k, ".bin")); writebin(Str("data/lattice_twist", k, ".bin"), res));
}
quit;
