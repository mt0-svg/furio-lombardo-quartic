\\ leading_class_explore.gp: the leading class of pr(lambda) at points of C(Q_2) (EXPLORATORY).
\\ For a point P of C(Q_2) in a disc of discs_q2.txt that lifts to D_delta(K_v) (v the place above 2 with e = 3):
\\ phi(x_P) = [U, V] by the approximate Abel-Prym map of p21_33_disc2.gp (certified K_v-divisor), its logarithm by
\\ genus2_log_kv.gp, lambda = log phi(x_P) - log phi(x_a), the coordinates of lambda in Lambda (chabauty_lattice.gp,
\\ SEL/lattice_k<k>.bin), pr(lambda) in Lambda/Gsat, nu = its 2-divisibility and its leading class; condition (iii)
\\ fails at P iff the leading class lies in pr(W). The sign of the lift does not matter
\\ (phi o iota = -phi and pr(log phi(x_a)) = 0).
\\ Consistency test near a known point P_i (tau = x - x(P_i)): lambda(P) - (log phi(x_i) - log phi(x_a)) against the
\\ tiny integral sum c_m tau^m of pullback_known_lifts.gp (an independent code path: global series against local group law).
\\ Usage: set JOBS = [[k, disc index, X, i or -1], ...] before reading, or use the default list below.
\\ Run from code/earlier-computations: gp -q leading_class_explore.gp > leading_class_explore.out
if (type(NOQUIT) != "t_INT", default(parisizemax, 5*10^9); default(nbthreads, 1));  \\ (a library read must not change parisizemax: it aborts the read)
[t, x, y, z, X, u, w, a, s, b];
read("abel_prym_lib.gp");
read("bruin_form.gp"); read("richelot_data.gp"); read("phi_known_lifts.gp"); read("pullback_known_lifts.gp");
read("../lib/richelot.gp"); read("../lib/td2loc.gp");
read("discs_q2.txt");
chq(c, msg) = if (!c, error("check failed: ", msg));
MRED = if (type(MRED0) == "t_INT", MRED0, 240);  \\ working precision pr^MRED (MRED0 overrides)
read("genus2_log_kv.gp");
SEL = "/tmp/k21c/sel/";
Fq = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
FA = [substvec(Fq, [z], [1]), substvec(Fq, [y], [1]), substvec(Fq, [x], [1])];
VA = [[x, y], [x, z], [y, z]];
NP = if (type(NP0) == "t_INT", NP0, 90);  \\ 2-adic precision of the points (NP0 overrides)
LSQ = if (type(LSQ0) == "t_INT", LSQ0, 200);  \\ precision pr^LSQ of the local square roots r, s (LSQ0 overrides)
discpt(d, X0) = {
  my(ch = d[1], c1 = d[2] + 2^d[4] * X0, F1, c = d[3] + O(2^(NP + 10)), it = 0);
  F1 = subst(FA[ch], VA[ch][1], c1);
  while (valuation(subst(F1, VA[ch][2], c), 2) < NP, c -= subst(F1, VA[ch][2], c) / subst(deriv(F1, VA[ch][2]), VA[ch][2], c); it++; chq(it < 200, "Newton"));
  c = truncate(c);
  if (ch == 1, [c1, c, 1], ch == 2, [c1, 1, c], [1, c1, c]);
}
nfK = nfinit([K21, [2, 7]]);
pr = [q | q <- idealprimedec(nfK, 2), q.e == 3][1];
NM = 4 * 3^2 * 5 * 7 * 11 * 13;
LV = td2_lvinit(nfK, pr, 150, 60); mapput(LV, "IM", idealpow(nfK, pr, MRED));
locsqrt(aa, M) = {
  my(zv, r);
  if (aa == 0 || !nfislocalpower(nfK, pr, aa, 2), return(0));
  zv = rich_lv_map(LV, aa);
  r = rich_lv_lift(LV, rich_lv_sqrt(LV, zv), idealpow(nfK, pr, M));
  chq(nfeltval(nfK, r^2 - aa, pr) >= M, "local square root to the requested precision");
  r;
}
apm_ruling_ap(S, P, T, t0) = {
  my(G, Mt, a0, b0, A0, GA, SA, i0 = 0, j0 = 0);
  Mt = S[1] + 2*t0*S[2] + t0^2*S[3];
  G = matconcat([Mt, matrix(3, 1); matrix(1, 3), Mat(-S[7])]);
  a0 = [P[1], P[2], P[3], P[4] + t0*P[5]]; b0 = [T[1], T[2], T[3], T[4] + t0*T[5]];
  A0 = a0~ * b0 - b0~ * a0;
  GA = G * A0 * G; SA = apm_star(A0);
  for (i = 1, 4, for (j = i + 1, 4, if (i0 == 0 && SA[i,j] != 0, i0 = i; j0 = j)));
  chq(i0, "nondegenerate projected plane");
  GA[i0, j0] / SA[i0, j0];
}
apm_phi_ap(S, P) = {
  my(Jm = matrix(3, 5, i, j, (S[3 + i] * P~)[j]), K0 = matker(Jm), T, a0, U, Y1, V, vs, jm);
  chq(#K0 == 2, "tangent space of dimension 1");
  T = K0[, 1]~; if (matrank(Mat([P~, T~])) < 2, T = K0[, 2]~);
  vs = vector(5, j, if (T[j] == 0, oo, nfeltval(nfK, T[j], pr))); jm = 1; for (j = 2, 5, if (vs[j] < vs[jm], jm = j));
  T = apply(c -> redK(LV, c), T / T[jm]);
  a0 = vector(3, i, T * S[3 + i] * T~);
  chq(a0[3] != 0, "no point of phi(P) above t = infinity");
  U = redKx(LV, t^2 + 2*a0[2]/a0[3]*t + a0[1]/a0[3]);
  Y1 = apm_ruling_ap(S, P, T, Mod(t, U));
  V = redKx(LV, lift(Y1));
  [U, V];
}
\\ Q_2-coordinates on 1, PI, PI^2 (as in chabauty_lattice.gp)
qcoords(aa, P, PI) = {
  my(c = [0, 0, 0], rem = aa, m, q, r, pw = [1, PI, PI^2], mold = -oo);
  while (rem != 0 && (m = kval(LV, rem)) < 3 * P,
    chq(m > mold, "qcoords: valuation increases"); mold = m;
    q = m \ 3; r = m % 3; c[r + 1] += 2^q; rem = redK(LV, rem - 2^q * pw[r + 1]));
  apply(ci -> if (denominator(ci) == 1, ci % 2^P, ci), c);
}
logvec(l, P, PI) = concat(qcoords(l[1], P, PI), qcoords(l[2], P, PI))~;
v2(c) = if (c == 0, oo, valuation(c, 2));
v2vec(v) = vecmin(apply(v2, Vec(v)));
f2in(W, v) = matrank(Mod(matconcat([W, v]), 2)) == matrank(Mod(W, 2));
PREC2 = 60;
CTX = vector(2);
ctx(k) = {
  if (CTX[k + 1] != 0, return(CTX[k + 1]));
  my(Lt = read(Str(SEL, "lattice_k", k, ".bin")), f = 0); if (type(Lt) == "t_VEC", Lt = Lt[#Lt]); my(f = subst(if (k == 0, F0, F1), t, 'x) * Mod(1, K21), dl = Mod(if (k == 0, d0, d1), K21),
     S = apm_init(Q1 * Mod(1, K21), Q2 * Mod(1, K21), Q3 * Mod(1, K21), dl), H = mapget(Lt, "H"), U = mapget(Lt, "U"), nzr = mapget(Lt, "nzr"),
     orow = [i | i <- [1 .. 6], i != nzr[1] && i != nzr[2]], phis = [ph | ph <- PHI, ph[2] == k], Lk);
  \\ logs of the known points at this working precision
  Lk = vector(2, j, my(Uu = subst(phis[j][4], t, 'x) * Mod(1, K21), Vv = subst(phis[j][5], t, 'x) * Mod(1, K21), uu = Uu / pollead(Uu));
      [phis[j][1], j2_log(LV, f, [uu, Vv % uu], 2^4 * NM, 800)]);
  CTX[k + 1] = [f, dl, S, H^-1, U, orow, mapget(Lt, "prW"), Lk, mapget(Lt, "PI")];
  CTX[k + 1];
}
\\ lambda at the point P (projective, integers) for twist k: [status, nu, leading class, in pr(W), lambda]
lambda_at(k, P) = {
  my(C = ctx(k), f = C[1], dl = C[2], S = C[3], Hi = C[4], U = C[5], orow = C[6], prW = C[7], La = C[8][1][2], PI = C[9],
     q, rr, ss, Pd, ph2, Ux, Vx, D, L, lam, yv, pv, nu, lc);
  q = vector(3, j, substvec([Q1, Q2, Q3][j], [x, y, z], P) * Mod(1, K21));
  rr = locsqrt(q[1] / dl, LSQ);
  if (rr != 0, ss = q[2] / (dl * rr),
    ss = locsqrt(q[3] / dl, LSQ); if (ss == 0, return(["no lift"])); rr = q[2] / (dl * ss));
  Pd = concat(P * Mod(1, K21), [redK(LV, rr), redK(LV, ss)]);
  ph2 = iferr(apm_phi_ap(S, Pd), E, return([Str("phi failed: ", E)]));
  Ux = td2_Kx(nfK, subst(lift(ph2[1]), t, 'x)); Vx = td2_Kx(nfK, subst(lift(ph2[2]), t, 'x));
  if (!td2_certify(nfK, pr, f, Ux, Vx), return(["not certified"]));
  D = j2_refine(LV, f, [Ux, Vx % Ux]);
  L = iferr(j2_log(LV, f, D, 2^4 * NM, 800), E, return([Str("log failed: ", E)]));
  lam = L - La;
  yv = Hi * logvec(lam, PREC2, PI);
  chq(denominator(yv) % 2 == 1, "lambda in Lambda");
  pv = vector(4, i, (U * yv)[orow[i]])~;
  nu = v2vec(pv);
  if (nu == oo, return(["ok", oo, 0, 0, L, D]));
  lc = apply(c -> c % 2, pv / 2^nu);
  ["ok", nu, lc~, f2in(prW, lc), L, D];
}
{JOBS = if (type(JOBS) == "t_VEC", JOBS,
  concat([[[0, 5, X0, -1] | X0 <- [1, 3, 5, 7, 9, 11, 13, 15]],
          [[0, 1, X0, 0] | X0 <- [2, 4, 8, 16, 6, 10]],
          [[0, 1, X0, 2] | X0 <- [3, 5, 9, 17]],
          [[1, 3, X0, 1] | X0 <- [4, 8, 12, 16]],
          [[1, 2, X0, 3] | X0 <- [1, 3, 5, 7, 11, 15]]]));}
{
  my(t0 = getabstime());
  foreach (JOBS, jb, my(k = jb[1], d = DISCS[jb[2]], P = discpt(d, jb[3]), r = lambda_at(k, P));
    if (r[1] != "ok", printf("k = %d, disc %d, X = %d: %s (%d ms)\n", k, jb[2], jb[3], r[1], getabstime() - t0); next);
    my(extra = "");
    if (jb[4] >= 0,
      \\ series check: lambda(P) - lambda(x_i) against sum c_m tau^m, tau = x/z - x(P_i)
      my(i = jb[4], C = ctx(k), Li = [l | l <- C[8], l[1] == i], TT = [tt | tt <- TINY, tt[1] == i][1], Pk = [[0, 0, 1], [1, 1, 1], [2, 0, 1], [-1, 0, 1]][i + 1], tau, ser, dif);
      if (#Li == 0, extra = "  (known point of the other twist)",
        tau = P[1] / P[3] - Pk[1];
        ser = sum(m = 1, #TT[4], [Mod(TT[4][m], K21), Mod(TT[5][m], K21)] * tau^m / m);
        dif = (r[5] - Li[1][2]) - ser;
        \\ the lift in the series is the one near x_i; the computed lift may be iota of it: compare both signs
        my(dif2 = (-r[5] - Li[1][2]) - ser, vd = vecmin(apply(c -> kval(LV, c), dif)), vd2 = vecmin(apply(c -> kval(LV, c), dif2)));
        extra = Str("  series check at tau = ", tau, " (v_2 = ", valuation(tau, 2), "): v(difference) ", max(vd, vd2), " (22 terms; v(lambda) ", vecmin(apply(c -> kval(LV, c), r[5] - Li[1][2])), ")")));
    printf("k = %d, disc %d, X = %d, P = (%s : %s : %s) mod 2^10: nu = %s, leading class %s, in pr(W): %d%s (%d ms)\n", k, jb[2], jb[3],
           P[1] % 1024, P[2] % 1024, P[3] % 1024, r[2], r[3], r[4], extra, getabstime() - t0));
}
if (type(NOQUIT) != "t_INT", quit);
