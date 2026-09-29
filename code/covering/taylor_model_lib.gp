\\ taylor_model_lib.gp: the polynomial, quadratic algebra and Jacobian functions of code/lib/pball.gp, the Abel-Prym
\\ map of code/earlier-computations/centres_cert.gp (via centres_ball_lib.gp) and trevD, ttco of m4b_1_sizes.gp, with every ball operation
\\ replaced by the Taylor model operation of taylor_model_probe.gp (generated once by renaming the prefixes pb_, pbx_, pbB_, pbj_
\\ to tm_, tmx_, tmB_, tmj_, b<name> -> t<name>, and two edits: the monic test of tmx_divrem and pb_vc of a constant term).
tmx_pad(A, n) = if (#A >= n, A, concat(A, vector(n - #A, i, tm_zero)));
tmx_add(A, B) = { my(n = max(#A, #B), A2 = tmx_pad(A, n), B2 = tmx_pad(B, n)); vector(n, i, tm_add(A2[i], B2[i])); }
tmx_sub(A, B) = { my(n = max(#A, #B), A2 = tmx_pad(A, n), B2 = tmx_pad(B, n)); vector(n, i, tm_sub(A2[i], B2[i])); }
tmx_neg(A) = apply(tm_neg, A);
tmx_scal(b, A) = vector(#A, i, tm_mul(b, A[i]));
tmx_mul(A, B) = {
  if (#A == 0 || #B == 0, return([]));
  my(C = vector(#A + #B - 1, i, tm_zero));
  for (i = 1, #A, for (j = 1, #B, C[i + j - 1] = tm_add(C[i + j - 1], tm_mul(A[i], B[j]))));
  C;
}
\\ [Q, R] with A = Q U + R, U monic (its leading ball must be exactly 1: only its other coefficients are used)
tmx_divrem(A, U) = {
  my(n = #A, d = #U, R = A, Q);
  if (U[d][1][1] != 1, error("tmx_divrem: U is not monic"));
  if (n < d, return([[], tmx_pad(A, d - 1)]));
  Q = vector(n - d + 1);
  forstep (i = n, d, -1,
    my(q = R[i]); Q[i - d + 1] = q;
    for (j = 1, d - 1, R[i - d + j] = tm_sub(R[i - d + j], tm_mul(q, U[j])));
    R[i] = tm_zero);
  [Q, R[1 .. d - 1]];
}
tmx_eval(A, b) = { my(r = tm_zero); forstep (i = #A, 1, -1, r = tm_add(tm_mul(r, b), A[i])); r; }
tmx_val(A) = { my(m = PB_INF); foreach (A, c, m = min(m, pb_val(c))); m; }
tmB_add(A, B) = [tm_add(A[1], B[1]), tm_add(A[2], B[2])];
tmB_sub(A, B) = [tm_sub(A[1], B[1]), tm_sub(A[2], B[2])];
tmB_neg(A) = [tm_neg(A[1]), tm_neg(A[2])];
tmB_scal(b, A) = [tm_mul(b, A[1]), tm_mul(b, A[2])];
tmB_k(b) = [b, tm_zero];
\\ (a0 + a1 th)(b0 + b1 th), th^2 = -u1 th - u0
tmB_mul(A, B, U) = {
  my(p00 = tm_mul(A[1], B[1]), p11 = tm_mul(A[2], B[2]), p01 = tm_add(tm_mul(A[1], B[2]), tm_mul(A[2], B[1])));
  [tm_sub(p00, tm_mul(p11, U[1])), tm_sub(p01, tm_mul(p11, U[2]))];
}
tmB_norm(A, U) = tm_add(tm_sub(tm_mul(A[1], A[1]), tm_mul(tm_mul(A[1], A[2]), U[2])), tm_mul(tm_mul(A[2], A[2]), U[1]));
tmB_tr(A, U) = tm_sub(tm_scal(2, A[1]), tm_mul(A[2], U[2]));
\\ inverse: conj(a) / N(a), conj(a0 + a1 th) = (a0 - a1 u1) - a1 th
tmB_inv(A, U) = { my(Ni = tm_inv(tmB_norm(A, U))); [tm_mul(tm_sub(A[1], tm_mul(A[2], U[2])), Ni), tm_neg(tm_mul(A[2], Ni))]; }
tmB_div(A, B, U) = tmB_mul(A, tmB_inv(B, U), U);
tmB_fromx(P, U) = { my(R = tmx_divrem(tmx_pad(P, 2), U)[2]); [R[1], R[2]]; }
tmj_iszero(D) = #D[1] == 1;
\\ one reduction step: u monic of degree 4, v of degree <= 3, u | f - v^2 (exactly, for the enclosed point)
tmj_red(f, u, v) = {
  my(q = tmx_divrem(tmx_sub(f, tmx_mul(v, v)), u)[1], lc, li, u3);
  if (#q != 3, error("tmj_red: degrees"));
  lc = q[3]; if (!tm_nz(lc), error("tmj_red: lc(u3) is not certified nonzero"));
  li = tm_inv(lc); u3 = [tm_mul(q[1], li), tm_mul(q[2], li), tm_one];
  [u3, tmx_divrem(tmx_neg(tmx_pad(v, 4)), u3)[2]];
}
tmj_add(f, D1, D2) = {
  if (tmj_iszero(D1), return(D2)); if (tmj_iszero(D2), return(D1));
  my(u1 = D1[1], v1 = tmx_pad(D1[2], 2), u2 = D2[1], v2 = tmx_pad(D2[2], 2), c, k, v);
  c = [tm_sub(u1[1], u2[1]), tm_sub(u1[2], u2[2])];      \\ u1 mod u2 (Res(u2, u1) = N_B2(c))
  k = tmB_mul(tmB_sub(v2, v1), tmB_inv(c, u2), u2);       \\ (v2 - v1) / u1 mod u2
  v = tmx_add(v1, tmx_mul(u1, k));
  tmj_red(f, tmx_mul(u1, u2), v);
}
tmj_neg(D) = [D[1], tmx_neg(D[2])];
tqeval(QF, P) = { my(r = tm_zero); foreach (QF, m, my(e = m[2], t1 = m[1]); for (h = 1, 3, for (q = 1, e[h], t1 = tm_mul(t1, P[h]))); r = tm_add(r, t1)); r; }
tdot(A, B) = { my(r = tm_zero); for (i = 1, #A, r = tm_add(r, tm_mul(A[i], B[i]))); r; }
tmv(M, v) = vector(#M, i, tdot(M[i], v));
tquad(M, v) = tdot(v, tmv(M, v));
tdet3(A) = {
  my(t1 = tm_mul(A[1][1], tm_sub(tm_mul(A[2][2], A[3][3]), tm_mul(A[2][3], A[3][2]))),
     t2 = tm_mul(A[1][2], tm_sub(tm_mul(A[2][1], A[3][3]), tm_mul(A[2][3], A[3][1]))),
     t3 = tm_mul(A[1][3], tm_sub(tm_mul(A[2][1], A[3][2]), tm_mul(A[2][2], A[3][1]))));
  tm_add(tm_sub(t1, t2), t3);
}
\\ adjugate: adj[i][j] = (-1)^(i+j) minor(j, i)
tadj3(A) = {
  my(mn = ((r, c) -> my(R = [q | q <- [1 .. 3], q != r], C = [q | q <- [1 .. 3], q != c]); tm_sub(tm_mul(A[R[1]][C[1]], A[R[2]][C[2]]), tm_mul(A[R[1]][C[2]], A[R[2]][C[1]]))));
  vector(3, i, vector(3, j, my(m = mn(j, i)); if ((i + j) % 2, tm_neg(m), m)));
}
bapm_init(k) = {
  my(dl = Mod(if (k == 0, d0, d1), K21), S = apm_init(Q1 * Mod(1, K21), Q2 * Mod(1, K21), Q3 * Mod(1, K21), dl));
  my(Fk = if (k == 0, F0, F1)); chq(S[8] == Fk * Mod(1, K21), "the Prym curve of apm_init is F_k");
  [bmat(S[1]), bmat(S[2]), bmat(S[3]), bmat(S[4]), bmat(S[5]), bmat(S[6]), kv(dl), kvx(subst(Fk, t, 'x))];
}
tstar(A) = {
  my(B = vector(4, i, vector(4, j, tmB_k(tm_zero))));
  B[1][2] = A[3][4]; B[1][3] = A[4][2]; B[1][4] = A[2][3]; B[2][3] = A[1][4]; B[2][4] = A[3][1]; B[3][4] = A[1][2];
  for (i = 1, 4, for (j = 1, i - 1, B[i][j] = tmB_neg(B[j][i])));
  B;
}
tapm_phi(SB, P) = {
  my(J = vector(3, i, tmv(SB[3 + i], P)), best = 0, bv = PB_INF, cands = List(), T = 0, a0, tv = PB_INF, U, th, Mt, G, av, bw, A0, GA, SA, piv = 0, pv = PB_INF, Y);
  forsubset ([5, 3], cs, my(Bm = vector(3, i, vector(3, j, J[i][cs[j]])), dt = tdet3(Bm));
    if (tm_nz(dt) && pb_vc((dt[1])[1]) < bv, bv = pb_vc((dt[1])[1]); best = [Vec(cs), dt, Bm]));
  chq(best != 0, "phi: the tangent space is certified of dimension 1");
  my(cs = best[1], dt = best[2], ad = tadj3(best[3]), ncs = [q | q <- [1 .. 5], !setsearch(Set(cs), q)]);
  foreach (ncs, n, my(Tn = vector(5, i, tm_zero), Jn = vector(3, i, J[i][n]), sol = tmv(ad, Jn));
    Tn[n] = dt; for (i = 1, 3, Tn[cs[i]] = tm_neg(sol[i]));
    my(a = [tquad(SB[4], Tn), tquad(SB[5], Tn), tquad(SB[6], Tn)]);
    if (tm_nz(a[3]) && pb_vc((a[3][1])[1]) < tv, tv = pb_vc((a[3][1])[1]); T = Tn; a0 = a));
  chq(T != 0, "phi: a0_3 certified nonzero");
  my(i3 = tm_inv(a0[3])); U = [tm_mul(a0[1], i3), tm_mul(tm_scal(2, a0[2]), i3), tm_one];
  chq(tm_nz(tm_sub(tm_mul(U[2], U[2]), tm_scal(4, U[1]))), "phi: disc U certified nonzero (the ruling identity in B = K[t]/(U) is used only for U with distinct roots)");
  th = [tm_zero, tm_one];
  my(th2 = tmB_mul(th, th, U));
  Mt = vector(3, i, vector(3, j, tmB_add(tmB_add(tmB_k(SB[1][i][j]), tmB_scal(tm_scal(2, SB[2][i][j]), th)), tmB_scal(SB[3][i][j], th2))));
  G = vector(4, i, vector(4, j, if (i <= 3 && j <= 3, Mt[i][j], i == 4 && j == 4, tmB_k(tm_neg(SB[7])), tmB_k(tm_zero))));
  av = [tmB_k(P[1]), tmB_k(P[2]), tmB_k(P[3]), tmB_add(tmB_k(P[4]), tmB_scal(P[5], th))];
  bw = [tmB_k(T[1]), tmB_k(T[2]), tmB_k(T[3]), tmB_add(tmB_k(T[4]), tmB_scal(T[5], th))];
  A0 = vector(4, i, vector(4, j, tmB_sub(tmB_mul(av[i], bw[j], U), tmB_mul(bw[i], av[j], U))));
  my(bmm = ((X1, X2) -> vector(4, i, vector(4, j, my(r = tmB_k(tm_zero)); for (l = 1, 4, r = tmB_add(r, tmB_mul(X1[i][l], X2[l][j], U))); r))));
  GA = bmm(bmm(G, A0), G);
  SA = tstar(A0);
  for (i = 1, 4, for (j = i + 1, 4, my(nn = tmB_norm(SA[i][j], U)); if (tm_nz(nn) && pb_vc((nn[1])[1]) < pv, pv = pb_vc((nn[1])[1]); piv = [i, j])));
  chq(piv != 0, "phi: a pivot of star(A) certified invertible");
  Y = tmB_div(GA[piv[1]][piv[2]], SA[piv[1]][piv[2]], U);
  \\ known-answer checks (must contain 0): G A G - Y star(A) at every entry, and Y^2 - f(t) in B
  my(bad = 0); for (i = 1, 4, for (j = 1, 4, my(dd = tmB_sub(GA[i][j], tmB_mul(Y, SA[i][j], U))); if (tm_nz(dd[1]) || tm_nz(dd[2]), bad++)));
  my(fB = tmB_fromx(SB[8], U), dY = tmB_sub(tmB_mul(Y, Y, U), fB)); if (tm_nz(dY[1]) || tm_nz(dY[2]), bad++);
  chq(bad == 0, "phi: G A G = Y star(A) and Y^2 = f(t) within the balls");
  [U, [Y[1], Y[2]]];
}
trevD(D) = {
  my(U = D[1], V = tmx_pad(D[2], 2), ui, up, vp);
  chq(tm_nz(U[1]), "reversal: u(0) certified nonzero");
  ui = tm_inv(U[1]); up = [ui, tm_mul(U[2], ui), tm_one];
  vp = tmx_divrem([tm_zero, tm_zero, V[2], V[1]], up)[2];
  [up, tmx_pad(vp, 2)];
}
\\ E0 = [(X - a)^2, b + v1 (X - a)] on F, b^2 = F(a), v1 = F'(a) / (2 b)
ttco(S, a0) = { my(U = S[1]); [tm_add(U[2], tm_c(2 * a0)), tm_add(tm_add(U[1], tm_scal(a0, U[2])), tm_c(a0^2))]; }
