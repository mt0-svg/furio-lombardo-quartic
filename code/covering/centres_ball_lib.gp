\\ centres_ball_lib.gp: the setup and the ball arithmetic Abel-Prym map of code/earlier-computations/centres_cert.gp (lines copied verbatim,
\\ the part before its section "(4), (5) the centres"), for the probes of the box inputs.
\\ Read from code/earlier-computations (relative paths).
[t, x, y, z, X, u, w, a, s, b];
read("abel_prym_lib.gp");
read("bruin_form.gp"); read("discs_q2.txt");
chq(c, msg) = if (!c, error("check failed: ", msg));
nfK = nfinit([K21, [2, 7]]);
pr = [q | q <- idealprimedec(nfK, 2), q.e == 3][1];
read("completion_kv.gp");
MW = if (type(MW0) == "t_INT", MW0, 3000);
NP = if (type(NP0) == "t_INT", NP0, 1100);
NM = 4 * 3^2 * 5 * 7 * 11 * 13;
TGT = 150;
Fq = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
FA = [substvec(Fq, [z], [1]), substvec(Fq, [y], [1]), substvec(Fq, [x], [1])];
VA = [[x, y], [x, z], [y, z]];
kvc(c) = if (type(c) == "t_COL", kv(nfbasistoalg(nfK, c)), kv(c));
qco(l) = { my(L = lift(l[1])); [vector(3, i, polcoef(L, i - 1, PBV)), vector(3, i, ceil((l[2] - (i - 1)) / 3))]; }
lvec(L) = { my(a = qco(L[1]), c = qco(L[2])); [concat(a[1], c[1])~, concat(a[2], c[2])]; }
v2(c) = if (c == 0, oo, valuation(c, 2));
v2vec(v) = vecmin(apply(v2, Vec(v)));
f2rank(M) = matrank(Mod(M, 2));
f2in(W, v) = f2rank(matconcat([W, v])) == f2rank(W);
red2(c, j) = {
  if (type(c) == "t_VEC" || type(c) == "t_COL" || type(c) == "t_MAT", return(apply(e -> red2(e, j), c)));
  chq(denominator(c) % 2 == 1, "red2: 2-integral");
  lift(Mod(numerator(c), 2^j) / denominator(c));
}
startswith(s, p) = my(a = Vecsmall(s), bb = Vecsmall(p)); #a >= #bb && a[1 .. #bb] == bb;
field(s, key) = {
  my(A = Vecsmall(s), B = Vecsmall(key), p = 0, e); for (i = 1, #A - #B + 1, if (A[i .. i + #B - 1] == B, p = i + #B; break));
  if (!p, return(oo)); e = p; while (e <= #A && A[e] != 44, e++); eval(Strchr(A[p .. e - 1]));
}

\\ ---------------------------------------------------------------- (1) the point
cpoint(d, X0) = {
  my(ch = d[1], c1 = d[2] + 2^d[4] * X0, var = VA[ch][2], F1 = subst(FA[ch], VA[ch][1], c1), c = d[3] + O(2^(NP + 10)), it = 0, Fv, Dv, kP, cb);
  while (valuation(subst(F1, var, c), 2) < NP, c -= subst(F1, var, c) / subst(deriv(F1, var), var, c); it++; chq(it < 400, "Newton"));
  c = truncate(c);
  Fv = valuation(subst(F1, var, c), 2); Dv = valuation(subst(deriv(F1, var), var, c), 2);
  chq(Fv > 2 * Dv, "Hensel for the point");
  kP = Fv - Dv;
  chq(kP >= d[4] && (c - d[3]) % 2^d[4] == 0, "the root lies in the disc");
  cb = pb(c, 3 * kP);
  [if (ch == 1, [pb_c(c1), cb, pb_one], ch == 2, [pb_c(c1), pb_one, cb], [pb_one, pb_c(c1), cb]), kP];
}
\\ ternary quadratic form with K21 coefficients: [[coefficient ball, [ex, ey, ez]], ...]
qform(Q) = {
  my(L = List());
  for (i = 0, 2, for (j = 0, 2 - i, my(l = 2 - i - j, c = polcoef(polcoef(polcoef(Q, i, x), j, y), l, z));
    if (c != 0, listput(L, [kv(Mod(c, K21)), [i, j, l]]))));
  Vec(L);
}
qeval(QF, P) = { my(r = pb_zero); foreach (QF, m, my(e = m[2], t1 = m[1]); for (h = 1, 3, for (q = 1, e[h], t1 = pb_mul(t1, P[h]))); r = pb_add(r, t1)); r; }

\\ ---------------------------------------------------------------- (2) square roots from scratch
\\ a certified square root of the ball al (nonzero), or 0 if al is not a square (search modulo pi^7 fails)
csqrt(al) = {
  my(va = pb_vc(al[1]), bet, r0 = 0, r);
  if (!pb_nz(al) || va % 2, return(0));
  bet = pb_mul(al, pb_c(Mod(PBV, PB_EP)^(-va)));
  forvec (ac = vector(6, i, [0, 1]), my(c = Mod(1 + sum(i = 1, 6, ac[i] * PBV^i), PB_EP)); if (pb_vc(bet[1] - c^2) >= 7, r0 = c; break));
  if (r0 == 0, return(0));
  r = pb_sqrt_newton(bet, r0, 14);
  r = Mod(PBV, PB_EP)^(va / 2) * r;
  pb_sqrt_cert(al, r);
}

\\ ---------------------------------------------------------------- (3) the Abel-Prym map in ball arithmetic
bmat(M) = vector(#M~, i, vector(#M, j, kvc(M[i, j])));
bdot(A, B) = { my(r = pb_zero); for (i = 1, #A, r = pb_add(r, pb_mul(A[i], B[i]))); r; }
bmv(M, v) = vector(#M, i, bdot(M[i], v));
bquad(M, v) = bdot(v, bmv(M, v));
bdet3(A) = {
  my(t1 = pb_mul(A[1][1], pb_sub(pb_mul(A[2][2], A[3][3]), pb_mul(A[2][3], A[3][2]))),
     t2 = pb_mul(A[1][2], pb_sub(pb_mul(A[2][1], A[3][3]), pb_mul(A[2][3], A[3][1]))),
     t3 = pb_mul(A[1][3], pb_sub(pb_mul(A[2][1], A[3][2]), pb_mul(A[2][2], A[3][1]))));
  pb_add(pb_sub(t1, t2), t3);
}
\\ adjugate: adj[i][j] = (-1)^(i+j) minor(j, i)
badj3(A) = {
  my(mn = ((r, c) -> my(R = [q | q <- [1 .. 3], q != r], C = [q | q <- [1 .. 3], q != c]); pb_sub(pb_mul(A[R[1]][C[1]], A[R[2]][C[2]]), pb_mul(A[R[1]][C[2]], A[R[2]][C[1]]))));
  vector(3, i, vector(3, j, my(m = mn(j, i)); if ((i + j) % 2, pb_neg(m), m)));
}
bapm_init(k) = {
  my(dl = Mod(if (k == 0, d0, d1), K21), S = apm_init(Q1 * Mod(1, K21), Q2 * Mod(1, K21), Q3 * Mod(1, K21), dl));
  my(Fk = if (k == 0, F0, F1)); chq(S[8] == Fk * Mod(1, K21), "the Prym curve of apm_init is F_k");
  [bmat(S[1]), bmat(S[2]), bmat(S[3]), bmat(S[4]), bmat(S[5]), bmat(S[6]), kv(dl), kvx(subst(Fk, t, 'x))];
}
bstar(A) = {
  my(B = vector(4, i, vector(4, j, pbB_k(pb_zero))));
  B[1][2] = A[3][4]; B[1][3] = A[4][2]; B[1][4] = A[2][3]; B[2][3] = A[1][4]; B[2][4] = A[3][1]; B[3][4] = A[1][2];
  for (i = 1, 4, for (j = 1, i - 1, B[i][j] = pbB_neg(B[j][i])));
  B;
}
bapm_phi(SB, P) = {
  my(J = vector(3, i, bmv(SB[3 + i], P)), best = 0, bv = PB_INF, cands = List(), T = 0, a0, tv = PB_INF, U, th, Mt, G, av, bw, A0, GA, SA, piv = 0, pv = PB_INF, Y);
  forsubset ([5, 3], cs, my(Bm = vector(3, i, vector(3, j, J[i][cs[j]])), dt = bdet3(Bm));
    if (pb_nz(dt) && pb_vc(dt[1]) < bv, bv = pb_vc(dt[1]); best = [Vec(cs), dt, Bm]));
  chq(best != 0, "phi: the tangent space is certified of dimension 1");
  my(cs = best[1], dt = best[2], ad = badj3(best[3]), ncs = [q | q <- [1 .. 5], !setsearch(Set(cs), q)]);
  foreach (ncs, n, my(Tn = vector(5, i, pb_zero), Jn = vector(3, i, J[i][n]), sol = bmv(ad, Jn));
    Tn[n] = dt; for (i = 1, 3, Tn[cs[i]] = pb_neg(sol[i]));
    my(a = [bquad(SB[4], Tn), bquad(SB[5], Tn), bquad(SB[6], Tn)]);
    if (pb_nz(a[3]) && pb_vc(a[3][1]) < tv, tv = pb_vc(a[3][1]); T = Tn; a0 = a));
  chq(T != 0, "phi: a0_3 certified nonzero");
  my(i3 = pb_inv(a0[3])); U = [pb_mul(a0[1], i3), pb_mul(pb_scal(2, a0[2]), i3), pb_one];
  chq(pb_nz(pb_sub(pb_mul(U[2], U[2]), pb_scal(4, U[1]))), "phi: disc U certified nonzero (the ruling identity in B = K[t]/(U) is used only for U with distinct roots)");
  th = [pb_zero, pb_one];
  my(th2 = pbB_mul(th, th, U));
  Mt = vector(3, i, vector(3, j, pbB_add(pbB_add(pbB_k(SB[1][i][j]), pbB_scal(pb_scal(2, SB[2][i][j]), th)), pbB_scal(SB[3][i][j], th2))));
  G = vector(4, i, vector(4, j, if (i <= 3 && j <= 3, Mt[i][j], i == 4 && j == 4, pbB_k(pb_neg(SB[7])), pbB_k(pb_zero))));
  av = [pbB_k(P[1]), pbB_k(P[2]), pbB_k(P[3]), pbB_add(pbB_k(P[4]), pbB_scal(P[5], th))];
  bw = [pbB_k(T[1]), pbB_k(T[2]), pbB_k(T[3]), pbB_add(pbB_k(T[4]), pbB_scal(T[5], th))];
  A0 = vector(4, i, vector(4, j, pbB_sub(pbB_mul(av[i], bw[j], U), pbB_mul(bw[i], av[j], U))));
  my(bmm = ((X1, X2) -> vector(4, i, vector(4, j, my(r = pbB_k(pb_zero)); for (l = 1, 4, r = pbB_add(r, pbB_mul(X1[i][l], X2[l][j], U))); r))));
  GA = bmm(bmm(G, A0), G);
  SA = bstar(A0);
  for (i = 1, 4, for (j = i + 1, 4, my(nn = pbB_norm(SA[i][j], U)); if (pb_nz(nn) && pb_vc(nn[1]) < pv, pv = pb_vc(nn[1]); piv = [i, j])));
  chq(piv != 0, "phi: a pivot of star(A) certified invertible");
  Y = pbB_div(GA[piv[1]][piv[2]], SA[piv[1]][piv[2]], U);
  \\ known-answer checks (must contain 0): G A G - Y star(A) at every entry, and Y^2 - f(t) in B
  my(bad = 0); for (i = 1, 4, for (j = 1, 4, my(dd = pbB_sub(GA[i][j], pbB_mul(Y, SA[i][j], U))); if (pb_nz(dd[1]) || pb_nz(dd[2]), bad++)));
  my(fB = pbB_fromx(SB[8], U), dY = pbB_sub(pbB_mul(Y, Y, U), fB)); if (pb_nz(dY[1]) || pb_nz(dY[2]), bad++);
  chq(bad == 0, "phi: G A G = Y star(A) and Y^2 = f(t) within the balls");
  [U, [Y[1], Y[2]]];
}
