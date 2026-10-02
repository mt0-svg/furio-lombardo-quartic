\\ redacted for the release: paths of the development workspace, which is not shipped
\\ pball.gp: ball arithmetic with proved error bounds in a totally ramified extension K = Q_p(pi) of Q_p, and on top
\\ of it the group law and the logarithm of the Jacobian of a genus 2 curve y^2 = f(x) (deg f = 6) over K.
\\
\\ Field. pi is a root of an Eisenstein polynomial E of degree e over Q, in the variable PBV (created by pb_init with
\\ varlower, so it has lower priority than every variable in use). v = v_pi, v(p) = e.
\\ Ball. A ball is [c, m]: c a t_POLMOD modulo E with rational coefficients (the centre), m an integer (the precision);
\\ it stands for the set c + pi^m O_K. Precisions are capped at PB_MW (a ball [c, PB_MW] around an exact c is
\\ still correct). Every function below returns a ball that contains the exact result of the operation for all
\\ inputs taken in the input balls (the "enclosure property"). The rules, with va = v(centre a) (PB_INF if a = 0):
\\   sum      [a + b, min(ma, mb)]
\\   product  [a b, min(va + mb, vb + ma, ma + mb)]       (ab - AB = a(b - B) + B... expanded, see pb_mul)
\\   inverse  [1/a, ma - 2 va], only when va < ma (then v(A) = va for every A in the ball; else an error)
\\ and centres are truncated to their precision (pb_red changes the centre by an element of pi^m O_K).
\\ Polynomials over balls: vectors of balls, lowest degree first. Division with remainder only by monic
\\ polynomials whose leading coefficient is exactly 1. Quadratic algebras B = K[x]/(U), U = x^2 + u1 x + u0 monic
\\ (ball coefficients): elements [a0, a1] = a0 + a1 th. For a in B, the values of a at the two roots of U (the two
\\ K-algebra maps B -> C_p when disc U != 0) are the roots of X^2 - Tr(a) X + N(a), so each has valuation at least
\\ min(v Tr(a), v N(a) / 2) (pbB_val, a proved lower bound over both embeddings).
\\
\\ Jacobian (deg f = 6, genus 2). Points: [U, V] with U monic of degree 2, deg V <= 1, U | f - V^2 exactly for the
\\ exact point enclosed, standing for [P1 + P2 - Dinf] (P_i = (x_i, V(x_i)), U(x_i) = 0, Dinf = inf+ + inf-);
\\ the origin is [[1], []]. Addition and doubling are Cantor's composition and one reduction step (the generic case):
\\ every branch condition (u1, u2 coprime; v1 prime to
\\ u1; lc(u3) != 0) is certified on the balls, so the enclosed exact computation takes the same branch; otherwise an
\\ error is raised (choose another addition chain).
\\ Logarithm for (dx/y, x dx/y). For D = [P1 + P2 - Dinf] close to the origin, D ~ P2 - iota(P1) and
\\   log D = int_{iota P1}^{P2} (1, x) dx / y = -(1/y1) int_0^s (x1 + z)^k (1 + E(z))^(-1/2) dz,
\\ s = x2 - x1, E(z) = f(x1 + z)/f(x1) - 1 = sum_{j=1..6} E_j z^j, computed in B = K[th]/(U) (th = x1, x2 = -u1 - th).
\\ With e_j = E_j s^j and h_n = g_n s^n (g = (1 + E)^(-1/2) = sum g_n z^n): 2 n h_n = - sum_j (2(n - j) + j) e_j h_{n-j},
\\ h_0 = 1, and int_0^s g dz = sum h_n s/(n+1), int_0^s (x1 + z) g dz = sum h_n (x1 s/(n+1) + s^2/(n+2)).
\\ Proved tail (Lemma T): let c = min_j (lower bound of v(e_j) over
\\ both embeddings) and c2 = 2 v(2) (= 2e for p = 2, 0 for p odd). If c > c2, then in every embedding
\\ v(h_n) >= ceil(n/6) (c - c2) for all n >= 1. Proof: in the variable w = z/s, sum h_n w^n = (1 + eps(w))^(-1/2),
\\ eps = sum e_j w^j of degree <= 6 without constant term; the coefficient of w^n is sum_{k = ceil(n/6)..n}
\\ binom(-1/2, k) [w^n] eps^k, with v(binom(-1/2, k)) = e (v_p(binom(2k, k)) - 2k v_p(2)) >= -k c2 and
\\ v([w^n] eps^k) >= k c (Gauss norm). The same bound shows the series converges on the closed disc |z| <= |s|,
\\ where y = -y1 (1 + E)^(1/2) is analytic; the integral along that disc is the abelian logarithm (Coleman; for p = 2
\\ Katz, Rabinoff, Zureick-Brown, the (ftc) property on an open disc containing the closed one).
\\ The series is summed to n0, the least n with a tail bound above the target, and the tail bound enters the result.
\\ Branch: the continuation of y from iota(P1) to x2 is -y1 / g(s) = +-y2; the exact value Z = y1 + y2 g(s) is 0 for
\\ the right branch and 2 y1 for the wrong one (in each embedding); it is certified 0 when the lower bound of v(Z)
\\ exceeds v(2) + max v(y1) (max over embeddings, bounded by v N(y1) - pbB_val(y1)).
\\ The logarithm lies in K^2 and equals its value at either root; it is recovered as Tr/2 (loss v(2)).
\\ Chart at infinity: X = 1/x, Y = y/x^3, F(X) = X^6 f(1/X); [u, v] -> [X^2 + (u1/u0) X + 1/u0, (v0 X^3 + v1 X^2) mod u'],
\\ and (dx/y, x dx/y) = (-X dX/Y, -dX/Y), so log = (-l'_2, -l'_1). log D = log(N D) / N in general.
\\
\\ Interface: pb_init(p, E, mw); pb(c, m), pb_c(a), pb_add, pb_sub, pb_neg, pb_mul, pb_inv, pb_div, pb_val, pb_nz,
\\ pb_vc; pbx_* (polynomials), pbB_* (quadratic algebras), pbj_add, pbj_dbl, pbj_mul, pbj_tinylog, pbj_log,
\\ pbj_genuine (a certified exact point of J(K) near an approximate [U, V]), pb_sqrt (certified square root).

pb_init(p, E, mw) = {
  PBV = varlower("pb");
  PB_P = p; PB_EP = subst(E, variable(E), PBV); PB_e = poldegree(PB_EP); PB_MW = mw; PB_INF = 10^9;
  if (pollead(PB_EP) != 1 || polcoef(PB_EP, 0) % p != 0 || valuation(polcoef(PB_EP, 0), p) != 1, error("pb_init: E is not Eisenstein at p"));
  for (i = 0, PB_e - 1, if (valuation(polcoef(PB_EP, i), p) < 1, error("pb_init: E is not Eisenstein at p")));
  PB_C2 = if (p == 2, 2 * PB_e, 0);
  pb_zero = [Mod(0, PB_EP), PB_MW]; pb_one = [Mod(1, PB_EP), PB_MW];
}
\\ exact valuation of a centre (PB_INF for 0)
pb_vc(c) = {
  my(L = if (type(c) == "t_POLMOD", lift(c), c), m = PB_INF);
  if (L == 0, return(PB_INF));
  if (type(L) != "t_POL", return(PB_e * valuation(L, PB_P)));
  for (i = 0, poldegree(L, PBV), my(a = polcoef(L, i, PBV)); if (a != 0, m = min(m, PB_e * valuation(a, PB_P) + i)));
  m;
}
\\ a rational number r with v_p(a - r) >= E and denominator a power of p
pb_tr(a, E) = {
  if (a == 0, return(0));
  my(j = max(0, -valuation(a, PB_P)), d, M);
  if (E + j <= 0, return(0));
  d = denominator(a) / PB_P^j; M = PB_P^(E + j);
  lift(Mod(numerator(a), M) / d) / PB_P^j;
}
\\ centre truncated modulo pi^m (changes it by an element of pi^m O_K)
pb_red(c, m) = {
  my(L = if (type(c) == "t_POLMOD", lift(c), c), R = 0);
  if (type(L) != "t_POL", return(Mod(pb_tr(L, ceil(m / PB_e)), PB_EP)));
  for (i = 0, poldegree(L, PBV), R += pb_tr(polcoef(L, i, PBV), ceil((m - i) / PB_e)) * PBV^i);
  Mod(R, PB_EP);
}
pb(c, m) = my(mm = min(m, PB_MW)); [pb_red(Mod(c, PB_EP), mm), mm];
pb_c(a) = pb(a, PB_MW);
pb_add(x, y) = pb(x[1] + y[1], min(x[2], y[2]));
pb_sub(x, y) = pb(x[1] - y[1], min(x[2], y[2]));
pb_neg(x) = [-x[1], x[2]];
\\ AB - ab = a (B - b) + b (A - a) + (A - a)(B - b)
pb_mul(x, y) = my(va = pb_vc(x[1]), vb = pb_vc(y[1])); pb(x[1] * y[1], min(min(va + y[2], vb + x[2]), x[2] + y[2]));
\\ 1/A - 1/a = (a - A)/(a A), v(A) = va
pb_inv(x) = my(va = pb_vc(x[1])); if (va >= x[2], error("pb_inv: the ball contains 0")); pb(1 / x[1], x[2] - 2 * va);
pb_div(x, y) = pb_mul(x, pb_inv(y));
pb_scal(r, x) = pb_mul(pb_c(r), x);
\\ lower bound of the valuation of every element of the ball
pb_val(x) = min(pb_vc(x[1]), x[2]);
\\ the ball does not contain 0 (then every element has valuation pb_vc(x[1]))
pb_nz(x) = pb_vc(x[1]) < x[2];
pb_str(x) = Str("[v ", if (pb_vc(x[1]) >= PB_INF, "oo", pb_vc(x[1])), ", prec ", x[2], "]");

\\ ---------------------------------------------------------------- polynomials (vectors of balls, lowest degree first)
pbx_c(P) = { my(v = if (type(P) == "t_POL", Vecrev(P), [P])); vector(#v, i, pb_c(v[i])); }
pbx_pad(A, n) = if (#A >= n, A, concat(A, vector(n - #A, i, pb_zero)));
pbx_add(A, B) = { my(n = max(#A, #B), A2 = pbx_pad(A, n), B2 = pbx_pad(B, n)); vector(n, i, pb_add(A2[i], B2[i])); }
pbx_sub(A, B) = { my(n = max(#A, #B), A2 = pbx_pad(A, n), B2 = pbx_pad(B, n)); vector(n, i, pb_sub(A2[i], B2[i])); }
pbx_neg(A) = apply(pb_neg, A);
pbx_scal(b, A) = vector(#A, i, pb_mul(b, A[i]));
pbx_mul(A, B) = {
  if (#A == 0 || #B == 0, return([]));
  my(C = vector(#A + #B - 1, i, pb_zero));
  for (i = 1, #A, for (j = 1, #B, C[i + j - 1] = pb_add(C[i + j - 1], pb_mul(A[i], B[j]))));
  C;
}
\\ [Q, R] with A = Q U + R, U monic (its leading ball must be exactly 1: only its other coefficients are used)
pbx_divrem(A, U) = {
  my(n = #A, d = #U, R = A, Q);
  if (U[d][1] != 1, error("pbx_divrem: U is not monic"));
  if (n < d, return([[], pbx_pad(A, d - 1)]));
  Q = vector(n - d + 1);
  forstep (i = n, d, -1,
    my(q = R[i]); Q[i - d + 1] = q;
    for (j = 1, d - 1, R[i - d + j] = pb_sub(R[i - d + j], pb_mul(q, U[j])));
    R[i] = pb_zero);
  [Q, R[1 .. d - 1]];
}
pbx_eval(A, b) = { my(r = pb_zero); forstep (i = #A, 1, -1, r = pb_add(pb_mul(r, b), A[i])); r; }
pbx_val(A) = { my(m = PB_INF); foreach (A, c, m = min(m, pb_val(c))); m; }

\\ ---------------------------------------------------------------- quadratic algebras B = K[x]/(U), U = [u0, u1, 1]
pbB_add(A, B) = [pb_add(A[1], B[1]), pb_add(A[2], B[2])];
pbB_sub(A, B) = [pb_sub(A[1], B[1]), pb_sub(A[2], B[2])];
pbB_neg(A) = [pb_neg(A[1]), pb_neg(A[2])];
pbB_scal(b, A) = [pb_mul(b, A[1]), pb_mul(b, A[2])];
pbB_k(b) = [b, pb_zero];
\\ (a0 + a1 th)(b0 + b1 th), th^2 = -u1 th - u0
pbB_mul(A, B, U) = {
  my(p00 = pb_mul(A[1], B[1]), p11 = pb_mul(A[2], B[2]), p01 = pb_add(pb_mul(A[1], B[2]), pb_mul(A[2], B[1])));
  [pb_sub(p00, pb_mul(p11, U[1])), pb_sub(p01, pb_mul(p11, U[2]))];
}
pbB_norm(A, U) = pb_add(pb_sub(pb_mul(A[1], A[1]), pb_mul(pb_mul(A[1], A[2]), U[2])), pb_mul(pb_mul(A[2], A[2]), U[1]));
pbB_tr(A, U) = pb_sub(pb_scal(2, A[1]), pb_mul(A[2], U[2]));
\\ inverse: conj(a) / N(a), conj(a0 + a1 th) = (a0 - a1 u1) - a1 th
pbB_inv(A, U) = { my(Ni = pb_inv(pbB_norm(A, U))); [pb_mul(pb_sub(A[1], pb_mul(A[2], U[2])), Ni), pb_neg(pb_mul(A[2], Ni))]; }
pbB_div(A, B, U) = pbB_mul(A, pbB_inv(B, U), U);
pbB_pow(A, n, U) = { my(R = pbB_k(pb_one)); for (i = 1, n, R = pbB_mul(R, A, U)); R; }
\\ proved lower bound of v(a(root)) over both roots of U
pbB_val(A, U) = min(pb_val(pbB_tr(A, U)), pb_val(pbB_norm(A, U)) / 2);
\\ proved upper bound of v(a(root)) over both roots (needs N(a) certified nonzero)
pbB_vmax(A, U) = { my(N = pbB_norm(A, U)); if (!pb_nz(N), error("pbB_vmax: N(a) not certified nonzero")); pb_vc(N[1]) - pbB_val(A, U); }
\\ a polynomial reduced modulo U, as an element of B
pbB_fromx(P, U) = { my(R = pbx_divrem(pbx_pad(P, 2), U)[2]); [R[1], R[2]]; }
pbB_evalx(P, A, U) = { my(r = pbB_k(pb_zero)); forstep (i = #P, 1, -1, r = pbB_add(pbB_mul(r, A, U), pbB_k(P[i]))); r; }

\\ ---------------------------------------------------------------- square roots
\\ certified square root of the ball x from an approximation r0 (any centre): if x / r0^2 = 1 + eps with
\\ v(eps) > c2 for every element of the ball, the exact square roots of the elements of x are +-r0 (1 + eps)^(1/2), and
\\ v((1 + eps)^(1/2) - 1) >= v(eps) - v(2); returns the ball around r0 (one of the two signs), or 0 when not certified
pb_sqrt_cert(x, r0) = {
  my(r0b = pb(r0, PB_MW), vr = pb_vc(r0b[1]), eps = pb_val(pb_sub(x, pb_mul(r0b, r0b))) - 2 * vr);
  if (eps <= PB_C2, return(0));
  pb(r0b[1], vr + eps - if (PB_P == 2, PB_e, 0));
}
\\ approximate square root by Newton (centres only; certification by pb_sqrt_cert)
pb_sqrt_newton(x, r0, it) = { my(r = r0); for (i = 1, it, r = pb_red((r + x[1] / r) / 2, PB_MW + 3 * PB_e)); r; }

\\ ---------------------------------------------------------------- Jacobian of y^2 = f(x), deg f = 6
pbj_zero() = [[pb_one], []];
pbj_iszero(D) = #D[1] == 1;
\\ one reduction step: u monic of degree 4, v of degree <= 3, u | f - v^2 (exactly, for the enclosed point)
pbj_red(f, u, v) = {
  my(q = pbx_divrem(pbx_sub(f, pbx_mul(v, v)), u)[1], lc, li, u3);
  if (#q != 3, error("pbj_red: degrees"));
  lc = q[3]; if (!pb_nz(lc), error("pbj_red: lc(u3) is not certified nonzero"));
  li = pb_inv(lc); u3 = [pb_mul(q[1], li), pb_mul(q[2], li), pb_one];
  [u3, pbx_divrem(pbx_neg(pbx_pad(v, 4)), u3)[2]];
}
pbj_add(f, D1, D2) = {
  if (pbj_iszero(D1), return(D2)); if (pbj_iszero(D2), return(D1));
  my(u1 = D1[1], v1 = pbx_pad(D1[2], 2), u2 = D2[1], v2 = pbx_pad(D2[2], 2), c, k, v);
  c = [pb_sub(u1[1], u2[1]), pb_sub(u1[2], u2[2])];      \\ u1 mod u2 (Res(u2, u1) = N_B2(c))
  k = pbB_mul(pbB_sub(v2, v1), pbB_inv(c, u2), u2);       \\ (v2 - v1) / u1 mod u2
  v = pbx_add(v1, pbx_mul(u1, k));
  pbj_red(f, pbx_mul(u1, u2), v);
}
pbj_dbl(f, D) = {
  if (pbj_iszero(D), return(D));
  my(u1 = D[1], v1 = pbx_pad(D[2], 2), w, k, v);
  w = pbx_divrem(pbx_sub(f, pbx_mul(v1, v1)), u1)[1];   \\ (f - v1^2) / u1 (exact division for the enclosed point)
  k = pbB_mul(pbB_fromx(w, u1), pbB_inv(pbB_scal(pb_c(2), v1), u1), u1);
  v = pbx_add(v1, pbx_mul(k, u1));
  pbj_red(f, pbx_mul(u1, u1), v);
}
pbj_neg(D) = [D[1], pbx_neg(D[2])];
pbj_mul(f, n, D) = {
  my(R = pbj_zero(), bn);
  if (n < 0, return(pbj_mul(f, -n, pbj_neg(D))));
  if (n == 0, return(R));
  bn = binary(n);
  for (i = 1, #bn, R = pbj_dbl(f, R); if (bn[i], R = pbj_add(f, R, D)));
  R;
}
\\ least valuation of the precision of the coefficients (diagnostics)
pbj_prec(D) = { my(m = PB_MW); foreach (concat(D[1], D[2]), c, m = min(m, c[2])); m; }

\\ ---------------------------------------------------------------- logarithm near the origin
\\ lower bound, over all n > n0, of ceil(n/d) (c - c2) + min over the two shapes of the terms (see pbj_tinylog_x):
\\ A(n) = vs - e v_p(n+1) (first integral), B(n) = min(vx + vs - e v_p(n+1), 2 vs - e v_p(n+2)) (second).
\\ Uses v_p(m) <= log_p(m) < #digits_p(m) and the monotonicity of n (c - c2)/d - e log_p(n + 2) for n + 2 >= e d / ((c - c2) ln p).
pbj_tailbound(n0, d, cc, vs, vx) = {
  my(dl = cc - PB_C2, nst, best = PB_INF, tn);
  if (dl <= 0, error("pbj_tailbound: c <= c2"));
  tn = (n -> ceil(n / d) * dl + min(vs - PB_e * valuation(n + 1, PB_P), min(vx + vs - PB_e * valuation(n + 1, PB_P), 2 * vs - PB_e * valuation(n + 2, PB_P))));
  \\ explicit range, then a bound for the rest: ln p > 0.69 (p >= 2)
  nst = max(n0 + 1, ceil(PB_e * d / (dl * 0.69)) + 1);
  for (n = n0 + 1, nst, best = min(best, tn(n)));
  \\ n > nst: ceil(n/d) dl >= n dl / d is increasing faster than e log_p(n+2), bounded below at nst by the digit count
  best = min(best, nst * dl / d + min(vs, min(vx + vs, 2 * vs)) - PB_e * #digits(nst + 2, PB_P));
  best;
}
\\ tiny logarithm in the chart of x, target precision tgt for the result; returns [ok, [l1, l2] (balls), info]
pbj_tinylog_x(f, D, tgt) = {
  my(u = D[1], v = pbx_pad(D[2], 2), th, s, y1, y2, pw, F, F0i, e, cc, vs, vx, vy1max, n0, h, T, I1, I2, G, Z, res, info = Map());
  if (pbj_iszero(D), return([1, [pb_zero, pb_zero], info]));
  if (!pb_nz(pb_sub(pb_mul(u[2], u[2]), pb_scal(4, u[1]))), return([0, 0, "disc u not certified nonzero"]));
  th = [pb_zero, pb_one];
  s = [pb_neg(u[2]), pb_c(-2)];
  y1 = [v[1], v[2]]; y2 = [pb_sub(v[1], pb_mul(v[2], u[2])), pb_neg(v[2])];
  \\ Taylor coefficients F_j = sum_i binom(i, j) f_i th^(i - j)
  pw = vector(7); pw[1] = pbB_k(pb_one); for (i = 2, 7, pw[i] = pbB_mul(pw[i - 1], th, u));
  F = vector(7, j, my(r = pbB_k(pb_zero)); for (i = j - 1, 6, r = pbB_add(r, pbB_scal(pb_mul(pb_c(binomial(i, j - 1)), f[i + 1]), pw[i - j + 2]))); r);
  if (!pb_nz(pbB_norm(F[1], u)), return([0, 0, "f(x1) f(x2) not certified nonzero"]));
  F0i = pbB_inv(F[1], u);
  my(sj = pbB_k(pb_one));
  e = vector(6, j, sj = pbB_mul(sj, s, u); pbB_mul(pbB_mul(F[j + 1], F0i, u), sj, u));
  cc = vecmin(vector(6, j, pbB_val(e[j], u)));
  mapput(info, "c", cc);
  if (cc <= PB_C2, return([0, 0, Str("c = ", cc, " <= c2")]));
  vs = pbB_val(s, u); vx = pbB_val(th, u); vy1max = pbB_vmax(y1, u);
  \\ tail of the result: (tail bound of the integrals) - max v(y1), then Tr/2 costs v(2)
  n0 = 1; while (pbj_tailbound(n0, 6, cc, vs, vx) - vy1max - (if (PB_P == 2, PB_e, 0)) < tgt, n0 = ceil(n0 * 5 / 4) + 1);
  T = pbj_tailbound(n0, 6, cc, vs, vx) - vy1max;
  mapput(info, "n0", n0);
  h = vector(n0 + 1); h[1] = pbB_k(pb_one);
  for (n = 1, n0,
    my(acc = pbB_k(pb_zero));
    for (j = 1, min(6, n), acc = pbB_add(acc, pbB_scal(pb_c(2 * (n - j) + j), pbB_mul(e[j], h[n - j + 1], u))));
    h[n + 1] = pbB_scal(pb_c(-1 / (2 * n)), acc));
  G = pbB_k(pb_zero); I1 = pbB_k(pb_zero); I2 = pbB_k(pb_zero);
  my(s2 = pbB_mul(s, s, u), xs = pbB_mul(th, s, u));
  for (k = 0, n0,
    G = pbB_add(G, h[k + 1]);
    I1 = pbB_add(I1, pbB_scal(pb_c(1 / (k + 1)), pbB_mul(h[k + 1], s, u)));
    I2 = pbB_add(I2, pbB_mul(h[k + 1], pbB_add(pbB_scal(pb_c(1 / (k + 1)), xs), pbB_scal(pb_c(1 / (k + 2)), s2)), u)));
  \\ branch: Z = y1 + y2 g(s), tail of g(s) = sum_{n > n0} h_n has valuation >= ceil((n0+1)/6) (c - c2)
  my(Tg = ceil((n0 + 1) / 6) * (cc - PB_C2), vZ);
  Z = pbB_add(y1, pbB_mul(y2, G, u));
  vZ = min(pbB_val(Z, u), pbB_val(y2, u) + Tg);
  mapput(info, "branch margin", vZ - (PB_e * valuation(2, PB_P) + vy1max));
  if (vZ <= PB_e * valuation(2, PB_P) + vy1max, return([0, 0, "branch not certified"]));
  \\ result: -(1/y1) (I1, I2), value at a root = Tr/2
  my(yi = pbB_inv(y1, u), L = [pbB_neg(pbB_mul(yi, I1, u)), pbB_neg(pbB_mul(yi, I2, u))]);
  res = vector(2, k, my(t2 = pbB_tr(L[k], u), hv = pb_c(1 / 2), r = pb_mul(hv, t2)); [r[1], floor(min(r[2], T - PB_e * valuation(2, PB_P)))]);
  mapput(info, "tail", T);
  mapput(info, "th-coefficient", [pb_val(L[1][2]), pb_val(L[2][2])]);
  [1, res, info];
}
pbj_tinylog_inf(f, D, tgt) = {
  my(u = D[1], v = pbx_pad(D[2], 2), up, vp, F, r);
  if (pbj_iszero(D), return([1, [pb_zero, pb_zero], Map()]));
  if (!pb_nz(u[1]), return([0, 0, "u(0) not certified nonzero"]));
  my(ui = pb_inv(u[1])); up = [ui, pb_mul(u[2], ui), pb_one];
  vp = pbx_divrem([pb_zero, pb_zero, v[2], v[1]], up)[2];
  F = vector(7, i, f[8 - i]);
  r = pbj_tinylog_x(F, [up, vp], tgt);
  if (!r[1], return(r));
  [1, [pb_neg(r[2][2]), pb_neg(r[2][1])], r[3]];
}
\\ log of a point close to the origin: chart of x, else the chart at infinity; [ok, log, info]
pbj_tinylog(f, D, tgt) = {
  my(r = pbj_tinylog_x(f, D, tgt));
  if (r[1], mapput(r[3], "chart", "x"); return(r));
  my(r2 = pbj_tinylog_inf(f, D, tgt));
  if (r2[1], mapput(r2[3], "chart", "inf"); return(r2));
  [0, 0, Str("x: ", r[3], "; inf: ", r2[3])];
}
\\ log D = log(N D) / N; tgt is the target precision of log(N D)
pbj_log(f, D, N, tgt) = {
  my(ND = pbj_mul(f, N, D), r = pbj_tinylog(f, ND, tgt));
  if (!r[1], error(Str("pbj_log: ", r[3])));
  mapput(r[3], "prec(N D)", pbj_prec(ND));
  [apply(l -> pb_mul(pb_c(1 / N), l), r[2]), r[3]];
}

\\ ---------------------------------------------------------------- exact points near approximations
\\ given U (balls, monic, disc certified nonzero) and an approximation V0 (centres) with f = V0^2 (1 + rho) mod U,
\\ v(rho) > c2 in both embeddings, the exact V = V0 (1 + rho)^(1/2) mod U satisfies U | f - V^2; it is enclosed by the
\\ returned balls: v((V - V0)(root)) >= e0 := min v(V0) + v(rho) - v(2) at both roots, hence for the coefficients
\\ (V - V0 = d0 + d1 th): v(d1) >= e0 - v(th - th') (v(th - th') = v(disc U)/2), v(d0) >= min(e0, v(d1) + v(th)).
\\ Returns [U, V balls] or 0.
pb_cen(c) = if (type(c) == "t_VEC", c[1], c);
pbj_genuine(f, U, V0) = {
  my(dsc = pb_sub(pb_mul(U[2], U[2]), pb_scal(4, U[1])), V0b, rho, vr, e0, vd, vth, m1, m0);
  if (!pb_nz(dsc), return(0));
  V0b = apply(c -> pb(pb_cen(c), PB_MW), pbx_pad(V0, 2));
  my(Vb = [V0b[1], V0b[2]], fB = pbB_fromx(f, U));
  rho = pbB_sub(pbB_div(fB, pbB_mul(Vb, Vb, U), U), pbB_k(pb_one));
  vr = pbB_val(rho, U);
  if (vr <= PB_C2, return(0));
  e0 = pbB_val(Vb, U) + vr - if (PB_P == 2, PB_e, 0);
  vd = pb_vc(dsc[1]) / 2; vth = pbB_val([pb_zero, pb_one], U);
  m1 = floor(e0 - vd); m0 = floor(min(e0, m1 + vth));
  [U, [pb(V0b[1][1], min(m0, V0b[1][2])), pb(V0b[2][1], min(m1, V0b[2][2]))]];
}
\\ Newton refinement of an approximate square root V0 of f modulo U (centres only)
pbj_refine(f, U, V0, it) = {
  my(Vb = apply(c -> pb(pb_cen(c), PB_MW), pbx_pad(V0, 2)), fB = pbB_fromx(f, U), W = [Vb[1], Vb[2]]);
  for (i = 1, it, W = pbB_scal(pb_c(1 / 2), pbB_add(W, pbB_div(fB, W, U))); W = [pb(W[1][1], PB_MW), pb(W[2][1], PB_MW)]);
  [W[1], W[2]];
}
