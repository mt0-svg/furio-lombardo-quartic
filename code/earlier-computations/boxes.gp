\\ boxes.gp: covering of C(Q_2) by boxes with proved constancy of the descent class and of the leading class
\\ of pr(lambda) (derivation: see the paper).
\\ Setting. Each disc d = [chart, a0, b0, k, 2] of discs_q2.txt is {(t, u) = (a0 + 2^k X, b0 + 2^k Y(X))} with
\\ Y in Z_2<X> of Gauss norm <= 1 (the classification criterion makes Y -> -H(X, Y) a contraction), so for X, X0 in
\\ the closed unit disc of C_2: |u(X) - u(X0)| <= 2^-k |X - X0|, and |F_u| = 2^(k - v2(g01)) on the whole disc.
\\ A box is S = {X = X0 mod 2^s}. For a quadric Q (Bruin form) the increment Q(P) - Q(P0) is bounded by the exact
\\ Taylor coefficients at the centre (radius 2^-(k + s) in t and u).
\\  (a) Descent class. If v_w(Q(P) - Q(P0)) > v_w(Q(P0)) + 2 e_w on S (Q = Q1, else Q3), the class of Q(P)/delta in
\\      K_w^x / K_w^x2 is constant on S. A class that is not a square at some w | 2 excludes S for the twist delta
\\      (a rational point of twist delta has Q1(P)/delta, resp. Q3(P)/delta, in K21^x2).
\\  (b) Leading class. At the place v (e = 3), if the same criterion holds on the disc of radius 2^-(s-1) around X0
\\      (the parent box), then r = sqrt(Q1/delta) (or s = sqrt(Q3/delta)) is analytic there with constant absolute
\\      value, the other coordinate is Q2/(delta r), and w = d lambda / dX = +-2^k (a12 s, a21 r) / F_u (p21_9_tiny.gp:
\\      phi^*(dt/Y), phi^*(t dt/Y) = (a12 s, a21 r) Omega_C, Omega_C = +-dt/F_u in every chart) has sup norm <= M on it.
\\      The abelian integral is the antiderivative on discs (Katz, Rabinoff, Zureick-Brown, Duke Math. J. 165 (2016),
\\      the abelian integral on a curve is an integration theory, condition (ftc) of their Definition 3.1), so
\\      |lambda(X) - lambda(X0)| <= M |X - X0| for |X - X0| <= 2^-s. If this lies in pi^m O_v^2 with
\\      m >= 3 (nu0 + 1) + mL (pi^mL O_v^2 inside Lambda), nu and the leading class are constant on S.
\\  (c) Near a known lift x_i (lambda(x_i) in log Gamma): analyticity on the disc of radius 2^-(s0-1) around X_i
\\      with sup norm M gives, for v2(X - X_i) = j >= s0, lambda(X) - lambda(X_i) = g0 (X - X_i) + tail with
\\      g0 = 2^k c_1 exact (pullback_known_lifts.gp) and v_pr(tail) >= vM + 3 (2 j - s0). The linear term fixes nu = nu1 + j and
\\      the class e1 of pr(g0) as soon as 3 j >= 3 (nu1 + 1 + s0) + mL - vM; the shells s0 <= j < J0 are boxes (b).
\\ The values nu0 and the leading class at box centres come from lambda_at of leading_class_explore.gp (numerical, the
\\ precision of the 2-adic Abel-Prym map and of the logarithm is not certified here).
\\ Output: every box with its verdict (excluded at place w, constant class not in pr(W), tail at a known point) and
\\ the check that the boxes cover the five discs; saves /tmp/k21c/m9e/boxes_k<k>.txt.
\\ Run from code/earlier-computations: gp -q boxes.gp > boxes.out
if (type(BOXLIB) != "t_INT", default(parisizemax, 5*10^9); default(nbthreads, 1));  \\ library mode: set BOXLIB before reading
NOQUIT = 1; JOBS = [];
read("leading_class_explore.gp");
system("mkdir -p /tmp/k21c/m9e");
PR2 = idealprimedec(nfK, 2);
EW = apply(q -> q.e, PR2);
IV = [i | i <- [1 .. #PR2], PR2[i].e == 3][1];
chq(idealval(nfK, idealhnf(nfK, pr), PR2[IV]) == 1, "the place v of p21_39 is PR2[IV]");
vw(w, c) = if (c == 0, oo, nfeltval(nfK, lift(Mod(c, K21)), PR2[w]));
rep(ch, T, U) = if (ch == 1, [T, U, 1], ch == 2, [T, 1, U], [1, T, U]);
\\ quadrics in the chart variables (x = t, y = u)
QC = vector(3, ch, vector(3, j, substvec([Q1, Q2, Q3][j], [x, y, z], rep(ch, x, y))));
\\ exact Taylor data of a quadric q(x, y) at (t0, u0): [value, [q_t, q_u], [q_tt/2, q_tu, q_uu/2]]
tayl(q, t0, u0) = {
  my(g = substvec(q, [x, y], [x + t0, y + u0]), c = (i, j) -> Mod(polcoef(polcoef(g, i, x), j, y), K21));
  [c(0, 0), [c(1, 0), c(0, 1)], [c(2, 0), c(1, 1), c(0, 2)]];
}
\\ lower bound for v_w(q(P) - q(P0)) when |t - t0|, |u - u0| <= 2^-R
incr(w, T, R) = min(vecmin(apply(c -> vw(w, c), T[2])) + EW[w] * R, vecmin(apply(c -> vw(w, c), T[3])) + 2 * EW[w] * R);
v2(c) = if (c == 0, oo, valuation(c, 2));
\\ disc data: [chart, a0, b0, k, v2(g01)]
{DD = vector(#DISCS, i, my(d = DISCS[i], G = substvec(FA[d[1]], VA[d[1]], [d[2] + 2^d[4] * 'X, d[3] + 2^d[4] * 'Y]));
  chq(d[5] == 2, "Y-parametrised disc"); [d[1], d[2], d[3], d[4], v2(polcoef(polcoef(G, 0, 'X), 1, 'Y))]);}
\\ centre of the box: approximate point (t0, u0) in chart coordinates (2-adic, modulo 2^NP), from discpt
centre(di, X0) = { my(P = discpt(DISCS[di], X0), ch = DD[di][1]); if (ch == 1, [P[1], P[2]], ch == 2, [P[1], P[3]], [P[2], P[3]]); }
DL = [Mod(d0, K21), Mod(d1, K21)];
\\ (a): class of the box S = (di, X0, s) at place w for twist k: "sq", "nsq" or "?"
boxclass(k, di, X0, s, w) = {
  my(c = centre(di, X0), R = DD[di][4] + s);
  for (j = 1, 2, my(q = QC[DD[di][1]][if (j == 1, 1, 3)], T = tayl(q, c[1], c[2]), vq = vw(w, T[1]));
    if (vq < oo && incr(w, T, R) > vq + 2 * EW[w],
      return(if (nfislocalpower(nfK, PR2[w], lift(T[1] / DL[k + 1]), 2), "sq", "nsq"))));
  "?";
}
\\ (b): lower bound vM for v_pr of the sup norm of w on the disc of radius 2^-(s-1) around X0, or oo if the
\\ analyticity criterion fails there
A12 = vector(2); A21 = vector(2);
{ foreach (TINY, tt, my(kk = tt[2] + 1, A = tt[3]); chq(A[1, 1] == 0 && A[2, 2] == 0, "pullback matrix is antidiagonal");
    A12[kk] = Mod(A[1, 2], K21); A21[kk] = Mod(A[2, 1], K21)); }
supbound(k, di, X0, s) = {
  my(c = centre(di, X0), R = DD[di][4] + s - 1, T1, T2, T3, v1, v3, v2s, br = 0, vr, vs);
  chq(s >= 1, "parent box inside the disc");
  T1 = tayl(QC[DD[di][1]][1], c[1], c[2]); T2 = tayl(QC[DD[di][1]][2], c[1], c[2]); T3 = tayl(QC[DD[di][1]][3], c[1], c[2]);
  v1 = vw(IV, T1[1]); v3 = vw(IV, T3[1]); v2s = min(vw(IV, T2[1]), incr(IV, T2, R));
  if (v1 < oo && incr(IV, T1, R) > v1 + 6, br = 1, v3 < oo && incr(IV, T3, R) > v3 + 6, br = 3, return(oo));
  if (br == 1, chq(v1 % 2 == 0, "square at v has even valuation"); vr = v1 / 2; vs = v2s - vr,
               chq(v3 % 2 == 0, "square at v has even valuation"); vs = v3 / 2; vr = v2s - vs);
  3 * DD[di][4] + min(vw(IV, A12[k + 1]) + vs, vw(IV, A21[k + 1]) + vr) - 3 * (DD[di][5] - DD[di][4]);
}
\\ mL: least m with pi^m O_v^2 inside Lambda
mLam(k) = {
  my(C = ctx(k), Hi = C[4], PIk = C[9]);
  for (m = 0, 60, my(ok = 1);
    for (i = 0, 2, for (j = 1, 2, my(l = [0, 0]); l[j] = PIk^(m + i); my(cv = Hi * logvec(l, PREC2, PIk)); if (denominator(cv) % 2 == 0, ok = 0)));
    if (ok, return(m)));
  error("mLam");
}
\\ pr coordinates of a pair in K_v^2 (Lambda coordinates then the projection of p21_36)
prc(k, l) = { my(C = ctx(k), yv = C[4] * logvec(apply(c -> redK(LV, c), l), PREC2, C[9])); vector(4, i, (C[5] * yv)[C[6][i]])~; }
\\ known lifts: [i, twist, disc, X_i]
KP = [[0, 0, 1, 0], [2, 0, 1, 1], [1, 1, 3, 0], [3, 1, 2, -1]];
LCACHE = Map();
lam_centre(k, di, X0) = {
  my(key = [k, di, X0]);
  if (mapisdefined(LCACHE, key), return(mapget(LCACHE, key)));
  my(r = lambda_at(k, discpt(DISCS[di], X0)));
  mapput(LCACHE, key, r); r;
}
run(k) = {
  my(t0 = getabstime(), mL = mLam(k), stack = List(), done = List(), nlam = 0, fails = 0, kp = [p | p <- KP, p[2] == k], tails = Map());
  printf("twist %d: mL = %d (pi^mL O_v^2 inside Lambda)\n", k, mL);
  \\ linear term data at the known lifts
  foreach (kp, p, my(TT = [tt | tt <- TINY, tt[1] == p[1]][1], g0 = [Mod(TT[4][1], K21), Mod(TT[5][1], K21)] * 2^DD[p[3]][4], pv = prc(k, g0), nu1 = v2vec(pv), e1 = apply(c -> c % 2, pv / 2^nu1));
    chq(!f2in(ctx(k)[7], e1), "class of the linear term outside pr(W)");
    mapput(tails, p[1], [nu1, e1]);
    printf("  x_%d (disc %d, X = %d): nu(pr g0) = %d, class %s not in pr(W)\n", p[1], p[3], p[4], nu1, e1~));
  for (di = 1, #DISCS, listput(stack, [di, 0, 0]));
  while (#stack,
    my(it = stack[#stack], di = it[1], X0 = it[2], s = it[3], hit = [p | p <- kp, p[3] == di && valuation(p[4] - X0, 2) >= s], cls, verdict = "");
    listpop(stack);
    chq(s <= 40, "box depth");
    if (#hit,
      \\ (c) box around a known lift
      if (s == 0, listput(stack, [di, X0, 1]); listput(stack, [di, X0 + 1, 1]); next);
      my(p = hit[1], Xi = p[4], vM = supbound(k, di, Xi, s), nu1, J0);
      if (vM == oo, listput(stack, [di, X0, s + 1]); listput(stack, [di, X0 + 2^s, s + 1]); next);
      nu1 = mapget(tails, p[1])[1];
      J0 = max(s, ceil((3 * (nu1 + 1 + s) + mL - vM) / 3));
      for (j = s, J0 - 1, listput(stack, [di, (Xi + 2^j) % 2^(j + 1), j + 1]));
      listput(done, [di, Xi % 2^J0, J0, Str("tail at x_", p[1], " (analytic radius 2^-", s - 1, ", vM = ", vM, ")")]);
      next);
    \\ (a) descent classes
    cls = vector(#PR2, w, boxclass(k, di, X0, s, w));
    my(ex = [w | w <- [1 .. #PR2], cls[w] == "nsq"]);
    if (#ex, listput(done, [di, X0, s, Str("excluded: non-square at the place with e = ", EW[ex[1]])]); next);
    if (#[w | w <- [1 .. #PR2], cls[w] == "?"] || s == 0, listput(stack, [di, X0, s + 1]); listput(stack, [di, X0 + 2^s, s + 1]); next);
    \\ (b) leading class
    my(r = lam_centre(k, di, X0)); nlam++; if (nlam % 10 == 0, printf("    [%d lambda evaluations, stack %d, %d boxes done, %d ms]\n", nlam, #stack, #done, getabstime() - t0));
    chq(r[1] == "ok", Str("lambda at the centre: ", r[1]));
    if (r[2] == oo, listput(stack, [di, X0, s + 1]); listput(stack, [di, X0 + 2^s, s + 1]); next);
    if (r[4], fails++; listput(done, [di, X0, s, Str("FAIL: leading class ", r[3], " in pr(W)")]); next);
    my(vM = supbound(k, di, X0, s));
    if (vM != oo && vM + 3 * s >= 3 * (r[2] + 1) + mL,
      listput(done, [di, X0, s, Str("constant: nu = ", r[2], ", class ", r[3], ", vM = ", vM)]),
      listput(stack, [di, X0, s + 1]); listput(stack, [di, X0 + 2^s, s + 1])));
  done = Vec(done);
  \\ covering check: the boxes are disjoint and their measures add up to one per disc (X in Z_2)
  for (di = 1, #DISCS, my(bx = [b | b <- done, b[1] == di]);
    chq(sum(i = 1, #bx, 1 / 2^bx[i][3]) == 1, Str("boxes cover disc ", di));
    for (i = 1, #bx, for (j = i + 1, #bx, my(sm = min(bx[i][3], bx[j][3])); chq((bx[i][2] - bx[j][2]) % 2^sm != 0, "disjoint boxes"))));
  my(fn = Str("/tmp/k21c/m9e/boxes_k", k, ".txt")); system(Str("rm -f ", fn));
  foreach (done, b, write(fn, b); printf("  disc %d, X = %d mod 2^%d: %s\n", b[1], b[2] % 2^b[3], b[3], b[4]));
  printf("twist %d: %d boxes, %d lambda evaluations, %d failures (%d ms)\n", k, #done, nlam, fails, getabstime() - t0);
  [done, fails];
}
{
  if (type(BOXLIB) != "t_INT",
    my(R0 = run(0), R1 = run(1));
    printf("RESULT: %s\n", if (R0[2] + R1[2] == 0, "every box of both twists is excluded, constant with a class outside pr(W), or a tail at a known lift", "FAILURES")));
}
if (type(BOXLIB) != "t_INT", quit);
