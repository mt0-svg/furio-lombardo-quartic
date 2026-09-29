\\ taylor_model_probe.gp: second probe of the box inputs: Taylor model enclosure of the arcs over each box.
\\ A Taylor model of order n over H = pi^eta O_v is [c_0, ..., c_n, R] (n + 2 balls), with pointwise semantics: the
\\ function f on H is enclosed if for every h in H there are c_i in the balls C_i and R in the ball B with
\\ f(h) = sum c_i h^i + h^(n+1) R. Every operation is an identity at each h, so only ball arithmetic is used:
\\   sum, product   the product of the polynomial parts, its terms of degree > n and the cross terms with the remainders
\\                  moved into R (h replaced by the ball H);
\\   constant ball  a function with all its values in a ball b is enclosed by [b, 0, ..., 0];
\\   inverse        P the truncated series of 1/g at the centres, e = 1 - g P (a Taylor model), 1/g = P + e (1/g) with
\\                  1/g(h) in the constant ball 1/ball(g) (g certified nonzero on H);
\\   square root    r(h) the root of a(h) in the certified ball of roots around r_0 (the branch of the centre),
\\                  P the truncated series, r = P + (a - P^2) (1/(r + P)), r + P in a ball certified nonzero;
\\   the point      t = t0 + 2^k h exactly (the free chart coordinate), u = P_u - F(t, P_u) (1/G) with P_u the truncated
\\                  implicit function series and G = (F(t, P_u) - F(t, u)) / (P_u - u) evaluated on the ball of u of
\\                  (|u - u0| <= 2^-(k+s)), certified nonzero.
\\ The pipeline of probe 1 (lift, phi of abel_prym_lib in the form of p21_46, reversal, one Cantor composition with
\\ R = E0 - phi(P(X0)), chart coordinates t at a = k) runs on Taylor models (taylor_model_lib.gp). Reported per box: the
\\ certified depth of t over the box, and of Lam t (the first order of lambda in the chart) against the need 3 (nu + 3),
\\ with the part of degree >= 2 in h separately; for the tails the ball of (Lam t - Lam t'(0) h) / h^2 against the
\\ need vM - 3 s0 of tail_sharp, and 2 Lam t'(0) against the certified ball of 4 c_1 (Lean data t.g). The terms of
\\ degree >= 2 of the chart logarithm itself are not included (ChartLog). Numerical probe of the method.
\\ Env: M4B_N (order, default 4), M4B_MW (precision in pi-digits, default 3000), M4B_LIM (constant boxes per twist),
\\ M4B_DEBUG = [k, disc, X0, s] (the Taylor models of every stage for one box).
\\ Run from code/earlier-computations:
\\   gp -q ../covering/taylor_model_probe.gp > ../covering/taylor_model_probe.out
default(parisizemax, 2 * 10^9); default(nbthreads, 1);
LIM = if (getenv("M4B_LIM"), eval(getenv("M4B_LIM")), 10^6);
if (getenv("M4B_MW"), MW0 = eval(getenv("M4B_MW")));
TM_N = if (getenv("M4B_N"), eval(getenv("M4B_N")), 4);
read("../covering/centres_ball_lib.gp");
kv_init(MW);
\\ operation count (env M4B_COUNT): every ball product and inverse after the setup
PB_CNT = [0, 0]; TM_CNT = 0;
if (getenv("M4B_COUNT"), pb_mul0 = pb_mul; pb_inv0 = pb_inv; pb_mul = (x, y) -> (PB_CNT[1]++; pb_mul0(x, y)); pb_inv = (x) -> (PB_CNT[2]++; pb_inv0(x)));

\\ ---------------------------------------------------------------- Taylor models of order TM_N
TM_ETA = 0;
hpw(e) = if (e == 0, pb_one, [Mod(0, PB_EP), e * TM_ETA]);
tm_cb(b) = concat([b], vector(TM_N + 1, i, pb_zero));
tm_c(x) = tm_cb(pb_c(x));
tm_zero = tm_cb(pb_zero); tm_one = tm_cb(pb_one);
tm_add(f, g) = vector(TM_N + 2, i, pb_add(f[i], g[i]));
tm_sub(f, g) = vector(TM_N + 2, i, pb_sub(f[i], g[i]));
tm_neg(f) = vector(TM_N + 2, i, pb_neg(f[i]));
\\ the ball of the polynomial part over H, and the ball of the whole function
tm_pball(f) = { my(r = pb_zero); forstep (i = TM_N, 0, -1, r = pb_add(pb_mul(r, hpw(1)), f[i + 1])); r; }
tm_ball(f) = pb_add(tm_pball(f), pb_mul(hpw(TM_N + 1), f[TM_N + 2]));
tm_nz(f) = pb_nz(tm_ball(f));
tm_mul(f, g) = {
  TM_CNT++;
  my(n = TM_N, C = vector(n + 2, i, pb_zero), hi = pb_zero);
  for (i = 0, n, for (j = 0, n, my(p = pb_mul(f[i + 1], g[j + 1]));
    if (i + j <= n, C[i + j + 1] = pb_add(C[i + j + 1], p), hi = pb_add(hi, pb_mul(p, hpw(i + j - n - 1))))));
  C[n + 2] = pb_add(pb_add(hi, pb_mul(f[n + 2], tm_pball(g))), pb_add(pb_mul(g[n + 2], tm_pball(f)), pb_mul(hpw(n + 1), pb_mul(f[n + 2], g[n + 2]))));
  C;
}
tm_scal(r, f) = tm_mul(tm_c(r), f);
tm_inv(g) = {
  my(n = TM_N, gb = tm_ball(g), d = vector(n + 2, i, pb_zero), e);
  if (!pb_nz(gb), error("tm_inv: not certified nonzero on H"));
  d[1] = pb_inv(g[1]);
  for (k = 1, n, my(s = pb_zero); for (i = 1, k, s = pb_add(s, pb_mul(g[i + 1], d[k - i + 1]))); d[k + 1] = pb_neg(pb_mul(s, d[1])));
  e = tm_sub(tm_one, tm_mul(g, d));
  tm_add(d, tm_mul(e, tm_cb(pb_inv(gb))));
}
tm_div(f, g) = tm_mul(f, tm_inv(g));
tm_sqrt(a, rc) = {
  my(n = TM_N, r0 = pb_sqrt_cert(a[1], pb_sqrt_newton(a[1], rc, 14)), P = vector(n + 2, i, pb_zero), rb, den, e);
  chq(r0 != 0, "tm_sqrt: root at the centre");
  rb = pb_sqrt_cert(tm_ball(a), r0[1]); chq(rb != 0, "tm_sqrt: square root certified over H");
  P[1] = r0; my(i2 = pb_inv(pb_scal(2, r0)));
  for (k = 1, n, my(s = a[k + 1]); for (i = 1, k - 1, s = pb_sub(s, pb_mul(P[i + 1], P[k - i + 1]))); P[k + 1] = pb_mul(s, i2));
  den = pb_add(rb, tm_ball(P)); chq(pb_nz(den), "tm_sqrt: r + P certified nonzero");
  e = tm_sub(a, tm_mul(P, P));
  tm_add(P, tm_mul(e, tm_cb(pb_inv(den))));
}
\\ the ball of (f(h) - c_0 - c_1 h) / h^2 over H (n >= 1), and the ball of f(h) - c_0 - c_1 h
tm_q2(f) = { my(r = pb_zero); forstep (i = TM_N, 2, -1, r = pb_add(pb_mul(r, hpw(1)), f[i + 1])); pb_add(r, pb_mul(hpw(TM_N - 1), f[TM_N + 2])); }
tm_hi(f) = pb_mul(hpw(2), tm_q2(f));
read("../covering/taylor_model_lib.gp");
tmc_all(x) = if (type(x) == "t_VEC" && #x == 2 && type(x[1]) == "t_POLMOD" && type(x[2]) == "t_INT", tm_cb(x), apply(tmc_all, x));

\\ ---------------------------------------------------------------- data of probe 1 (balls)
frevB(k) = kvx(polrecip(if (k == 0, F0, F1)));
revD(D) = {
  my(U = D[1], V = pbx_pad(D[2], 2), ui, up, vp);
  chq(pb_nz(U[1]), "reversal: u(0) certified nonzero");
  ui = pb_inv(U[1]); up = [ui, pb_mul(U[2], ui), pb_one];
  vp = pbx_divrem([pb_zero, pb_zero, V[2], V[1]], up)[2];
  [up, pbx_pad(vp, 2)];
}
e0init(Fr, a0) = {
  my(fa = pbx_eval(Fr, pb_c(a0)), bb = csqrt(fa), Fd, fp, v1);
  chq(bb != 0, "F(a) is a square");
  Fd = vector(6, i, pb_scal(i, Fr[i + 1])); fp = pbx_eval(Fd, pb_c(a0));
  v1 = pb_div(fp, pb_scal(2, bb));
  [[[pb_c(a0^2), pb_c(-2 * a0), pb_one], [pb_sub(bb, pb_scal(a0, v1)), v1]], bb, v1];
}
laminit(a0, bb, v1) = {
  my(bi = pb_inv(bb), yp = pb_mul(v1, pb_mul(bi, bi)));
  [[pb_scal(a0, bi), pb_sub(bi, pb_scal(a0, yp))], [bi, pb_neg(yp)]];
}
\\ the point of the disc d at X0: [chart, free coordinate c1, approximate root c (integer), k, Hensel precision kP]
cpointD(d, X0) = {
  my(ch = d[1], c1 = d[2] + 2^d[4] * X0, var = VA[ch][2], F1 = subst(FA[ch], VA[ch][1], c1), c = d[3] + O(2^(NP + 10)), it = 0, Fv, Dv, kP);
  while (valuation(subst(F1, var, c), 2) < NP, c -= subst(F1, var, c) / subst(deriv(F1, var), var, c); it++; chq(it < 400, "Newton"));
  c = truncate(c); Fv = valuation(subst(F1, var, c), 2); Dv = valuation(subst(deriv(F1, var), var, c), 2);
  if (Fv == oo, kP = PB_MW, chq(Fv > 2 * Dv, "Hensel for the point"); kP = Fv - Dv);
  chq(kP >= d[4] && (c - d[3]) % 2^d[4] == 0, "the root lies in the disc");
  [ch, c1, c, d[4], kP];
}
ballPt(cp) = { my(c1 = pb_c(cp[2]), cb = pb(cp[3], 3 * cp[5]), ch = cp[1]); if (ch == 1, [c1, cb, pb_one], ch == 2, [c1, pb_one, cb], [pb_one, c1, cb]); }
\\ a bivariate integer polynomial on Taylor models (Horner in v2, coefficients by Horner in v1), and on balls
tm_evp1(p, v1, T1) = { my(r = tm_zero); forstep (i = poldegree(p, v1), 0, -1, r = tm_add(tm_mul(r, T1), tm_c(polcoef(p, i, v1)))); r; }
tm_eval2(F, v1, v2, T1, T2) = { my(r = tm_zero); forstep (j = poldegree(F, v2), 0, -1, r = tm_add(tm_mul(r, T2), tm_evp1(polcoef(F, j, v2), v1, T1))); r; }
pb_evp1(p, v1, b) = { my(r = pb_zero); forstep (i = poldegree(p, v1), 0, -1, r = pb_add(pb_mul(r, b), pb_c(polcoef(p, i, v1)))); r; }
\\ the point P(X0 + h) as Taylor models, h in H = 2^s Z_2 (TM_ETA = 3 s): coordinates x, y, z with the chart one 1
tmP(cp, sl) = {
  my(ch = cp[1], v1 = VA[ch][1], v2 = VA[ch][2], F = FA[ch], k = cp[4], n = TM_N, tt, us, F2, Pu, res, Gb, uu, tb, Pb, ub);
  tt = tm_zero; tt[1] = pb_c(cp[2]); tt[2] = pb_c(2^k);
  \\ the implicit function series u(hh) at the centre, 2-adically (the coefficients need not be exact: the residual
  \\ F(t, P_u) below encloses the error)
  F2 = subst(F, v1, cp[2] + 2^k * 'hh);
  us = (cp[3] + O(2^NP)) + O('hh^(n + 1));
  for (i = 1, 2 + ceil(log(n + 1) / log(2)), us = us - subst(F2, v2, us) / subst(deriv(F2, v2), v2, us));
  Pu = tm_zero; for (i = 0, n, Pu[i + 1] = pb(truncate(polcoef(us, i, 'hh)), PB_MW));
  res = tm_eval2(F, v1, v2, tt, Pu);
  tb = tm_ball(tt); Pb = tm_ball(Pu); ub = pb(cp[3], min(3 * cp[5], 3 * (k + sl)));
  \\ G = sum_j f_j(t) sum_{a + b = j - 1} P_u^a u^b on the balls
  Gb = pb_zero;
  for (j = 1, poldegree(F, v2), my(fj = pb_evp1(polcoef(F, j, v2), v1, tb), s = pb_zero);
    for (a = 0, j - 1, my(m = pb_one); for (q = 1, a, m = pb_mul(m, Pb)); for (q = 1, j - 1 - a, m = pb_mul(m, ub)); s = pb_add(s, m));
    Gb = pb_add(Gb, pb_mul(fj, s)));
  chq(pb_nz(Gb), "tmP: the divided difference G certified nonzero");
  uu = tm_sub(Pu, tm_mul(res, tm_cb(pb_inv(Gb))));
  if (ch == 1, [tt, uu, tm_one], ch == 2, [tt, tm_one, uu], [tm_one, tt, uu]);
}
liftB(P, SB, QF) = {
  my(q = vector(3, j, qeval(QF[j], P)), rr, ss, wh);
  if (pb_nz(q[1]), rr = csqrt(pb_div(q[1], SB[7])));
  if (pb_nz(q[1]) && rr != 0, wh = 1; ss = pb_div(q[2], pb_mul(SB[7], rr)),
    wh = 3; ss = csqrt(pb_div(q[3], SB[7])); chq(ss != 0, "lift"); rr = pb_div(q[2], pb_mul(SB[7], ss)));
  [concat(P, [rr, ss]), [wh, if (wh == 1, rr[1], ss[1])]];
}
liftT(P, SBt, QFt, br) = {
  my(q = vector(3, j, tqeval(QFt[j], P)), al, r, o);
  al = tm_div(q[br[1]], SBt[7]); r = tm_sqrt(al, br[2]);
  o = tm_div(q[2], tm_mul(SBt[7], r));
  concat(P, if (br[1] == 1, [r, o], [o, r]));
}
tmstr(f) = { my(n = #f - 2); Str("[", strjoin(vector(n + 1, i, Str(min(pb_val(f[i]), 9999))), " "), " | R ", min(pb_val(f[n + 2]), 9999), "]"); }

\\ ---------------------------------------------------------------- one box
\\ returns [certified depth of t, margin of Lam t over the need, margin of its part of degree >= 2] (constant boxes)
\\ or [margin of the remainder of the tail, 2 Lam t'(0) in Q_2^6] (tails)
probe_tm(k, SB, SBt, QF, QFt, Fr, Frt, E0, Lam, di, X0, sl, nu, vM, tail) = {
  my(d = DISCS[di], cp = cpointD(d, X0), lb, Dc, R, Rt, Pt, Dt, S, tt, lt, dt, dl, res);
  TM_ETA = 3 * sl;
  res = iferr(
    lb = liftB(ballPt(cp), SB, QF); Dc = bapm_phi(SB, lb[1]); R = pbj_add(Fr, E0, pbj_neg(revD(Dc))); Rt = tmc_all(R);
    Pt = liftT(tmP(cp, sl), SBt, QFt, lb[2]);
    Dt = tapm_phi(SBt, Pt);
    S = tmj_add(Frt, trevD(Dt), Rt);
    tt = ttco(S, k);
    lt = vector(2, i, tm_add(tm_mul(tm_cb(Lam[i][1]), tt[1]), tm_mul(tm_cb(Lam[i][2]), tt[2])));
    [tt, lt], E, Str(E));
  if (type(res) == "t_STR", printf("k=%d disc %d X0 %d s %d: FAIL %s\n", k, di, X0, sl, res); return(0));
  [tt, lt] = res;
  dt = min(pb_val(tm_ball(tt[1])), pb_val(tm_ball(tt[2]))); dl = min(pb_val(tm_ball(lt[1])), pb_val(tm_ball(lt[2])));
  if (!tail,
    my(need = 3 * (nu + 3), vh = min(pb_val(tm_hi(lt[1])), pb_val(tm_hi(lt[2]))), v1 = min(pb_val(lt[1][2]), pb_val(lt[2][2])) + 3 * sl);
    printf("k=%d const disc %d X0 %d s %d nu %d | t: %s %s | Lam t over the box: v >= %d (linear %d, degree >= 2: %d), need %d, margin %d, degree >= 2 margin %d\n",
      k, di, X0, sl, nu, tmstr(tt[1]), tmstr(tt[2]), dl, v1, vh, need, dl - need, vh - need);
    return([dt, dl - need, vh - need]));
  my(vr = min(pb_val(tm_q2(lt[1])), pb_val(tm_q2(lt[2]))), g2 = [pb_scal(2, lt[1][2]), pb_scal(2, lt[2][2])], gc = lvec(g2));
  printf("k=%d tail disc %d Xi %d s %d | t: %s %s | (Lam t - w0 h)/h^2: v >= %d, need vM - 3 s0 = %d, margin %d | 2 w0 in Q_2^6 mod 2^20: %s (prec %s)\n",
    k, di, X0, sl, tmstr(tt[1]), tmstr(tt[2]), vr, vM - 3 * tail, vr - (vM - 3 * tail), apply(c -> red2(c, 20), gc[1]~), gc[2]~);
  [vr - (vM - 3 * tail), gc];
}

\\ tails: [disc, i, s, Xi, s0, vM, g (Lean data t.g)]
{
TAILS = [[[1, 2, 6, 1, 2, 9, [2487464474786852688, 2970955812190878640, 2253358810462344160, 1643501964253933440, 69045205743936640, 3484280535514576640]],
          [1, 0, 6, 0, 2, 9, [2989358559989772016, 1272636743877474064, 2078376642129818784, 0, 0, 0]]],
         [[3, 1, 6, 0, 3, 6, [0, 0, 0, 1378280866709316248, 1861976125032813912, 4348367945323720728]],
          [2, 3, 4, -1, 2, 6, [1253760234980920656, 3505599530101993152, 3786388044172492128, 2737673349208861976, 1044351484718617528, 3236771003752745416]]]];
}
run(k) = {
  my(t0 = getabstime(), SB = bapm_init(k), SBt = tmc_all(SB), QF = [qform(Q1), qform(Q2), qform(Q3)], QFt = apply(Q -> apply(m -> [tm_cb(m[1]), m[2]], Q), QF),
     Fr = frevB(k), Frt = tmc_all(Fr), ei = e0init(Fr, k), E0 = ei[1], Lam = laminit(k, ei[2], ei[3]), B = readvec(Str("data/boxes_twist", k, ".txt")), n = 0, L = List());
  foreach (B, bx, if (n >= LIM, break); if (startswith(bx[4], "constant"),
    my(r = probe_tm(k, SB, SBt, QF, QFt, Fr, Frt, E0, Lam, bx[1], bx[2], bx[3], field(bx[4], "nu = "), field(bx[4], "vM = "), 0));
    n++; listput(L, r)));
  foreach (TAILS[k + 1], tb,
    my(r = probe_tm(k, SB, SBt, QF, QFt, Fr, Frt, E0, Lam, tb[1], tb[4], tb[3], 0, tb[6], tb[5]));
    if (r != 0, my(gd = vector(6, i, red2(tb[7][i], 20)), gp = apply(c -> red2(c, 20), r[2][1]~), gm = apply(c -> red2(-c, 20), r[2][1]~));
      printf("   tail x_%d: Lean t.g mod 2^20 = %s; 2 w0 = +t.g mod 2^min(20, prec): %d, = -t.g: %d\n", tb[2], gd,
        vecmin(vector(6, i, (gp[i] - gd[i]) % 2^min(20, r[2][2][i]) == 0)), vecmin(vector(6, i, (gm[i] - gd[i]) % 2^min(20, r[2][2][i]) == 0)))));
  my(ok = [r | r <- Vec(L), r != 0]);
  printf("k = %d: %d constant boxes, %d Taylor model runs; min margin of Lam t over the need %d; min remainder margin %d; min certified depth of t %d (%d ms)\n",
    k, n, #ok, if (#ok, vecmin(apply(r -> r[2], ok)), "-"), if (#ok, vecmin(apply(r -> r[3], ok)), "-"), if (#ok, vecmin(apply(r -> r[1], ok)), "-"), getabstime() - t0);
}
\\ diagnostic: the Taylor models of every stage for one box (env M4B_DEBUG = [k, disc, X0, s])
dbg(k, di, X0, sl) = {
  my(SB = bapm_init(k), SBt = tmc_all(SB), QF = [qform(Q1), qform(Q2), qform(Q3)], QFt = apply(Q -> apply(m -> [tm_cb(m[1]), m[2]], Q), QF),
     Fr = frevB(k), Frt = tmc_all(Fr), ei = e0init(Fr, k), E0 = ei[1], Lam = laminit(k, ei[2], ei[3]), d = DISCS[di], cp = cpointD(d, X0),
     lb = liftB(ballPt(cp), SB, QF), Dc = bapm_phi(SB, lb[1]), R = pbj_add(Fr, E0, pbj_neg(revD(Dc))), Pt, Dt, Dr, S, tt);
  TM_ETA = 3 * sl;
  Pt = liftT(tmP(cp, sl), SBt, QFt, lb[2]); print("point and lift: ", apply(tmstr, Pt));
  Dt = tapm_phi(SBt, Pt); print("phi u: ", apply(tmstr, Dt[1]), " v: ", apply(tmstr, Dt[2]));
  Dr = trevD(Dt); print("reversed u: ", apply(tmstr, Dr[1]), " v: ", apply(tmstr, Dr[2]));
  print("R u: ", apply(pb_str, R[1]), " v: ", apply(pb_str, R[2]));
  S = tmj_add(Frt, Dr, tmc_all(R)); print("sum u: ", apply(tmstr, S[1]), " v: ", apply(tmstr, S[2]));
  tt = ttco(S, k); print("t: ", apply(tmstr, tt));
  print("Taylor model products: ", TM_CNT);
}
if (getenv("M4B_DEBUG"), my(a = eval(getenv("M4B_DEBUG"))); dbg(a[1], a[2], a[3], a[4]); quit);
run(0); run(1);
quit;
