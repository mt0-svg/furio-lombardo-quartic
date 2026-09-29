\\ di_values_probe.gp: the D_i value chain of hD / hBD in exact p-adic arithmetic (numerical probe,
\\ not a certificate). For each twist k and point D_i of SelmerSpan (on g = (fRev k)^sigma, the Lean model of `Dpt k i`):
\\   Q0 = N D_i (N = 2^4 NM, the multiple of p21_45's pbj_log), by left-to-right double-and-add from D_i with the Lean
\\   programs `compAdd`, `compDbl`, `reduce4` (KvArith/Comp/Cantor.lean) over the field;
\\   R_0 = Q0 + E0 (E0 = [(X - a)^2, v0(X - a)], a = aK k = k, v0 = b (1 + beta1 X) of `baseKv k`, 2b = bT k mod 2^3);
\\   R_{j+1} = (2 R_j) + (-E0), so R_j = 2^j Q0 + E0;
\\ and at each j the chart coordinates t = chartT a R_j, w = chartW a R_j: v(t0), v(t1), the conditions of
\\ `resQ_branch_ne_zero` (m >= 7) and of B1 (v(t_i) >= M0 + 4), and the valuations of every inverted quantity (they set
\\ the precision loss of ball arithmetic). Then lamK(D_i) ~ Amat t_J / (2^J N) with the error |pv|^(2D - M0 - 3) of
\\ `norm_lamK_chart_sub_le` (D = min v(t_i)), the least J for the precision q_i of hBD, and a known-answer test against
\\ M4's lattice data l_i (code/covering/data/lattice_int_twist<k>.gp) modulo the proved-error precision.
\\ Run from code/local-group:
\\   gp -q ../local-group/di_values_probe.gp > ../local-group/di_values_probe.out
default(parisizemax, 3*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../descent/descent_data_lib.gp");
read("completion_kv_lib.gp");
read("lean_data_reader.gp");
NM = 4 * 3^2 * 5 * 7 * 11 * 13; NN = 2^4 * NM;
M0v = [8, 0]; bTv = [[6, 6, 8], [11, 11, 15]];
JMAX = 70;
\\ inverted quantities of the current program run: [name, valuation]
INV = List();
inv(c, nm) = { my(v = vpi(c)); listput(INV, v); chq(v < 1000, Str("zero inverse: ", nm)); 1 / c };
\\ Mum = [u0, u1, v0, v1]; Quart = [c0, c1, c2, c3]; Sext = [f0, ..., f6] (vector index + 1)
compAdd(D, E) = {
  my(g0 = D[1] - E[1], g1 = D[2] - E[2], N = g0*g0 - g0*g1*E[2] + g1*g1*E[1], Ni = inv(N, "compAdd N"),
     i0 = (g0 - g1*E[2])*Ni, i1 = -(g1*Ni), d0 = E[3] - D[3], d1 = E[4] - D[4],
     k0 = d0*i0 - d1*i1*E[1], k1 = d0*i1 + d1*i0 - d1*i1*E[2]);
  [[D[1]*E[1], D[1]*E[2] + D[2]*E[1], D[1] + D[2]*E[2] + E[1], D[2] + E[2]],
   [D[3] + D[1]*k0, D[4] + D[2]*k0 + D[1]*k1, k0 + D[2]*k1, k1]];
}
compDbl(f, D) = {
  my(u0 = D[1], u1 = D[2], v0 = D[3], v1 = D[4], g3 = f[4], g2 = f[3] - v1*v1, h4 = f[7], h3 = f[6] - u1*h4,
     h2 = f[5] - u1*h3 - u0*h4, h1 = g3 - u1*h2 - u0*h3, h0 = g2 - u1*h1 - u0*h2, q1 = h3 - u1*h4,
     q0 = h2 - u1*q1 - u0*h4, e1 = h1 - u1*q0 - u0*q1, e0 = h0 - u0*q0, b0 = v0 + v0, b1 = v1 + v1,
     N = b0*b0 - b0*b1*u1 + b1*b1*u0, Ni = inv(N, "compDbl N"), i0 = (b0 - b1*u1)*Ni, i1 = -(b1*Ni),
     k0 = e0*i0 - e1*i1*u0, k1 = e0*i1 + e1*i0 - e1*i1*u1);
  [[u0*u0, u0*u1 + u1*u0, u0 + u1*u1 + u0, u1 + u1], [v0 + u0*k0, v1 + u1*k0 + u0*k1, k0 + u1*k1, k1]];
}
reduce4(f, U, w) = {
  my(g6 = f[7] - w[4]*w[4], g5 = f[6] - (w[3]*w[4] + w[4]*w[3]), g4 = f[5] - (w[2]*w[4] + w[4]*w[2] + w[3]*w[3]),
     q1 = g5 - g6*U[4], q0 = g4 - q1*U[4] - g6*U[3], li = inv(g6, "reduce4 g6"), s1 = q1*li, s0 = q0*li,
     t1 = -((w[4]*(s1*s1 - s0) - w[3]*s1) + w[2]), t0 = -((w[4]*(s1*s0) - w[3]*s0) + w[1]));
  [s0, s1, t0, t1];
}
cAdd(f, D, E) = { my(r = compAdd(D, E)); reduce4(f, r[1], r[2]) };
cDbl(f, D) = { my(r = compDbl(f, D)); reduce4(f, r[1], r[2]) };
mneg(D) = [D[1], D[2], -D[3], -D[4]];
\\ on the curve: u | f - v^2 (the remainder, as a vector of two valuations)
oncurve(f, D) = { my(U = 'y^2 + D[2]*'y + D[1], V = D[4]*'y + D[3], F = sum(j = 0, 6, f[j + 1] * 'y^j), R = (F - V^2) % U);
  [vpi(polcoef(R, 0, 'y)), vpi(polcoef(R, 1, 'y))] };
\\ left-to-right double-and-add from D
cmul(f, n, D) = { my(bn = binary(n), R = D, nd = 0, na = 0);
  for (i = 2, #bn, R = cDbl(f, R); nd++; if (bn[i], R = cAdd(f, R, D); na++)); [R, nd, na] };
chartT(a, R) = [R[2] + 2*a, R[1] + a*R[2] + a^2];
chartW(a, R) = [R[3] + a*R[4], R[4]];
coords(xv) = vector(3, i, cfk(xv, i - 1));
res = List();
{
  for (k = 1, 2,
    my(R = read(Str("../earlier-computations/local_images_twist", k - 1, "_e3.bin")), Fl = vector(7, j, FnDataL[k][8 - j]),
       fr, f, aa = k - 1, Fa, Fpa, bb, beta1, E0m, nE0, M0 = M0v[k], Ls = readstr(Str("../covering/data/lattice_int_twist", k - 1, ".gp")), Lt);
    \\ the first two lines of the lattice file: the precisions q_i and the centres l_i
    Lt = [eval(strsplit(strsplit(Ls[1], "= ")[2], ";")[1]), eval(strsplit(strsplit(Ls[2], "= ")[2], ";")[1])];
    fr = sum(j = 1, 7, nfbasistoalg(nf, Fl[j]~) / 4 * t^(j - 1));
    f = vector(7, j, sg(polcoef(fr, j - 1, t)));
    \\ E0 of baseKv k: fK = F(X + a), b^2 = fK(0) = F(a), 2b = bT k mod 2^3, v0 = b + b beta1 X, beta1 = F'(a) / (2 F(a))
    Fa = sum(j = 0, 6, f[j + 1] * aa^j); Fpa = sum(j = 1, 6, j * f[j + 1] * aa^(j - 1));
    bb = ksqrt(Fa); if (vpi(2 * bb - kv(bTv[k])) < 9, bb = -bb); chq(vpi(2 * bb - kv(bTv[k])) >= 9, "sign of b");
    beta1 = Fpa / (2 * Fa);
    E0m = [aa^2, -2*aa, bb - aa*bb*beta1, bb*beta1];
    chq(oncurve(f, E0m) == [vpi(0), vpi(0)] || vecmin(oncurve(f, E0m)) > 2000, "E0 on the curve");
    nE0 = mneg(E0m);
    my(A = matrix(2, 2), g1 = -beta1);
    A[1, 1] = aa / bb; A[1, 2] = (1 + aa * g1) / bb; A[2, 1] = 1 / bb; A[2, 2] = g1 / bb;
    printf("==== twist %d: a = %d, M0 = %d, v(b) = %d, v(Amat) = %s, N = 2^4 NM = %d (v2 = %d)\n", k - 1, aa, M0, vpi(bb),
      [vpi(A[1,1]), vpi(A[1,2]), vpi(A[2,1]), vpi(A[2,2])], NN, valuation(NN, 2));
    for (i = 1, 7,
      my(uu = subst(lift(R[7][i][1]), 'x, t), vv = subst(lift(R[7][i][2]), 'x, t), u0 = polcoef(uu, 0, t), u1 = polcoef(uu, 1, t),
         p, r, U, vr, pk, rk, D, Q0, cm, Rj, tt, ww, dep, qi = Lt[1][i], li = Lt[2][i], log0, Jneed = -1, Jd = -1, kat = "", invs);
      p = red(lift(Mod(u1, K21) / Mod(u0, K21))); r = red(lift(1 / Mod(u0, K21))); U = t^2 + p*t + r;
      vr = red(lift(Mod(Mod(1, K21) * (t^3 * subst(vv, t, 1/t)), Mod(1, K21) * U)));
      pk = sg(p); rk = sg(r);
      \\ the exact V (as SelmerSpan/Dpt.lean): Z1 X + Z0 = 4 (g mod U), n^2 = Z0^2 - p Z1 Z0 + r Z1^2, a^2 = 2 Z0 - p Z1 + 2 n,
      \\ V = Z1/(2a) X + (a/4 + Z1 p/(4a)), with the signs of the stored v_i
      my(Rm = red(lift(Mod(Mod(1, K21) * fr, Mod(1, K21) * U))), Z1k, Z0k, nk, best = [-1]);
      Z1k = 4 * sg(polcoef(Rm, 1, t)); Z0k = 4 * sg(polcoef(Rm, 0, t));
      nk = ksqrt(Z0k^2 - pk * Z1k * Z0k + rk * Z1k^2);
      foreach ([1, -1], sn, my(n1 = sn * nk, w2 = 2 * Z0k - pk * Z1k + 2 * n1);
        if (ksq(w2), my(a1 = ksqrt(w2));
          foreach ([1, -1], sa, my(a2 = sa * a1, b2 = Z1k / (2 * a2), c2 = a2 / 4 + b2 * pk / 2, dmin);
            dmin = min(vpi(sg(polcoef(vr, 1, t)) - b2), vpi(sg(polcoef(vr, 0, t)) - c2));
            if (dmin > best[1], best = [dmin, b2, c2]))));
      chq(best[1] >= 60, "V agrees with the stored v_i");
      D = [rk, pk, best[3], best[2]];
      chq(vecmin(oncurve(f, D)) > 2000, Str("D_", i, " on g"));
      INV = List();
      cm = cmul(f, NN, D); Q0 = cm[1];
      Rj = cAdd(f, Q0, E0m);
      invs = vecmax(Vec(INV));
      my(tr = List(), ok7 = -1, okB = -1);
      for (j = 0, JMAX,
        tt = chartT(aa, Rj); ww = chartW(aa, Rj);
        dep = [vpi(tt[1]), vpi(tt[2])];
        my(m7 = min(dep[1] - aa, dep[2] - 2 * aa), wb = [vpi(ww[1] - bb), vpi(2 * bb), vpi(ww[2]) + aa - vpi(bb)], Dm = vecmin(dep));
        if (ok7 < 0 && m7 >= 7 && wb[1] > wb[2] && wb[3] >= 0, ok7 = j);
        if (okB < 0 && Dm >= M0 + 4, okB = j);
        \\ hD: v(lamK(D_i)) >= 0 needs min(v(Amat t), 2D - M0 - 3) >= 3 (j + v2 N)
        my(lin = A * tt~, vlin = min(vpi(lin[1]), vpi(lin[2])), err = 2 * Dm - M0 - 3, sc = 3 * (j + valuation(NN, 2)));
        if (Jd < 0 && ok7 >= 0 && okB >= 0 && min(vlin, err) >= sc, Jd = j);
        if (Jneed < 0 && ok7 >= 0 && okB >= 0 && err - sc >= 3 * qi, Jneed = j;
          \\ KAT: coordinates of Amat t / (2^j N) against l_i, modulo 2^floor((err - sc)/3)
          my(lam = [lin[1] / (2^j * NN), lin[2] / (2^j * NN)], cv = concat(coords(lam[1]), coords(lam[2])), pr = floor((err - sc) / 3), bad = 0);
          for (c = 1, 6, my(dd = cv[c] - li[c]); if (dd != 0 && valuation(dd, 2) < min(pr, qi), bad++));
          kat = Str("KAT lam(D_i) = l_i mod 2^", min(pr, qi), ": ", if (bad == 0, "pass", Str("FAIL (", bad, " coordinates)"))));
        if (j <= 3 || j % 10 == 0 || j == Jneed, listput(tr, [j, dep, vlin]));
        if (Jneed >= 0, break);
        INV = List();
        Rj = cAdd(f, cDbl(f, Rj), nE0);
        invs = max(invs, vecmax(Vec(INV))));
      printf("  D_%d: N D: %d doublings, %d additions; R_0 = N D + E0: v(t) = %s; resQ (m >= 7) from j = %d, B1 from j = %d; hD from j = %d; q = %d needs J = %d; max v(inverted) = %d; %s\n",
        i, cm[2], cm[3], tr[1][2], ok7, okB, Jd, qi, Jneed, invs, kat);
      printf("       trace [j, v(t0), v(t1), v(Amat t)]: %s\n", Vec(tr));
      listput(res, [k - 1, i, cm[2], cm[3], Jd, Jneed, invs])));
  printf("summary [k, i, doublings in N D, additions in N D, J for hD, J for hBD, max v(inverted)]: %s\n", Vec(res));
}
quit;
