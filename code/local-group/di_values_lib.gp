\\ di_values_lib.gp: the D_i value chain in exact p-adic arithmetic, as functions (the code of
\\ di_values_probe.gp, factored for the exporters). The caller runs from code/local-group, sets parisizemax and reads
\\ ../descent/descent_data_lib.gp, completion_kv_lib.gp, lean_data_reader.gp first.
NM = 4 * 3^2 * 5 * 7 * 11 * 13; NN = 2^4 * NM;
M0v = [8, 0]; bTv = [[6, 6, 8], [11, 11, 15]];
\\ Mum = [u0, u1, v0, v1]; Quart = [c0, c1, c2, c3]; Sext = [f0, ..., f6] (vector index + 1): the Lean programs
\\ `compAdd`, `compDbl`, `reduce4` of KvArith/Comp/Cantor.lean over the field
INV = List();
inv(c, nm) = { my(v = vpi(c)); listput(INV, v); chq(v < 1000, Str("zero inverse: ", nm)); 1 / c };
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
oncurve(f, D) = { my(U = 'y^2 + D[2]*'y + D[1], V = D[4]*'y + D[3], F = sum(j = 0, 6, f[j + 1] * 'y^j), R = (F - V^2) % U);
  [vpi(polcoef(R, 0, 'y)), vpi(polcoef(R, 1, 'y))] };
cmul(f, n, D) = { my(bn = binary(n), R = D, nd = 0, na = 0);
  for (i = 2, #bn, R = cDbl(f, R); nd++; if (bn[i], R = cAdd(f, R, D); na++)); [R, nd, na] };
chartT(a, R) = [R[2] + 2*a, R[1] + a*R[2] + a^2];
coords(xv) = vector(3, i, cfk(xv, i - 1));
\\ the twist data: [f, a, M0, b, E0, Amat, q, l] (f the Sext of g = (fRev k)^sigma, E0 of baseKv k, q_i and l_i of the
\\ lattice file of M4), k = 0, 1
twistData(k) = {
  my(Fl = vector(7, j, FnDataL[k + 1][8 - j]), fr, f, aa = k, Fa, Fpa, bb, beta1, E0m, M0 = M0v[k + 1],
     Ls = readstr(Str("../covering/data/lattice_int_twist", k, ".gp")), Lt, A = matrix(2, 2), g1);
  Lt = [eval(strsplit(strsplit(Ls[1], "= ")[2], ";")[1]), eval(strsplit(strsplit(Ls[2], "= ")[2], ";")[1])];
  fr = sum(j = 1, 7, nfbasistoalg(nf, Fl[j]~) / 4 * t^(j - 1));
  f = vector(7, j, sg(polcoef(fr, j - 1, t)));
  Fa = sum(j = 0, 6, f[j + 1] * aa^j); Fpa = sum(j = 1, 6, j * f[j + 1] * aa^(j - 1));
  bb = ksqrt(Fa); if (vpi(2 * bb - kv(bTv[k + 1])) < 9, bb = -bb); chq(vpi(2 * bb - kv(bTv[k + 1])) >= 9, "sign of b");
  beta1 = Fpa / (2 * Fa); g1 = -beta1;
  E0m = [aa^2, -2*aa, bb - aa*bb*beta1, bb*beta1];
  chq(vecmin(oncurve(f, E0m)) > 2000, "E0 on the curve");
  A[1, 1] = aa / bb; A[1, 2] = (1 + aa * g1) / bb; A[2, 1] = 1 / bb; A[2, 2] = g1 / bb;
  [f, aa, M0, bb, E0m, A, Lt[1], Lt[2], fr];
}
\\ the point D_i of SelmerSpan (the Lean model of `Dpt k i`) on g, from its stored u_i, v_i (p21_21 data)
dPoint(k, i, T) = {
  my(R = read(Str("../earlier-computations/local_images_twist", k, "_e3.bin")), f = T[1], fr = T[9],
     uu = subst(lift(R[7][i][1]), 'x, t), vv = subst(lift(R[7][i][2]), 'x, t), u0 = polcoef(uu, 0, t), u1 = polcoef(uu, 1, t),
     p, r, U, vr, pk, rk, D, Rm, Z1k, Z0k, nk, best = [-1]);
  p = red(lift(Mod(u1, K21) / Mod(u0, K21))); r = red(lift(1 / Mod(u0, K21))); U = t^2 + p*t + r;
  vr = red(lift(Mod(Mod(1, K21) * (t^3 * subst(vv, t, 1/t)), Mod(1, K21) * U)));
  pk = sg(p); rk = sg(r);
  Rm = red(lift(Mod(Mod(1, K21) * fr, Mod(1, K21) * U)));
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
  D;
}
\\ the chain R_0 = N D + E0, R_{j+1} = 2 R_j - E0 up to the least J with err - sc >= 3 q (as di_values_probe.gp), returns
\\ [J, R_J, t_J, D = min v(t_J), err = 2D - M0 - 3]
dChain(T, D, qi) = {
  my(f = T[1], aa = T[2], M0 = T[3], E0m = T[5], nE0 = mneg(T[5]), Rj, tt, Dm, err, sc);
  Rj = cAdd(f, cmul(f, NN, D)[1], E0m);
  for (j = 0, 200,
    tt = chartT(aa, Rj); Dm = min(vpi(tt[1]), vpi(tt[2])); err = 2 * Dm - M0 - 3; sc = 3 * (j + valuation(NN, 2));
    if (err - sc >= 3 * qi, return([j, Rj, tt, Dm, err]));
    Rj = cAdd(f, cDbl(f, Rj), nE0));
  error("no J");
}
\\ an element x of K_v as ball data [c0, c1, c2, e, r] modulo 2^P: 2^e x = c0 + c1 pv + c2 pv^2 + O(pv^r)
toBall(x, P) = {
  my(cs = coords(x), e = 0, c, pr = 3 * P);
  for (i = 1, 3, if (cs[i] != 0, e = max(e, -valuation(cs[i], 2))));
  c = vector(3, i, my(y = cs[i] * 2^e); if (type(y) == "t_PADIC", pr = min(pr, 3 * padicprec(y, 2)));
    if (y == 0, 0, lift(Mod(truncate(y), 2^P))));
  concat(c, [e, pr]);
}
