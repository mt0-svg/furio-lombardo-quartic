\\ count_square_classes.gp: the square classes the count needs at w2, w3 (residue field F_2) and at the place above 7,
\\ relative to M2's generators alpha_w (selmer_rows_lib.gp SB_AL). fRev_k = c_k q h with q, h monic and twist independent
\\ (selmer_rows_lib.gp), d = disc q, ndK = N(D) = D0^2 - d D1^2 (M3a's ND, twist independent; its class is that of disc h).
\\ Depth at a dyadic w with residue F_2 and e = v_w(2): for z with v = v_w(z) even, s runs over 1 + sums of alpha^i
\\ (greedy: while t = v_w(z - alpha^v s^2) - v is even and < 2e, s += alpha^(t/2), which raises t). Then t odd < 2e: z is not a
\\ square, with certificate ||z / (alpha^(v/2) s)^2 - 1|| = ||alpha||^t (SquareLemmas.lean sb_not_isSquare_of_norm_sub_one);
\\ t = 2e: not a square (unramified class, 1 + 4u with u a unit, u = y^2 + y has no solution mod alpha in F_2);
\\ t > 2e: a square. v odd: not a square (sb_not_isSquare_of_norm_odd).
\\ Also the base abscissas of the count (count_base_abscissas.out at w2, w3; count_base_point_w7.out at 7): the depth of f(x).
\\ Run from code/selmer-local-conditions: gp -q count_square_classes.gp < /dev/null > count_square_classes.out 2>&1
default(parisizemax, 10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
o = Mod(1, K21); red(g) = lift(o * g);
{SB_AL = [[0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0],
         [-2, 2, 0, 1, 0, -2, 1, -1, 0, 2, 0, 1, 2, -1, 0, 2, 1, -1, 0, 1, -1],
         [1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         [-2, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1]];}
P2 = idealprimedec(nf, 2); p7 = idealprimedec(nf, 7)[1];
pw2 = [pr | pr <- P2, pr.e == 12][1]; pw3 = [pr | pr <- P2, pr.e == 6][1];
al = vector(4, i, lift(nfbasistoalg(nf, SB_AL[i]~)));
printf("alpha generates: w2 %d, w3 %d, 7 %d\n", idealhnf(nf, al[2]) == idealhnf(nf, pw2), idealhnf(nf, al[3]) == idealhnf(nf, pw3), idealhnf(nf, al[4]) == idealhnf(nf, p7));
vw(z, pr) = if (z == 0, oo, idealval(nf, z, pr));
\\ fRev_k = c_k q h
fr = vector(2, k, polrecip(if (k == 1, F0, F1)));
cc = vector(2, k, polcoef(fr[k], 6, t)); inv(c) = lift(1 / (o * c));
fm = red(fr[1] * inv(cc[1])); fa = nffactor(nf, fm); qq = fa[1, 1]; if (poldegree(qq, t) != 2, qq = fa[2, 1]); hh = red(fm / (o * qq));
printf("q, h monic of degrees %d, %d, twist independent: %d\n", poldegree(qq, t), poldegree(hh, t), red(fr[2] - cc[2] * qq * hh) == 0);
dd = red(polcoef(qq, 1, t)^2 - 4 * polcoef(qq, 0, t));
\\ h = A^2 - d B^2 with Lean's data (M3a/LocalData.lean abData, denominators maDen = 92, mbDen = 184, twist 0 row)
{
  my(AB = [[-2622, 898, 1361, 657, 934, -1872, 139, -260, 1243, 1291, 888, 1061, 3443, -1487, 1578, 1171, 2191, 93, 748, 2173, -352],
  [-1396, 278, 255, 730, -337, 416, -1164, -204, -228, -553, -239, 752, -1020, 24, 359, 813, 438, -1090, 652, -242, 317],
  [358, -1154, -47, -39, -19, -451, -381, 62, 329, -50, 10, -446, -435, 460, 37, -77, -135, -35, 173, -162, 11],
  [-66, 298, -49, 61, -134, 329, 16, -54, -277, -205, -128, 77, -320, 12, -141, 78, -130, -168, -94, -200, 67]], a0, a1, b0, b1);
  a0 = lift(nfbasistoalg(nf, AB[1]~)) / 92; a1 = lift(nfbasistoalg(nf, AB[2]~)) / 92;
  b0 = lift(nfbasistoalg(nf, AB[3]~)) / 184; b1 = lift(nfbasistoalg(nf, AB[4]~)) / 184;
  printf("Lean's normal form: h = A^2 - d B^2: %d\n", red(hh - ((t^2 + a1 * t + a0)^2 - dd * (b1 * t + b0)^2)) == 0);
  D0 = red(a1^2 + dd * b1^2 - 4 * a0); D1 = red(2 * a1 * b1 - 4 * b0); ND = red(D0^2 - dd * D1^2);
}
depth(z, pr, a, E) = {
  my(v = vw(z, pr), s = 1, t);
  if (v % 2, return([v, "odd valuation", 0]));
  for (i = 1, 4 * E, t = vw(red(z - a^v * s^2), pr) - v;
    if (t % 2 || t >= 2 * E, break);
    s = red(s + a^(t / 2)));
  [v, t, s];
}
cls(r, E) = if (type(r[2]) == "t_STR", "not a square (odd valuation)", if (r[2] % 2 && r[2] < 2 * E, "not a square (odd depth)", if (r[2] == 2 * E, "not a square (depth 2e)", "square")));
{
  foreach([[pw2, al[2], "w2"], [pw3, al[3], "w3"]], T,
    my(pr = T[1], a = T[2], E = pr.e, r);
    r = depth(dd, pr, a, E); printf("%s (e = %d): d: v = %d, depth %s: %s\n", T[3], E, r[1], r[2], cls(r, E));
    for (k = 1, 2, r = depth(cc[k], pr, a, E); printf("%s: c_%d: v = %d, depth %s: %s\n", T[3], k - 1, r[1], r[2], cls(r, E))));
  printf("7: v(ND) = %d, v(c_1) = %d, v(c_0) = %d\n", vw(ND, p7), vw(cc[2], p7), vw(cc[1], p7));
  \\ base abscissas: twist 0 at w2, w3: x = 0; twist 1 at w2: 1 + a + a^2 + a^3 + a^5 + a^7, at w3: 1 + a^5 (count_base_abscissas.out)
  my(pts = [[1, pw2, al[2], 0, "w2"], [1, pw3, al[3], 0, "w3"],
            [2, pw2, al[2], 1 + al[2] + al[2]^2 + al[2]^3 + al[2]^5 + al[2]^7, "w2"], [2, pw3, al[3], 1 + al[3]^5, "w3"]]);
  foreach(pts, P, my(k = P[1], x = red(P[4]), f0 = red(subst(fr[k], t, x)), r = depth(f0, P[2], P[3], P[2].e));
    printf("twist %d at %s, x = %s: f(x): v = %d, depth %s: %s\n", k - 1, P[5], if (P[4] == 0, "0", "(count_6)"), r[1], r[2], cls(r, P[2].e)));
}
print("DONE");
