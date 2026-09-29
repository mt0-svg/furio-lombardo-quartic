\\ count_base_abscissas.gp: base abscissas of C_1 : y^2 = fRev 1(x) over K_w at w2, w3 written on M2's generator alpha_w of the
\\ prime (selmer_rows_lib.gp SB_AL, lean/FurioLombardo/M2/SpecialData.lean al2, al3), the uniformizer of the local side's field
\\ layer: x = alpha^j sum_{i < m} c_i alpha^i, c_i in {0, 1}, c_0 = 1, j in [-3, 2], m = 8 (as count_local_points.gp with
\\ pi = alpha). A hit: f(x) a square in K_w (nfislocalpower), f(x) != 0, N0 != 0 (R7's tN0 of the coefficients of
\\ f(X + x), the numerator of R0), and v_w(N0). Twist 0 at w2, w3: x = 0 checked the same way.
\\ Run from code/selmer-local-conditions: gp -q count_base_abscissas.gp < /dev/null > count_base_abscissas.out 2>&1
default(parisizemax, 10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
o = Mod(1, K21); red(g) = lift(o * g);
{SB_AL = [[0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0],
         [-2, 2, 0, 1, 0, -2, 1, -1, 0, 2, 0, 1, 2, -1, 0, 2, 1, -1, 0, 1, -1],
         [1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         [-2, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1]];}
P2 = idealprimedec(nf, 2);
pw2 = [pr | pr <- P2, pr.e == 12][1]; pw3 = [pr | pr <- P2, pr.e == 6][1];
al2 = lift(nfbasistoalg(nf, SB_AL[2]~)); al3 = lift(nfbasistoalg(nf, SB_AL[3]~));
printf("alpha_2 generates w2: %d, alpha_3 generates w3: %d\n", idealhnf(nf, al2) == idealhnf(nf, pw2), idealhnf(nf, al3) == idealhnf(nf, pw3));
tN0(c0, c1, c2, c3, c4) = 64*c0^3*c4 - 16*c0^2*c2^2 - 32*c0^2*c1*c3 + 24*c0*c1^2*c2 - 5*c1^4;
test(fr, pr, x) = {
  my(fT = red(subst(fr, t, t + x)), f0 = polcoef(fT, 0, t), N0);
  if (f0 == 0 || !nfislocalpower(nf, pr, f0, 2), return(0));
  N0 = red(tN0(polcoef(fT, 0, t), polcoef(fT, 1, t), polcoef(fT, 2, t), polcoef(fT, 3, t), polcoef(fT, 4, t)));
  if (N0 == 0, return(0));
  [idealval(nf, f0, pr), idealval(nf, N0, pr)];
}
search(fr, pr, al, m, jr, nmax) = {
  my(hits = List(), cnt = 0);
  for (j = jr[1], jr[2],
    forvec(c = vector(m - 1, i, [0, 1]),
      my(x = red((1 + sum(i = 1, m - 1, c[i] * al^i)) * al^j), r);
      cnt++; r = test(fr, pr, x);
      if (r != 0, listput(hits, [j, concat([1], c), r[1], r[2]]); if (#hits >= nmax, return([cnt, Vec(hits)])))));
  [cnt, Vec(hits)];
}
{
  foreach([[pw2, "w2"], [pw3, "w3"]], T,
    my(r = test(polrecip(F0), T[1], 0));
    printf("twist 0 place %s, x = 0: [v(f0), v(N0)] = %s\n", T[2], r));
  foreach([[pw2, al2, "w2"], [pw3, al3, "w3"]], T,
    my(t0 = getabstime(), r = search(polrecip(F1), T[1], T[2], 8, [-3, 2], 3));
    printf("twist 1 place %s (e = %d): %d abscissas tried, hits [j, digits c_0..c_7 on alpha, v(f0), v(N0)] %s (%d ms)\n",
      T[3], T[1].e, r[1], r[2], getabstime() - t0));
}
print("DONE");
