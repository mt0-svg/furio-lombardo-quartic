\\ count_local_points.gp: does C_k : y^2 = fRev k(x) have a K_w-point with y != 0 at w2, w3 (twist 1) and at the place
\\ above 7 (twists 0, 1)? Exhaustive over x = u pi^j (x = sum_{i < m} c_i pi^i times pi^j, c_i in a residue set, j in
\\ [-3, 2]) at a fixed precision m: a hit is an x in K21 with f(x) a local square (nfislocalpower), r4 != 0, r6 != 0
\\ as in count_local_facts.gp; the first hits are printed. pi: an element of K21 of valuation 1 at the place.
\\ Run from code/selmer-local-conditions: gp -q count_local_points.gp < /dev/null > count_local_points.out 2>&1
default(parisizemax, 2*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
o = Mod(1, K21);
red(g) = lift(o * g);
P2 = idealprimedec(nf, 2); P7 = idealprimedec(nf, 7);
pw2 = [pr | pr <- P2, pr.e == 12][1]; pw3 = [pr | pr <- P2, pr.e == 6][1]; p7 = P7[1];
unif(pr) = {my(g = nfbasistoalg(nf, pr.gen[2])); if (idealval(nf, g, pr) == 1, lift(g), my(g2 = lift(g + pr.p)); if (idealval(nf, g2, pr) == 1, g2, error("no uniformizer")))};
sq(x, pr) = nfislocalpower(nf, pr, x, 2);
\\ residue representatives: {0, 1} at f = 1; at 7 (f = 3) the residue field F_343 from a basis of O/pr
resreps(pr) = if (pr.f == 1, vector(pr.p, i, i - 1), my(B = [1, b, b^2], R = List()); forvec(c = vector(3, i, [0, pr.p - 1]), listput(R, c[1] + c[2] * b + c[3] * b^2)); Vec(R));
search(fr, pr, m, jr, nmax) = {
  my(pi = unif(pr), RR = resreps(pr), hits = List(), cnt = 0);
  if (pr.f > 1, RR = RR[1 .. min(#RR, 60)]);
  for (j = jr[1], jr[2],
    forvec(c = vector(m, i, [1, #RR]),
      my(u = sum(i = 1, m, RR[c[i]] * pi^(i - 1)), x, fT, f0, P, R);
      if (RR[c[1]] == 0, next);
      x = red(u * pi^j); cnt++;
      fT = red(subst(fr, t, t + x)); f0 = polcoef(fT, 0, t);
      if (f0 == 0, next);
      if (!sq(f0, pr), next);
      P = red(truncate(sqrt(Ser(o * fT / f0, t, 4)))); R = red(fT - f0 * P^2);
      if (polcoef(R, 4, t) == 0 || polcoef(R, 6, t) == 0, next);
      listput(hits, [j, vector(m, i, RR[c[i]]), idealval(nf, f0, pr)]);
      if (#hits >= nmax, return([cnt, Vec(hits)]))));
  [cnt, Vec(hits)];
}
{
  my(tests = [[1, pw2, "w2", 8], [1, pw3, "w3", 8], [0, p7, "7", 2], [1, p7, "7", 2]]);
  foreach(tests, T,
    my(k = T[1], fr = polrecip(if (k == 0, F0, F1)), r, t0 = getabstime());
    r = search(fr, T[2], T[4], [-3, 2], 3);
    printf("twist %d place %s (e = %d, f = %d, precision %d): %d abscissas tried, hits %s (%d ms)\n", k, T[3], T[2].e, T[2].f, T[4], r[1], r[2], getabstime() - t0));
}
print("DONE");
