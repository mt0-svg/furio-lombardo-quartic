\\ count_base_points.gp: base points for R7's Setup at each place of the count, searched
\\ among a = i + j b + l b^2 in K21 (b the generator of K21, |i| <= 8, |j| <= 2, |l| <= 1) and a = i / 2^s, i / 7^s:
\\ conditions as count_local_facts.gp (b): f0 = fRev(a) != 0, r4 != 0, r6 != 0, f0 a square in K_w. Prints, per twist and
\\ place, the first hits in the search order (smallest height first) with the valuation of f0 at the place.
\\ Run from code/selmer-local-conditions: gp -q count_base_points.gp < /dev/null > count_base_points.out 2>&1
default(parisizemax, 2*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
o = Mod(1, K21);
red(g) = lift(o * g);
P2 = idealprimedec(nf, 2); P7 = idealprimedec(nf, 7);
pv = [pr | pr <- P2, pr.e == 3][1]; pw2 = [pr | pr <- P2, pr.e == 12][1]; pw3 = [pr | pr <- P2, pr.e == 6][1]; p7 = P7[1];
PL = [["v", pv], ["w2", pw2], ["w3", pw3], ["7", p7]];
sq(x, pr) = nfislocalpower(nf, pr, x, 2);
cands = List();
for (h = 0, 11, for (i = -8, 8, for (j = -2, 2, for (l = -1, 1, if (abs(i) + 3 * abs(j) + 5 * abs(l) == h, listput(cands, i + j * b + l * b^2))))));
for (s = 1, 3, for (i = -7, 7, if (i % 2, listput(cands, i / 2^s)); if (i % 7, listput(cands, i / 7^s))));
print(#cands, " candidates");
{
  for (k = 0, 1,
    my(F = if (k == 0, F0, F1), fr = polrecip(F), found = vector(4, i, List()));
    foreach(cands, a,
      if (vecmin(apply(L -> #L, found)) >= 3, break);
      my(fT = red(subst(fr, t, t + a)), f0 = polcoef(fT, 0, t), P, R);
      if (f0 == 0, next);
      P = red(truncate(sqrt(Ser(o * fT / f0, t, 4))));
      R = red(fT - f0 * P^2);
      if (valuation(R, t) < 4 || poldegree(R, t) > 6, error("bad remainder at a = ", a));
      if (polcoef(R, 4, t) == 0 || polcoef(R, 6, t) == 0, next);
      for (w = 1, 4, if (#found[w] < 3 && sq(f0, PL[w][2]), listput(found[w], [a, idealval(nf, f0, PL[w][2])]))));
    for (w = 1, 4, print("twist ", k, " place ", PL[w][1], ": ", Vec(found[w]))));
}
print("DONE");
