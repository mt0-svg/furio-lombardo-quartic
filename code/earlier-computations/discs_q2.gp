\\ discs_q2.gp: a partition of C(Q_2) into discs on which one affine coordinate is a parameter.
\\ C : Fq(x, y, z) = 0 (the model of p21_9_tiny.gp; P0 = (0:0:1), P1 = (1:1:1), P2 = (2:0:1), P3 = (-1:0:1)).
\\ P^2(Q_2) is the disjoint union of the charts z = 1 (x, y in Z_2), y = 1 (x in Z_2, z in 2Z_2), x = 1 (y, z in 2Z_2).
\\ A box B = (a0 + 2^k X, b0 + 2^k Y), X, Y in Z_2, with G(X, Y) = F(a0 + 2^k X, b0 + 2^k Y) = sum g_ij X^i Y^j:
\\  - no zero in B if v(g_00) < v(g_ij) for all (i, j) != (0, 0);
\\  - Y-parametrised if v(g_ij) > v(g_01) for all j >= 1, (i, j) != (0, 1) (then Y -> G(X, Y) scales distances by
\\    exactly 2^-v(g_01) for every X, so G(X, .) has a root iff v(G(X, 0)) >= v(g_01), and then exactly one) and
\\    v(g_i0) >= v(g_01) for all i (so every X in Z_2 gives exactly one point): the zeros in B are (X, Y(X)), X in Z_2;
\\  - X-parametrised symmetrically; otherwise B is split into its 4 sub-boxes.
\\ Output: DISCS = list of [chart, a0, b0, k, par] (par 2: Y = Y(X), the parameter is X; par 1: X = X(Y), the parameter
\\ is Y), saved to discs_q2.txt.
\\ Known answer tests: P0..P3 lie in exactly one disc each; the discs are pairwise disjoint (by construction: the boxes
\\ are disjoint); a sample of 2-adic points of C found by an independent Newton search lies in some disc.
default(parisizemax, 2*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
chq(c, msg) = if (!c, error("check failed: ", msg));
Fq = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
FA = [substvec(Fq, [z], [1]), substvec(Fq, [y], [1]), substvec(Fq, [x], [1])];   \\ in (x, y), (x, z), (y, z)
VA = [[x, y], [x, z], [y, z]];
KMAX = 40;
v2(c) = if (c == 0, oo, valuation(c, 2));
coefs(G) = { my(L = List()); for (i = 0, poldegree(G, 'X), my(Gi = polcoef(G, i, 'X)); for (j = 0, poldegree(Gi, 'Y), listput(L, [i, j, polcoef(Gi, j, 'Y)]))); Vec(L); }
classify(G) = {
  my(C = coefs(G), g00 = oo, g01 = oo, g10 = oo, okY = 1, okX = 1, full = 1, fullx = 1, zero = 1);
  foreach (C, c, if (c[1] == 0 && c[2] == 0, g00 = v2(c[3])); if (c[1] == 0 && c[2] == 1, g01 = v2(c[3])); if (c[1] == 1 && c[2] == 0, g10 = v2(c[3])));
  foreach (C, c, if (c[1] + c[2] > 0 && v2(c[3]) <= g00, zero = 0));
  if (zero, return(0));
  foreach (C, c, if (c[2] >= 1 && [c[1], c[2]] != [0, 1] && v2(c[3]) <= g01, okY = 0); if (c[2] == 0 && v2(c[3]) < g01, full = 0));
  if (g01 < oo && okY && full, return(2));
  foreach (C, c, if (c[1] >= 1 && [c[1], c[2]] != [1, 0] && v2(c[3]) <= g10, okX = 0); if (c[1] == 0 && v2(c[3]) < g10, fullx = 0));
  if (g10 < oo && okX && fullx, return(1));
  -1;
}
DISCS = List();
explore(ch, a0, b0, k) = {
  my(G = substvec(FA[ch], VA[ch], [a0 + 2^k * 'X, b0 + 2^k * 'Y]), c);
  chq(k <= KMAX, "recursion depth");
  c = classify(G);
  if (c == 0, return);
  if (c > 0, listput(DISCS, [ch, a0, b0, k, c]); return);
  for (e1 = 0, 1, for (e2 = 0, 1, explore(ch, a0 + e1 * 2^k, b0 + e2 * 2^k, k + 1)));
}
explore(1, 0, 0, 0);
explore(2, 0, 0, 1); explore(2, 1, 0, 1);
explore(3, 0, 0, 1);
DISCS = Vec(DISCS);
printf("%d discs; charts %s; depths %s\n", #DISCS, vector(3, ch, #[d | d <- DISCS, d[1] == ch]), vecsort(apply(d -> d[4], DISCS)));
\\ membership of a point (chart coordinates) in a disc
indisc(d, p) = { my(k = d[4]); valuation(p[1] - d[2], 2) >= k && valuation(p[2] - d[3], 2) >= k; };
chartof(P) = { my(vx = v2(P[1]), vy = v2(P[2]), vz = v2(P[3]), m = vecmin([vx, vy, vz]));
  if (vz == m, [1, [P[1] / P[3], P[2] / P[3]]], if (vy == m, [2, [P[1] / P[2], P[3] / P[2]]], [3, [P[2] / P[1], P[3] / P[1]]])); };
{
  my(Pk = [[0, 0, 1], [1, 1, 1], [2, 0, 1], [-1, 0, 1]]);
  for (i = 1, 4, my(cp = chartof(Pk[i]), hits = [j | j <- [1 .. #DISCS], DISCS[j][1] == cp[1] && indisc(DISCS[j], cp[2])]);
    printf("P%d: chart %d, in discs %s\n", i - 1, cp[1], apply(j -> DISCS[j], hits));
    chq(#hits == 1, "known point in exactly one disc"));
  \\ random 2-adic points of C: x rational with small height, y by Newton from all residues mod 8, checked in some disc
  my(nfound = 0, nin = 0);
  for (xn = -30, 30, for (y0 = 0, 7, my(F1 = substvec(FA[1], [x], [xn]), c = y0 + O(2^60), ok = 1, it = 0, d);
    \\ Newton in y with F_y check
    while (valuation(subst(F1, y, c), 2) < 50 && ok, d = subst(deriv(F1, y), y, c); if (d == 0 || (it == 0 && valuation(d, 2) >= valuation(subst(F1, y, c), 2) / 2), ok = 0, c -= subst(F1, y, c) / d; it++; if (it > 100, ok = 0)));
    if (ok && valuation(subst(F1, y, c), 2) >= 50 && valuation(c, 2) >= 0, nfound++;
      my(cp = [xn, truncate(c)], hits = [j | j <- [1 .. #DISCS], DISCS[j][1] == 1 && indisc(DISCS[j], cp)]);
      if (#hits == 1, nin++, printf("  point (%d, %s) in %d discs\n", xn, cp[2], #hits)))));
  printf("independent Newton points in chart z = 1: %d found, %d in exactly one disc\n", nfound, nin);
  chq(nfound == nin, "every sampled point lies in exactly one disc");
  system("rm -f discs_q2.txt"); write("discs_q2.txt", "DISCS = ", DISCS, ";");
}
quit;
