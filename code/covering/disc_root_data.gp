\\ disc_root_data.gp: the data of the root uniqueness lemmas of M4Box (lean/FurioLombardo/Discharge/M4Box/DiscRoot.lean).
\\ For each disc d of M4 (discPt of lean/FurioLombardo/Discharge/M4Cert/Curve.lean), G(X, Y) = F(discPt d X Y) with F
\\ the quartic of lean/Statement.lean, 2^m the 2-part of the content of G, G1 = G / 2^m, and
\\ H(X, Y, Y') = (G1(X, Y) - G1(X, Y')) / (Y - Y') (an integer polynomial), printed in Lean syntax (x, y, y2 for X, Y, Y');
\\ also the values of H mod 2 at the 8 residues (all odd: then G(X, .) has exactly one root in Z_2 for every X) and the
\\ coefficients of G1 in y (for Hensel's lemma). Same certificate as part 2 of code/covering/log_branch.gp.
\\ Run: gp -q disc_root_data.gp > disc_root_data.out
Fq = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
discPtL(d, X, Y) = {if (d == 1, [2 * X, 2 * Y, 1], d == 2, [1 + 2 * X, 2 * Y, 1], d == 3, [1 + 2 * X, 1 + 2 * Y, 1],
  d == 4, [2 * X, 1, 2 * Y], d == 5, [1 + 2 * X, 1, 2 * Y], error("disc"));}
lean(P) = { my(s = Str(P)); s = strjoin(strsplit(s, "XX"), "x"); s = strjoin(strsplit(s, "YP"), "y2"); strjoin(strsplit(s, "YY"), "y"); }
{
for (d = 1, 5,
  my(G = substvec(Fq, [x, y, z], discPtL(d, 'XX, 'YY)), m = valuation(content(G), 2), G1 = G / 2^m, H, res = []);
  H = (G1 - substvec(G1, ['YY], ['YP])) / ('YY - 'YP);
  if (type(H) != "t_POL" || denominator(content(H)) != 1, error("H is not an integer polynomial"));
  for (a = 0, 1, for (b = 0, 1, for (c = 0, 1, res = concat(res, substvec(H, ['XX, 'YY, 'YP], [a, b, c]) % 2))));
  if (vecmin(res) != 1, error("H not odd"));
  printf("disc %d: m = %d; H mod 2 at the residues (X, Y, Y') in {0,1}^3: %s\n", d, m, res);
  printf("  G1 = %s\n", lean(G1));
  printf("  H = %s\n", lean(H));
  printf("  G1 in y: %s\n", vector(poldegree(G1, 'YY) + 1, i, lean(polcoef(G1, i - 1, 'YY))));
);
}
quit;
