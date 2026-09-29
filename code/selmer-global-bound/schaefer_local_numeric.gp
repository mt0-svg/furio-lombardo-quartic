\\ schaefer_local_numeric.gp: numerical check of the local Schaefer lemma, with every
\\ branch of its case split. Setting: K = Q_p (p-adic numbers of precision PREC), f = (X - theta) g in Z[X] of degree 6
\\ with unit leading coefficient and g(theta) a unit; reduced classes [u, V] of degree 2 from pairs of points of
\\ y^2 = f over Q_p (both rational) or over a quadratic extension Q_p(s), s^2 = n (a conjugate pair; n a nonsquare
\\ unit, unramified, or n = p, ramified), in four regimes for each point (near theta, near another root of f in Z_p,
\\ near infinity, generic). For each class: w = (V^2 - f)/u, c = p^min(0, v(u1), v(u0)), U = u/c, W = c w.
\\ Checked: (L) v(u(theta)/c) even; (A) identity U(theta) W(theta) = V(theta)^2; (B) U(theta) Res_{2,5}(U, g) =
\\ (U2^2 Res_{2,1}(U, V))^2; (S) cont(W) = min(0, 2 cont V); (C) at least one of U(theta), W'(theta), Res_{2,5}(U, g)
\\ is a unit (W' = W / p^cont(W)), and the branch counts.
\\ Run from code/selmer-global-bound: gp -q schaefer_local_numeric.gp > schaefer_local_numeric.out (about a minute).
default(parisizemax, 2*10^9);
PREC = 80;
'X; 's;  \\ variable priority: X above s (polynomials in X over Q_p(s))
NCHK = 0; NFAIL = 0;
chk(c, msg) = { NCHK++; if (!c, NFAIL++; print("FAIL: ", msg)); };
\\ valuation of a p-adic number, a polynomial (content) or a polmod a + b s (min over the coordinates)
vp(x, p) = {
  if (type(x) == "t_POLMOD", x = lift(x); return(min(vp(polcoef(x, 0, 's), p), vp(polcoef(x, 1, 's), p))));
  if (type(x) == "t_POL", return(vecmin(apply(c -> vp(c, p), Vec(x)))));
  if (x == 0, return(oo));
  valuation(x, p);
}
\\ square root in Q_p (t_PADIC) or in Q_p(s): returns 0 when there is none
sqrtp(z, p) = if (issquare(z), sqrt(z), 0);
sqrtE(z, p, n) = {
  my(a, b, N, m, x2, x, y);
  if (type(z) != "t_POLMOD", my(r = sqrtp(z, p)); if (r != 0, return(r));
    if (issquare(z / n), return(sqrt(z / n) * Mod('s, 's^2 - n))); return(0));
  z = lift(z); a = polcoef(z, 0, 's); b = polcoef(z, 1, 's);
  if (b == 0, return(sqrtE(a, p, n)));
  N = a^2 - n * b^2; m = sqrtp(N, p); if (m == 0, return(0));
  foreach([1, -1], sg, x2 = (a + sg * m) / 2;
    if (x2 != 0 && issquare(x2), x = sqrt(x2); y = b / (2 * x); return(Mod(x + y * 's, 's^2 - n))));
  0;
}
\\ the conjugate of a + b s
conjE(x) = if (type(x) == "t_POLMOD", Mod(subst(lift(x), 's, -'s), x.mod), x);
\\ a random point of y^2 = f over Q_p or Q_p(s) in a regime: 1 near theta, 2 near another Z_p root, 3 near infinity,
\\ 4 generic; the x coordinate is x0 + p^a r with r a unit of the field (in Q_p(s) with a nonzero s part)
randpt(f, p, n, th, rts, reg, ext) = {
  my(O = O(p^PREC), x, y, r, a);
  for (tries = 1, 200,
    r = (1 + p * random(p^6) + random(p - 1)) + O;
    if (ext, r = Mod(r + (1 + random(p - 1) + p * random(p^4)) * 's, 's^2 - n));
    a = 1 + random(5);
    x = if (reg == 1, th + p^a * r, reg == 2, if (#rts == 0, next); rts[1 + random(#rts)] + p^a * r,
            reg == 3, r / p^a, r + random(p^3));
    y = if (ext, sqrtE(subst(f, 'X, x), p, n), sqrtp(subst(f, 'X, x) + O, p));
    if (y != 0, return([x, y])));
  0;
}
\\ the class [u, V] of P1 + P2 (P1 != -P2); a conjugate pair when P2 = conj(P1)
classof(f, P1, P2) = {
  my(x1 = P1[1], y1 = P1[2], x2 = P2[1], y2 = P2[2], u, V, sl);
  if (x1 == x2, if (y1 == 0, return(0)); sl = subst(deriv(f, 'X), 'X, x1) / (2 * y1), sl = (y2 - y1) / (x2 - x1));
  u = 'X^2 - (x1 + x2) * 'X + x1 * x2;
  V = sl * ('X - x1) + y1;
  u = apply(c -> if (type(c) == "t_POLMOD", lift(c), c), u); V = apply(c -> if (type(c) == "t_POLMOD", lift(c), c), V);
  \\ coefficients of a Galois stable pair are in Q_p: the s part is 0 up to precision, then dropped
  foreach(concat(Vec(u), Vec(V)), cc, if (type(cc) == "t_POL", my(b = polcoef(cc, 1, 's)); chk(b == 0 || valuation(b, p) >= PREC - 40, "conjugate pair gives a class over Q_p")));
  u = apply(c -> if (type(c) == "t_POL", polcoef(c, 0, 's), c), u); V = apply(c -> if (type(c) == "t_POL", polcoef(c, 0, 's), c), V);
  [u, V];
}
\\ residue reduction of a primitive polynomial over Z_p modulo p, as a polynomial over F_p
redp(P, p) = Pol(apply(c -> Mod(truncate(c), p), Vec(P)), 'X);
\\ one class: all the checks, returns the branch: 1 U(theta) unit, 2 W'(theta) unit, 3 Res unit (first that holds)
docls(f, g, th, p, u, V, ~ST) = {
  my(w, rem, c, U, W, s, t, Wp, Uth, Wth, R, lhsB, rhsB, br, vc, vU);
  rem = (V^2 - f) % u; chk(vp(rem, p) >= PREC - 30, "u divides V^2 - f (to precision)");
  w = (V^2 - f) \ u;
  vc = min(0, min(vp(polcoef(u, 1, 'X), p), vp(polcoef(u, 0, 'X), p)));
  c = p^vc; U = u / c; W = c * w;
  chk(vp(U, p) == 0, "U primitive");
  Uth = subst(U, 'X, th);
  if (Uth == 0 || vp(Uth, p) > PREC - 40, ST[5]++; return(0));
  \\ (L) the lemma
  vU = vp(Uth, p);
  if (NEG, if (vU % 2, ST[6]++); return(0));
  chk(vU % 2 == 0, Str("(L) v(U(theta)) even, got ", vU, " at p = ", p));
  \\ (S) content of W
  s = if (V == 0, oo, vp(V, p)); t = vp(W, p);
  chk(t == if (s == oo || s >= 0, 0, 2 * s), Str("(S) cont W = min(0, 2 cont V): ", [s, t]));
  Wp = W / p^t;
  \\ (A)
  Wth = subst(W, 'X, th);
  chk(vp(Uth * Wth - subst(V, 'X, th)^2, p) >= PREC - 40, "(A) U(theta) W(theta) = V(theta)^2");
  \\ (B)
  R = polresultant(U, g, 'X);
  lhsB = Uth * R; rhsB = (pollead(U)^2 * polresultant(U, V, 'X))^2;
  if (poldegree(V, 'X) < 1, rhsB = (pollead(U)^2 * pollead(U)^(1 - poldegree(V, 'X)) * polresultant(U, V, 'X))^2);
  chk(vp(lhsB - rhsB, p) >= vp(lhsB, p) + PREC / 2 - 30, "(B) U(theta) Res(U, g) = (U2^2 Res(U, V))^2");
  \\ (C) branches
  br = if (vp(Uth, p) == 0, 1, vp(subst(Wp, 'X, th), p) == 0, 2, vp(R, p) == 0, 3, 0);
  chk(br > 0, Str("(C) one of U(theta), W'(theta), Res(U, g) is a unit: ", [vp(Uth, p), vp(subst(Wp, 'X, th), p), vp(R, p), s]));
  if (br, ST[br]++);
  \\ the sub-branch of the proof's case (3c): U-bar linear with root theta-bar
  if (br == 3 && poldegree(redp(U, p)) == 1, ST[4]++);
  br;
}

runall() = {
  my(tot = vector(6));
  foreach([3, 5, 7, 11, 2], p,
    my(ST = vector(6), ncls = 0);
    for (trial = 1, 60,
      my(th, g, f, rts, n);
      th = random(p^3);
      g = sum(i = 0, 4, (random(2 * p^2) - p^2) * 'X^i) + (1 + random(p - 1) + p * random(p)) * 'X^5;
      if (NEG, g = ('X - th) * (sum(i = 0, 3, (random(2 * p^2) - p^2) * 'X^i) + (1 + random(p - 1)) * 'X^4) + p * sum(i = 0, 4, random(p^2) * 'X^i));
      if (!NEG && subst(g, 'X, th) % p == 0, next);
      f = ('X - th) * g;
      rts = [r | r <- polrootspadic(f, p, PREC), valuation(r - th, p) == 0 && valuation(r, p) >= 0];
      \\ n: an unramified nonsquare unit; the ramified extension uses p
      n = 0; for (a = 2, 50, if (!issquare(Mod(a, p)) && a % p, n = a; break)); if (p == 2, n = 5);
      foreach([n, p], nn,
        for (k = 1, 6,
          my(r1 = 1 + random(4), r2 = 1 + random(4), P1, P2, cl, ext = random(2));
          if (ext,
            P1 = randpt(f, p, nn, th, rts, r1, 1); if (P1 == 0, next); P2 = [conjE(P1[1]), conjE(P1[2])],
            P1 = randpt(f, p, nn, th, rts, r1, 0); P2 = randpt(f, p, nn, th, rts, r2, 0); if (P1 == 0 || P2 == 0, next);
            if (random(4) == 0, P2 = P1));
          cl = classof(f, P1, P2); if (cl == 0, next);
          if (vp(subst(cl[1], 'X, th), p) > PREC - 40, next);
          ncls++; docls(f, g, th, p, cl[1], cl[2], ~ST))));
    printf("p = %d: %d classes; branch U(theta) unit %d, W'(theta) unit %d, Res unit %d (of which U-bar linear at theta-bar %d), skipped %d\n",
           p, ncls, ST[1], ST[2], ST[3], ST[4], ST[5]);
    tot += ST);
  tot;
}
NEG = 0; print("main test: f'(theta) a unit"); T0 = runall();
printf("checks %d, failures %d\n", NCHK, NFAIL);
print("negative control: f-bar with a double root at theta-bar (hypothesis dropped); odd v(U(theta)) expected sometimes");
NEG = 1; T1 = runall();
printf("negative control: %d classes with v(U(theta)) odd\n", T1[6]);
printf("RESULT %s\n", if (NFAIL == 0 && T0[2] > 0 && T0[3] > 0 && T0[4] > 0 && T1[6] > 0, "PASS", "FAIL"));
quit;
