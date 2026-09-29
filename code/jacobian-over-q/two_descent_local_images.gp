\\ Step 3 of the 2-descent: local images of delta at 2, 7 and infinity.
\\ Run from code/jacobian-over-q:  gp -q -D parisizemax=4000000000 two_descent_lib.gp two_descent_local_images.gp
chk(b, s) = if (!b, error("CHECK FAILED: ", s), print("ok  ", s));
f2v(v) = Mod(v, 2);

print("== orbit structure of Omega (embeddings of A3) over Q_2, Q_7, R");
chk(P2.e * P2.f == 8, "Q_2: one orbit of size 8 (2 = P^4, f = 2)");
chk(P7a.e * P7a.f == 1 && P7b.e * P7b.f == 7, "Q_7: orbits of sizes 1 and 7");
chk(bnf.sign == [2, 3], "R: complex conjugation has 2 fixed points and 3 transpositions on Omega");

print("== local square classes at 2");
cl2m1 = cl2(-1); cl2two = cl2(2); cl2five = cl2(5);
chk(cl2five == vector(10, i, 0), "5 is a square in L = A3 (x) Q_2 (L contains the unramified quadratic extension)");
{
  my(Q2 = [-1, 2, 5], ker = 0);
  forvec (e = vector(3, i, [0, 1]), my(d = prod(i = 1, 3, Q2[i]^e[i])); if (cl2(d) == vector(10, i, 0), ker++));
  chk(ker == 2, "ker(Q_2^x/Q_2^x2 -> L^x/L^x2) = {1, 5}: dimension 1");
  chk(f2rank(Mat([cl2m1~, cl2two~])) == 2, "the image of Q_2^x in L^x/L^x2 has dimension 2 (spanned by -1, 2)");
}
print("   Q_2: W^G = Diag (one orbit), so (W/Diag)^G = ker(Q_2^x/Q_2^x2 -> L^x/L^x2) has dimension 1;");
print("   its nonzero element has weight 4 (even), so J(Q_2)[2] = (W0/Diag)^G has dimension 1,");
print("   dim J(Q_2)/2J(Q_2) = 1 + 3 = 4; no orbit of odd size, so [R - 3P0] is not in 2J(Q_2):");
print("   the local kernel of delta_2 has dimension 1 and dim Im(delta_2) = 3.");

print("== sampling C(Q_2)");
\\ the rational base point P1 = (1,1,1) is outside the support of div(G_A)
bP = [1, 1, 1];
chk(substvec(F, [x,y,z], bP) == 0 && substvec(GA, [x,y,z], bP) != 0, "P1 = (1,1,1) lies on C and G_A(P1) != 0");
cb2 = cl2(substvec(GA, [x,y,z], bP));
\\ class of G_A at a Q_2-point given by x0 in Q and a 2-adic root yP of F(x0, y, 1)
\\ returns [class vector, valuation, precision] or 0 if the precision is insufficient
cl2pt(x0, yP) = {
  my(k, v, pr, V, b, val);
  k = max(0, max(-valuation(x0, 2), -valuation(yP, 2)));
  V = [x0 * 2^k, truncate(yP * 2^k), 2^k];
  pr = padicprec(yP * 2^k, 2);
  if (denominator(V[1]) != 1 || denominator(V[2]) != 1, error("non integral"));
  b = substvec(GA, [x,y,z], V);
  if (b == 0, return(0));
  val = nfeltval(bnf, b, P2);
  if (val > 4 * pr - 9, return(0));      \\ class of G_A(P) = class of G_A(Ptilde) needs val + 9 <= 4 * pr
  [cl2(b), val, pr];
}
{
  my(basis = Mat([cl2m1~, cl2two~]), cnt = 0, used = 0, got = 0, maxval = 0, xs = List(), pts = List());
  for (m = -40, 40, listput(xs, m));
  for (m = -31, 31, if (m % 2, listput(xs, m/2); listput(xs, m/4); listput(xs, m/8)));
  for (i = 1, #xs,
    my(x0 = xs[i], rts = polrootspadic(subst(subst(F, z, 1), x, x0), 2, 60));
    for (j = 1, #rts,
      my(c = cl2pt(x0, rts[j]));
      cnt++;
      if (c == 0, next);
      used++; maxval = max(maxval, c[2]);
      my(dv = (c[1] - cb2) % 2, nb = matconcat([basis, dv~]));
      if (f2rank(nb) > f2rank(basis), basis = nb; listput(pts, [x0, rts[j]]);
        print("   new direction from the Q_2-point with x0 = ", x0, ", v_2(y) = ", valuation(rts[j], 2), ": dim now ", f2rank(basis) - 2))));
  print("   Q_2-points tried: ", cnt, ", with enough precision: ", used, ", largest v_P(G_A(P)) met: ", maxval);
  Im2 = basis;
  chk(f2rank(Im2) - 2 == 3, "the differences of Q_2-points span a 3-dimensional subspace of L^x/L^x2 Q_2^x");
  Im2pts = Vec(pts);
  print("   = Im(delta_2), since dim Im(delta_2) = 3; generators found at: ", Im2pts);
}

print("== Q_7");
print("   orbits of sizes 1 and 7: (W/Diag)^G = {0, class of the fixed point}, which has odd weight,");
print("   so J(Q_7)[2] = 0 and J(Q_7)/2J(Q_7) = 0: Im(delta_7) = 0.");
cl7seven = cl7(7); cl7three = cl7(3);
chk(f2rank(Mat([cl7seven~, cl7three~])) == 2, "the image of Q_7^x in (A3 (x) Q_7)^x / squares has dimension 2 (spanned by 7, 3)");
Im7 = Mat([cl7seven~, cl7three~]);
{
  \\ sanity check: sampled differences of Q_7-points land in the image of Q_7^x
  my(cb7 = cl7(substvec(GA, [x,y,z], bP)), cnt = 0, bad = 0);
  for (x0 = -30, 30,
    my(rts = polrootspadic(subst(subst(F, z, 1), x, x0), 7, 30));
    for (j = 1, #rts,
      my(k = max(0, -valuation(rts[j], 7)), V = [x0 * 7^k, truncate(rts[j] * 7^k), 7^k], pr = padicprec(rts[j] * 7^k, 7), b, va, vb);
      b = substvec(GA, [x,y,z], V);
      if (b == 0, next);
      va = nfeltval(bnf, b, P7a); vb = nfeltval(bnf, b, P7b);
      if (va + 1 > pr || vb + 1 > 7 * pr, next);
      cnt++;
      if (f2rank(matconcat([Im7, ((cl7(b) - cb7) % 2)~])) > 2, bad++)));
  chk(cnt > 50 && bad == 0, Str("sanity: ", cnt, " Q_7-points, every difference is trivial in (A3 (x) Q_7)^x / squares Q_7^x"));
}

print("== R");
print("   complex conjugation has fixed points on Omega: (W/Diag)^c = W^c/Diag of dimension 4, weight map onto mu_2,");
print("   so J(R)[2] has dimension 3 = g, J(R) is connected and J(R)/2J(R) = 0: Im(delta_inf) = 0.");
Iminf = Mat([clinf(-1)~]);
chk(clinf(-1) == [1, 1], "the image of R^x is the diagonal of (R^x/R^x2)^2");
{
  \\ sanity check: real points; the sign pattern of G_A must be constant up to the diagonal
  my(cnt = 0, bad = 0, rr = bnf.roots, sgn, par0);
  par0 = sum(k = 1, 2, subst(substvec(lift(GA), [x, y, z], bP), a, rr[k]) < 0) % 2;
  for (i = -200, 200, my(x0 = i / 20, rts = polroots(subst(subst(F, z, 1), x, x0)));
    for (j = 1, #rts, if (abs(imag(rts[j])) > 1e-20, next);
      my(y0 = real(rts[j]), vals = vector(2, k, subst(substvec(lift(GA), [x, y, z], [x0, y0, 1]), a, rr[k])));
      if (vecmin(abs(vals)) < 1e-10, next);
      cnt++;
      sgn = vector(2, k, vals[k] < 0);
      if ((sgn[1] + sgn[2]) % 2 != par0, bad++)));
  chk(cnt > 100 && bad == 0, Str("sanity (floating point): ", cnt, " real points, the parity of the signs of G_A at the two real places is the same as at P1"));
}
print("step 3 done");
