\\ Step 5 of the 2-descent: images of known rational divisor classes, principal divisors, consistency.
\\ Run from code/jacobian-over-q:
\\   gp -q -D parisizemax=4000000000 two_descent_lib.gp two_descent_local_images.gp fake_selmer_group.gp known_classes_images.gp
chk(b, s) = if (!b, error("CHECK FAILED: ", s), print("ok  ", s));

\\ intersection divisor Phi.C (Phi a form over Q) as a list of [multiplicity, orbit]; every point must have z != 0
\\ and each fibre of the projection from [0:1:0] must contain one point of Phi.C only.
sect(Phi) = {
  my(R = polresultant(F, Phi, y), R1, fa, out = List());
  if (poldegree(R, x) != 4 * poldegree(substvec(Phi, [x,y,z], [x*u, y*u, z*u]), u), error("intersection point on z = 0"));
  R1 = subst(R, z, 1);
  fa = factor(R1);
  for (i = 1, #fa~, my(m = subst(fa[i, 1], x, u), g, Yu);
    if (poldegree(m, u) == 0, next);
    m = m / pollead(m);
    g = gcd(substvec(f1, [x], [Mod(u, m)]), substvec(subst(Phi, z, 1), [x], [Mod(u, m)]));
    if (poldegree(g, y) != 1, error("fibre with several intersection points"));
    Yu = lift(-polcoef(g, 0, y) / polcoef(g, 1, y));
    listput(out, [fa[i, 2], [m, [u, Yu, 1]]]));
  Vec(out);
}
\\ remove an orbit (given by its x-polynomial in u) from a section
dropx(S, m) = { my(out = List(), found = 0);
  for (i = 1, #S, if (S[i][2][1] == m, found = 1; if (S[i][1] > 1, listput(out, [S[i][1] - 1, S[i][2]])), listput(out, S[i])));
  if (!found, error("orbit not found")); Vec(out); }
scale(S, n) = apply(t -> [n * t[1], t[2]], S);
\\ class of delta(D) in V = A(S,2) (vector in F_2^8), and a check that it lies in the Selmer kernel
dcls(D) = globcls(delta(D))[1];
inspan(v, B) = f2rank(matconcat([B, v~])) == f2rank(B);
RAT = Mat(apply(v -> v~, ratv));

print("== auxiliary divisors");
\\ A0 = l0.C - P0 for the line l0 : y = 3x through P0
S0 = sect(y - 3*x);
A0 = dropx(S0, u);
chk(vecsum(apply(t -> t[1] * orbdeg(t[2]), A0)) == 3, "A0 = (y = 3x).C - P0 is effective of degree 3");
Hs = sect(y - x - 2*z);
chk(vecsum(apply(t -> t[1] * orbdeg(t[2]), Hs)) == 4, "H' = (y = x + 2z).C, a line section");
\\ a conic through the three points of R, and its residual R'
{
  my(cm = [x^2, x*y, x*z, y^2, y*z, z^2], rows, K, qq);
  rows = matrix(3, 6, i, j, polcoef(substvec(cm[j], [x, y, z], orbR[2]) % orbR[1], i - 1, u));
  K = matker(rows);
  chk(#K == 3, "the conics through R form a 3-dimensional space");
  qq = sum(j = 1, 6, (K[j, 1] + 2*K[j, 2] - K[j, 3]) * cm[j]); qq = qq / content(qq);
  Qconic = qq;
}
print("   conic through R: ", Qconic);
SQ = sect(Qconic);
Rp = dropx(SQ, orbR[1]);
chk(vecsum(apply(t -> t[1] * orbdeg(t[2]), Rp)) == 5, "R' = q.C - R is effective of degree 5");
for (i = 1, #A0, chk(onC(A0[i][2]), "orbit of A0 on C"));
for (i = 1, #Rp, chk(onC(Rp[i][2]), "orbit of R' on C"));

print("== principal divisors map to 0");
{
  my(h2 = sect(x + y - 2*z), c2 = sect(x^2 + x*y - 3*y^2 + 2*x*z - z^2 + 5*y*z), v);
  v = dcls(concat(h2, scale(Hs, -1)));
  chk(inspan(v, RAT), "delta((x + y = 2z).C - H') = 0 in A^x/A^x2 Q^x");
  v = dcls(concat(c2, scale(Hs, -2)));
  chk(inspan(v, RAT), "delta(conic.C - 2H') = 0");
}

print("== known classes, with P0 replaced by H' - A0");
Qb = [u^2 - u + 2, [u, 1, 0]];
chk(onC(Qb), "Qb : x^2 - xy + 2y^2 = z = 0 lies on C");
Pt = [[1,1,1], [2,0,1], [-1,0,1]];
for (i = 1, 3, chk(substvec(F, [x,y,z], Pt[i]) == 0, Str("P", i, " on C")));
\\ D_i = P_i - P0 ~ P_i + A0 - H'
Dcl = vector(3, i, dcls(concat(concat([[1, ptorb(Pt[i])]], A0), scale(Hs, -1))));
\\ Qb - 2P0 ~ Qb + 2A0 - 2H'
Qcl = dcls(concat(concat([[1, Qb]], scale(A0, 2)), scale(Hs, -2)));
\\ gen3 = R - 3P0 ~ (2H - R') - 3(H - A0) ~ 3A0 - R' - H'
Gcl = dcls(concat(concat(scale(A0, 3), scale(Rp, -1)), scale(Hs, -1)));
print("   delta(D1) = ", Dcl[1], "  delta(D2) = ", Dcl[2], "  delta(D3) = ", Dcl[3]);
print("   delta(Qb - 2P0) = ", Qcl, "  delta(gen3) = ", Gcl, "   (in A(S,2), modulo <-1,2,7>)");
iszero(v) = inspan(v, RAT);
chk(iszero(Gcl), "delta(gen3) = 0: gen3 = [R - 3P0] spans the kernel (PSS Prop. mapker)");
chk(iszero(Dcl[2]), "delta(D2) = 0 (D2 = 2 B2 lies in 2J(Q))");
chk(iszero((Dcl[1] + Dcl[3]) % 2), "delta(D1) = delta(D3) (D1 - D3 = 2 B3)");
chk(!iszero(Dcl[1]) && !iszero(Qcl) && !iszero((Dcl[1] + Qcl) % 2), "delta(D1), delta(Qb - 2P0) and their sum are nonzero");
{
  my(B = matconcat([RAT, Dcl[1]~, Qcl~]));
  chk(f2rank(B) - 3 == 2, "delta(D1) and delta(Qb - 2P0) span a 2-dimensional subspace");
  chk(f2rank(matconcat([SelK, B])) == f2rank(SelK), "these images lie in the fake Selmer kernel computed in step 4 (consistency)");
  chk(f2rank(B) == f2rank(SelK) && #SelK == 5, "so they span Sel_fake, which has dimension 2");
}
\\ images of B1, B2, B3: B1 = D1, B2 = gen3 - D2 - 3 D3, B3 = [Qb - 2P0] - D1 + D3
{
  my(b1 = Dcl[1], b2 = (Gcl + Dcl[2] + 3 * Dcl[3]) % 2, b3 = (Qcl + Dcl[1] + Dcl[3]) % 2);
  chk(f2rank(matconcat([RAT, b1~, b2~, b3~])) - 3 == 2, "delta(B1), delta(B2), delta(B3) span dimension 2");
  chk(iszero((b1 + b2) % 2), "delta(B1) = delta(B2), consistent with gen3 = 3B1 + 3B2 - 6B3 and delta(gen3) = 0");
}
print("== local sanity for the global images");
{
  \\ delta(D1) and delta(Qb - 2P0) as elements: their classes at 2 lie in Im2, at 7 in Im7, at infinity in Iminf
  my(e1 = delta(concat(concat([[1, ptorb(Pt[1])]], A0), scale(Hs, -1))),
     e4 = delta(concat(concat([[1, Qb]], scale(A0, 2)), scale(Hs, -2))));
  foreach ([e1, e4], e,
    chk(f2rank(matconcat([Im2, cl2(e)~])) == f2rank(Im2), "class at 2 lies in Im(delta_2) + Q_2^x");
    chk(f2rank(matconcat([Im7, cl7(e)~])) == f2rank(Im7), "class at 7 lies in Q_7^x");
    chk(f2rank(matconcat([Iminf, clinf(e)~])) == f2rank(Iminf), "class at infinity lies in R^x");
    chk(issquare(nfeltnorm(bnf, e)), "norm is a square in Q"));
}
print("== conclusion");
{
  my(dSel = f2rank(SelK) - 3, dIm = f2rank(matconcat([RAT, Dcl[1]~, Qcl~])) - 3);
  chk(P7a.e * P7a.f == 1 && P7b.e * P7b.f == 7, "Q_7: orbits of sizes 1 and 7, so J(Q_7)[2] = 0 (step 3) and J(Q)[2] = 0");
  chk(P2.e * P2.f == 8, "Q_2: one orbit of size 8, so gen3 is not in 2J(Q_2) (step 3), hence not in 2J(Q)");
  chk(iszero(Gcl), "delta(gen3) = 0, and the kernel of delta on J(Q)/2J(Q) is <gen3> (PSS Prop. mapker)");
  chk(dSel == 2 && dIm == dSel, "delta(D1) and delta(Qb - 2P0) span Sel_fake, of dimension 2 (step 4, with bnfcertify)");
  print("   dim J(Q)/2J(Q) = dim <gen3> + dim delta(J(Q)) = 1 + ", dIm, ", and dim delta(J(Q)) <= dim Sel_fake = ", dSel);
  print("   basis of J(Q)/2J(Q): gen3 = [R - 3P0], D1 = [P1 - P0], [Qb - 2P0] (the images of D1 and Qb - 2P0 are");
  print("   independent, and gen3 is a nonzero class of the kernel)");
  print("rank J(Q) = dim J(Q)/2J(Q) = ", 1 + dIm);
}
print("step 5 done");
