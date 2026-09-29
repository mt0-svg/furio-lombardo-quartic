\\ Step 1 of the 2-descent: flexes, triangles, the algebra A3, the cubic G_A and its divisor,
\\ the cubic Psi with div = 2E, the norm identity.  Every check is an exact computation; any failure stops the script.
\\ Run from code/jacobian-over-q:  gp -q -D parisizemax=4000000000 two_descent_lib.gp two_descent_algebra.gp
chk(b, s) = if (!b, error("CHECK FAILED: ", s), print("ok  ", s));

print("== the curve and its flexes");
chk(substvec(F, [x,y,z], [0,1,0]) != 0, "[0:1:0] is not on C (projection from it is defined on C)");
chk(poldegree(rflex, x) == 24 && polisirreducible(rflex), "Res_y(F, Hess)(x, 1) has degree 24 and is irreducible over Q");
chk(polresultant(substvec(F, [x,z], [1,0]), substvec(Hess, [x,z], [1,0]), y) != 0, "no flex on the line z = 0 (F(1,y,0) has degree 4 in y and [0:1:0] is not on C)");
print("   so the 24 flexes are distinct, simple zeros of Hess on C (Hess.C = sum of the 24 flexes), with distinct x/z");

print("== the algebra A3");
chk(nfdisc(A3) == -2^8 * 7^9, "disc(O_A3) = -2^8 7^9, so A3 is unramified outside 2, 7");
chk(bnf.sign == [2, 3], "signature (2, 3)");
chk(#nfsubfields(A3) == 2, "A3 has no subfield other than Q and A3");
{
  my(S = nfsplitting(A3), t7 = 0, t8 = 0);
  chk(poldegree(S) == 336, "the Galois closure of A3 has degree 336 (nfsplitting)");
  forprime (p = 3, 200, if (p == 7 || poldisc(A3) % p == 0, next);
    my(d = vecsort(apply(poldegree, factormod(A3, p)[, 1]~)));
    if (d == [1, 7], t7 = p); if (d == [8], t8 = p));
  chk(t7 && t8, Str("Frobenius cycle types 7+1 (p = ", t7, ") and 8 (p = ", t8, ") occur"));
  print("   hence Gal = the transitive group of degree 8 and order 336, 8T43 = PGL(2,7) (GAP: two_descent_galois_module.g)");
}
{
  my(phi = polmodular(7), f = substvec(phi, [x, y], [a, 12544]));
  chk(nfisisom(A3, f) != 0, "A3 = Q[X]/Phi_7(X, 12544) (the 7-isogeny field of E3, j(E3) = 12544)");
}

print("== the triangle over A3");
chk(poldegree(cT, X) == 3, "Res_y(F, Hess)(x,1) has a cubic factor cT over A3");
{
  my(N = polresultant(A3, lift(subst(cT, X, x)), a));
  chk(N == rflex / pollead(rflex), "Norm_{A3/Q}(cT) = Res_y(F,Hess)(x,1)/lc: the 8 conjugate triples partition the 24 flexes");
}
chk(poldegree(YT, X) == 2, "y = YT(x) has degree exactly 2 on the triple: its three flexes are not collinear");
{
  \\ triangle property: the tangent line at T1 = (X, YT) meets C in 3 T1 + T1' with T1' in the same triple
  my(fx = subst(subst(deriv(f1, x), x, X), y, YT) % cT, fy = subst(subst(deriv(f1, y), x, X), y, YT) % cT,
     q, r4, xn, yn);
  \\ parametrize the tangent line by the variable y: (X + y*fy, YT - y*fx)
  q = substvec(f1, [x, y], [X + y*fy, YT - y*fx]);
  q = Pol(apply(c -> c % cT, Vec(q)), y);
  chk(polcoef(q, 0, y) == 0 && polcoef(q, 1, y) == 0 && polcoef(q, 2, y) == 0, "the flex T1 has contact order >= 3 with its tangent");
  r4 = -(polcoef(q, 3, y) * Mod(1, cT)) / (polcoef(q, 4, y) * Mod(1, cT));   \\ the fourth intersection point
  xn = lift(Mod(X, cT) + r4 * Mod(fy, cT)); yn = lift(Mod(YT, cT) - r4 * Mod(fx, cT));
  chk(subst(cT, X, Mod(xn, cT)) == 0, "the fourth point of the tangent at T1 is a flex of the same triple (triangle)");
  chk(Mod(subst(YT, X, xn), cT) == Mod(yn, cT), "   and its y-coordinate is YT(x) of that flex");
  chk(xn != X, "   and it is not T1 itself");
}
print("   hence 4T ~ 3H for every triangle T (the product of the three tangent lines meets C in 4T)");

print("== the cubic G_A");
chk(GAkerdim == 1, "the cubics over A3 with order >= 3 at P0 and contact >= 2 at the three flexes of T form a line");
print("GA = ", GA);
{
  my(R = polresultant(F, GA, y), R1, q, e0 = 0, ec = 0, cx = subst(cT, X, x), r3);
  chk(poldegree(R, x) == 12, "Res_y(F, GA) is a binary form of degree 12 with nonzero x^12 coefficient: no point of C.G on z = 0");
  q = subst(R, z, 1);
  while (polcoef(q, 0, x) == 0, q = q / x; e0++);
  while (q % cx == 0, q = q \ cx; ec++);
  chk(e0 == 3, "exponent of x in Res_y(F, GA) is 3: I_P0(C, G) = 3 and no other point of C on x = 0 lies on G");
  chk(ec == 2, "exponent of cT is 2: I_T(C, G) = 2 at each flex of T, no other point above those x lies on G");
  q = q / pollead(q);
  r3 = simplify(lift(q));
  chk(type(r3) == "t_POL" && variables(r3) == [x] && poldegree(r3) == 3, "the residual factor is a cubic with rational coefficients");
  r3 = r3 * denominator(content(r3)); r3 = r3 / content(r3);
  print("   r3 = ", r3);
  chk(polisirreducible(r3), "r3 is irreducible over Q");
  chk(poldegree(gcd(r3, x * polresultant(A3, lift(cx), a))) == 0, "r3 is prime to x and to the flex polynomial");
}
{
  \\ R: the y-coordinate of the point of C.G above a root of r3 lies in Q(root)
  my(R = polresultant(F, GA, y), q = subst(R, z, 1), cx = subst(cT, X, x), r3, g, yR, ok = 0);
  while (polcoef(q, 0, x) == 0, q = q / x); while (q % cx == 0, q = q \ cx);
  r3 = simplify(lift(q / pollead(q))); r3 = r3 * denominator(content(r3)); r3 = r3 / content(r3);
  rR = subst(r3, x, u) / pollead(r3);
  \\ gcd over the cubic field Q(u) of F(u, y, 1) and the norm to Q(u) of GA(u, y, 1)
  g = gcd(substvec(f1, [x], [Mod(u, rR)]), polresultant(A3, lift(substvec(subst(GA, z, 1), [x], [Mod(u, rR)])), a));
  chk(poldegree(g, y) == 1, "above each root of r3 exactly one point of C lies on all conjugates of G");
  yR = lift(-polcoef(g, 0, y) / polcoef(g, 1, y));
  orbR = [rR, [u, yR, 1]];
  chk(onC(orbR), "R = (u, yR(u), 1), r3(u) = 0, lies on C");
  chk(evalorb(GA, orbR) == 0 && (substvec(subst(GA, z, 1), [x, y], [Mod(u, rR), Mod(yR, rR)]) == 0), "GA vanishes at R over A3 (x) Q(u): R is a Q-rational divisor, the same for all conjugates of G");
  print("   R: x = u, y = ", yR, ", z = 1, with ", rR, " = 0");
  \\ non-collinearity of the three points of R: det = (Vandermonde) * (coefficient of u^2 in yR)
  chk(poldegree(yR, u) == 2, "the three points of R are not collinear");
}
print("   => div(G_omega) = 2 T_omega + E for every omega in Omega, with E = 3 P0 + R a Q-rational divisor");

print("== the cubic Psi with div(Psi) = 2E = 6 P0 + 2R");
{
  my(rows = List(), xs = xP0ser(8), K, psi, R, q, e0 = 0, e3 = 0, r3 = subst(rR, u, x), V0, V1, fxR, fyR, yR = orbR[2][2]);
  for (k = 0, 5, listput(rows, vector(10, i, polcoef(subst(subst(mons3[i], z, 1), x, xs), k, y))));
  fxR = substvec(deriv(f1, x), [x, y], [u, yR]) % rR; fyR = substvec(deriv(f1, y), [x, y], [u, yR]) % rR;
  V0 = vector(10, i, substvec(subst(mons3[i], z, 1), [x, y], [u, yR]) % rR);
  V1 = vector(10, i, my(m = subst(mons3[i], z, 1));
       (fxR * substvec(deriv(m, y), [x, y], [u, yR]) - fyR * substvec(deriv(m, x), [x, y], [u, yR])) % rR);
  for (k = 0, 2, listput(rows, vector(10, i, polcoef(V0[i], k, u))));
  for (k = 0, 2, listput(rows, vector(10, i, polcoef(V1[i], k, u))));
  K = matker(matrix(#rows, 10, i, j, rows[i][j]));
  chk(#K == 1, "the cubics over Q with order >= 6 at P0 and contact >= 2 at R form a line");
  psi = sum(i = 1, 10, K[i, 1] * mons3[i]); psi = psi / content(psi);
  Psi = psi;
  print("   Psi = ", Psi);
  R = polresultant(F, Psi, y);
  chk(poldegree(R, x) == 12, "no point of C.Psi on z = 0");
  q = subst(R, z, 1);
  while (polcoef(q, 0, x) == 0, q = q / x; e0++);
  while (q % r3 == 0, q = q \ r3; e3++);
  chk(e0 == 6 && e3 == 2 && poldegree(q) == 0, "Res_y(F, Psi) = const * x^6 * r3^2: div(Psi) = 6 P0 + 2R exactly");
}
print("   => 2E ~ 3H; with 2T + E ~ 3H this gives 4T ~ 3H again, and sum_omega T_omega = Hess.C ~ 6H ~ 8 T_omega0");

print("== norm identity N_{A3/Q}(G_A) = c * Hess^2 * Psi^4 modulo F");
{
  my(N = polresultant(A3, lift(GA), a), P = [1, 1, 1], cst, D);
  chk(substvec(F, [x,y,z], P) == 0, "P1 = (1,1,1) is on C");
  cst = substvec(N, [x,y,z], P) / (substvec(Hess, [x,y,z], P)^2 * substvec(Psi, [x,y,z], P)^4);
  D = N - cst * Hess^2 * Psi^4;
  chk(D % F == 0, Str("N(GA) - c Hess^2 Psi^4 is divisible by F, c = ", factor(cst)));
  normconst = cst;
}
print("   => for every degree 0 divisor D disjoint from the supports, N(delta(D)) = Hess(D)^2 Psi(D)^4 is a square");

print("== P0 and the Hessian: supports");
chk(substvec(Hess, [x,y,z], [0,0,1]) != 0, "P0 is not a flex");
print("step 1 done");
