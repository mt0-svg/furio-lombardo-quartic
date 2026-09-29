\\ schaefer_identities.gp: the two identities of the Schaefer lemma and its parity
\\ conclusion on reduced classes of Jac(fRev k)(K21), k = 0, 1, built by Cantor addition from the known points
\\ phi(x_a), phi(x_b) and T (the Cantor routine and the point setup are copied from an earlier script, not shipped).
\\ For each class [u, V] with u coprime to f = fRev k, w = (V^2 - f)/u:
\\ (R) Res(u, f) = Res(u, V)^2 exactly in K21 (u monic; this is identity B with c = 1 through multiplicativity);
\\ (B) in F = K21[t]/(g_i) for g_i = q, h (theta = t mod g_i, gg = f/(X - theta) over F):
\\     u(theta) Res_{2,5}(u, gg) = Res(u, V)^2 exactly;
\\ (A) u(theta) w(theta) = V(theta)^2 exactly in F;
\\ (P) parity: for every prime P of the absolute field F_q (degree 42) above a prime p not dividing 14 that divides
\\     the norm of u(theta) or a denominator of u (all such p below PBOUND): the hypotheses of the lemma at P (f
\\     P-integral, leading coefficient and f'(theta) P-units) and v_P(u(theta)) - min(0, v_P(u1), v_P(u0)) even.
\\ Run from code/selmer-global-bound: gp -q schaefer_identities.gp > schaefer_identities.out
default(parisizemax, 5*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
read("../earlier-computations/phi_known_lifts.gp");
PBOUND = 3000;
NCHK = 0; NFAIL = 0;
chk(c, msg) = { NCHK++; if (!c, NFAIL++; print("FAIL: ", msg)); };
o = Mod(1, K21);
red(g) = lift(o * g);
modp(g, m) = red(lift(Mod(o * g, o * m)));
invp(g, m) = red(lift(Mod(o * g, o * m)^(-1)));
monic(P) = P / pollead(P);
eqD(D1, D2) = red(D1[1] - D2[1]) == 0 && red(D1[2] - D2[2]) == 0;
\\ Cantor addition
jadd(D1, D2, f) = {
  if (poldegree(D1[1], t) == 0, return(D2)); if (poldegree(D2[1], t) == 0, return(D1));
  my(u1 = o * D1[1], v1 = o * D1[2], u2 = o * D2[1], v2 = o * D2[2], ff = o * f, r, e1, e2, g, c1, c2, d, u, v, un, l);
  r = gcdext(u1, u2); e1 = r[1]; e2 = r[2]; g = r[3];
  l = pollead(g); e1 /= l; e2 /= l; g /= l;
  r = gcdext(g, v1 + v2); c1 = r[1]; c2 = r[2]; d = r[3];
  l = pollead(d); c1 /= l; c2 /= l; d /= l;
  u = (u1 * u2) \ d^2;
  v = ((c1 * e1 * u1 * v2 + c1 * e2 * u2 * v1 + c2 * (v1 * v2 + ff)) \ d) % u;
  while (poldegree(u, t) > 2,
    un = monic((ff - v^2) \ u);
    v = (-v) % un; u = un);
  if (poldegree(u, t) == 0, return([1, 0]));
  [red(u), red(v % u)];
}
jneg(D) = [D[1], red(-D[2])];
jmul(n, D, f) = { my(R = [1, 0], B = if (n < 0, jneg(D), D)); for (i = 1, abs(n), R = jadd(R, B, f)); R; }

\\ absolute field of K21[t]/(g): [nfabs, map of a polynomial in t over K21 to an absolute element]
absfield(g, plist) = {
  my(R = rnfequation(nf, o * g, 1), Pabs = R[1], a = R[2], k = R[3], nfa, img);
  \\ Pabs is not monic (the factors of fRev have denominators): nfinit returns [nf, c] with c the image of its root
  nfa = nfinit([Pabs, plist]); my(cz = Mod(variable(Pabs), Pabs));
  if (type(nfa) == "t_VEC" && #nfa == 2, cz = nfa[2]; nfa = nfa[1]);
  img = (P -> my(az = subst(lift(Mod(a, Pabs)), variable(Pabs), cz)); subst(subst(lift(o * P), t, cz - k * az), b, az));
  [nfa, img];
}

{
  my(tot = [0, 0, 0]);
  for (k = 1, 2,
    my(f = if (k == 1, F0, F1), fr, fa, q, h, T, pts = List(), Ps, lc);
    fr = polrecip(f); lc = pollead(fr, t);
    fa = nffactor(nf, fr);
    q = fa[1, 1]; h = fa[2, 1];
    chk(poldegree(q, t) == 2 && poldegree(h, t) == 4 && red(fr - lc * q * h) == 0, "fRev = lc q h");
    T = [q, 0];
    foreach(PHI, E, if (E[2] == k - 1,
      my(U = E[4], V = E[5], Ur, Vr);
      Ur = red(polrecip(U) / polcoef(U, 0, t));
      Vr = red((polcoef(V, 0, t) * t^3 + polcoef(V, 1, t) * t^2) % (o * Ur));
      chk(modp(Vr^2 - fr, Ur) == 0, "phi(x_i) on the reversed model");
      listput(pts, [Ur, Vr])));
    my(Pa = pts[1], Pb = pts[2]);
    Ps = [Pa, Pb, jadd(Pa, Pb, fr), jadd(Pa, jneg(Pb), fr), jadd(Pa, T, fr), jadd(Pb, T, fr), jmul(2, Pa, fr), jmul(2, Pb, fr),
          jadd(jmul(2, Pa, fr), Pb, fr), jadd(Pa, jmul(2, Pb, fr), fr), jadd(jadd(Pa, Pb, fr), T, fr), jmul(3, Pa, fr)];
    \\ prime data of F_q for the parity test: the primes p below PBOUND met by the classes, collected first
    my(cls = List(), plist = List());
    for (ip = 1, #Ps,
      my(P = Ps[ip], u, V, Nq, den);
      if (poldegree(P[1], t) != 2, next);
      u = P[1]; V = P[2];
      if (poldegree(gcd(o * u, o * fr), t) > 0, next);
      listput(cls, [ip, u, V]);
      Nq = norm(o * polresultant(o * u, o * q, t));
      den = lcm(apply(c -> denominator(content(lift(o * c))), Vec(u)));
      foreach(concat(factor(numerator(Nq), PBOUND)[, 1]~, concat(factor(denominator(Nq), PBOUND)[, 1]~, factor(den, PBOUND)[, 1]~)), pp,
        if (pp < PBOUND && pp % 2 && pp % 7 && isprime(pp), listput(plist, pp))));
    plist = Set(concat(Vec(plist), [3, 5, 11]));
    printf("twist %d: %d classes, parity primes %s\n", k - 1, #cls, plist);
    my(AF = absfield(q, concat([2, 7], plist)), nfq = AF[1], img = AF[2], prs = List());
    foreach(plist, pp, foreach(idealprimedec(nfq, pp), PP, listput(prs, PP)));
    foreach(cls, C,
      my(ip = C[1], u = C[2], V = C[3], w, uX, VX, fX, nA, nB, nP = 0);
      w = red((o * (V^2 - fr)) \ (o * u)); chk(red(V^2 - fr - u * w) == 0, "V^2 - f = u w");
      \\ (R)
      chk(red(polresultant(o * u, o * fr, t) - polresultant(o * u, o * V, t)^2) == 0, Str("(R) Res(u, f) = Res(u, V)^2, class ", ip));
      \\ (A), (B) in both factor fields
      uX = subst(u, t, X); VX = subst(V, t, X); fX = subst(fr, t, X);
      foreach([q, h], gi,
        my(th = Mod(o * t, o * gi), gg, lhs, rhs, uth);
        gg = (o * fX) \ (X - th); chk((o * fX) % (X - th) == 0, "X - theta divides f");
        uth = subst(o * uX, X, th);
        chk(uth * subst(o * subst(w, t, X), X, th) == subst(o * VX, X, th)^2, Str("(A) class ", ip, " factor deg ", poldegree(gi, t)));
        lhs = uth * polresultant(o * uX, gg, X); rhs = polresultant(o * uX, o * VX, X)^2;
        chk(lhs == rhs, Str("(B) u(theta) Res_{2,5}(u, f/(X - theta)) = Res(u, V)^2, class ", ip, " factor deg ", poldegree(gi, t))));
      \\ (P) on F_q
      my(uthA = img(u), u1A = img(polcoef(u, 1, t)), u0A = img(polcoef(u, 0, t)), fdA = img(deriv(fr, t)));
      foreach(prs, PP,
        my(vl = nfeltval(nfq, img(lc), PP), vd = nfeltval(nfq, fdA, PP), vint, vu, m);
        vint = vecmin(apply(cc -> nfeltval(nfq, img(cc), PP), Vec(fr)));
        chk(vl == 0 && vd == 0 && vint >= 0, Str("good reduction hypotheses at P above ", PP.p));
        vu = nfeltval(nfq, uthA, PP);
        m = min(0, min(nfeltval(nfq, u1A, PP), nfeltval(nfq, u0A, PP)));
        nP++;
        chk((vu - m) % 2 == 0, Str("(P) parity at P above ", PP.p, ": v(u(theta)) = ", vu, ", content ", m, ", class ", ip)));
      tot[1]++; tot[2] += nP);
    printf("twist %d: identities (R), (A), (B) and %d prime parity tests done\n", k - 1, tot[2]));
  printf("classes %d, prime tests %d; checks %d, failures %d\n", tot[1], tot[2], NCHK, NFAIL);
  print(if (NFAIL == 0 && tot[1] >= 16, "RESULT PASS", "RESULT FAIL"));
}
quit;
