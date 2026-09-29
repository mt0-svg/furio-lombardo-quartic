\\ schaefer_global_models.gp: the global Schaefer statement for fRev k with a change of model at the bad primes
\\ Input /tmp/k21c/sel/fields.bin is written by code/earlier-computations/prym_two_descent_lib.gp (the factor fields of p21_29).
\\ (the global statement, in the form corrected after schaefer_identities and schaefer_bad_models).
\\ fRev k is bad (outside 14) at pr3, pr439 (fRev = unit (t - r)^6 mod pr, v(disc) = 30) and at the five primes above
\\ 23 (v(lc) = 1: a root at infinity mod pr). Corrected construction, checked here on 12 Cantor classes per twist:
\\   (M) pi = a generator of pr3 pr439, aT = -469 (= -1 mod 3, = -30 mod 439), f1 = fRev(aT + pi t) / pi^6.
\\       Expected: f1 integral with lc(f1) = lc(fRev) and N(disc f1) = +-2^x 7^y (so f1 is good as a binary form outside 14,
\\       with lc a non unit exactly at the five primes above 23).
\\   (I) at the primes above 23: inverted models f2 = t^6 f1(a2 + 1/t) for a2 in {0, 1, 2}; expected f1(a2) a unit at the
\\       five primes above 23 (so lc(f2) a unit there, and disc(f2) = disc(f1)).
\\   (C) for a class [U, V] (U monic quadratic coprime to fRev): U1 = U(aT + pi t) / pi^2 (monic), c a generator of the
\\       fractional ideal (1, U1_1, U1_0). Claim: v_P(U(theta)) - v_P(c) is even at every prime P of F = K21[t]/(q) and
\\       F = K21[t]/(h) not above 14. Tested at every P above an odd prime p != 7 below PBOUND met by the class, and at
\\       every P above 3, 23, 439, 5, 11; the naive c0 (a generator of (1, U_1, U_0), the draft statement) is tested too.
\\   (H) at each tested P the hypotheses of the local lemma for the model used in the proof: f1 at P with lc unit
\\       (f1'(theta1) a unit, theta1 = (theta - aT)/pi), else f2 for the first a2 with U1(a2) != 0 (lc(f2) = f1(a2) and
\\       f2'(theta2) units, theta2 = 1/(theta1 - a2)), and the content transport v_P(c) = min(0, v_P(U2 coefficients) +
\\       v_P(U1(a2))) with U2 = t^2 U1(a2 + 1/t) / U1(a2).
\\ Run from code/selmer-global-bound (one twist per run, KLIST = [0] or [1]):
\\   echo "KLIST = [k]; read(\"schaefer_global_models.gp\")" | gp -q -D parisizemax=1800000000 -D nbthreads=1 > schaefer_global_models_twist<k>.out
\\ defaults are set on the command line (a default() inside read() aborts the read)
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
read("../earlier-computations/phi_known_lifts.gp");
PBOUND = 3000;
if (type(KLIST) == "t_POL", KLIST = [0, 1]);   \\ set KLIST = [0] or [1] before reading to run one twist
NCHK = 0; NFAIL = 0;
chk(c, msg) = { NCHK++; if (!c, NFAIL++; print("FAIL: ", msg)); };
o = Mod(1, K21);
red(g) = lift(o * g);
modp(g, m) = red(lift(Mod(o * g, o * m)));
monic(P) = P / pollead(P);
jadd(D1, D2, f) = {
  if (poldegree(D1[1], t) == 0, return(D2)); if (poldegree(D2[1], t) == 0, return(D1));
  my(u1 = o * D1[1], v1 = o * D1[2], u2 = o * D2[1], v2 = o * D2[2], ff = o * f, r, e1, e2, g, c1, c2, d, uu, vv, un, l);
  r = gcdext(u1, u2); e1 = r[1]; e2 = r[2]; g = r[3];
  l = pollead(g); e1 /= l; e2 /= l; g /= l;
  r = gcdext(g, v1 + v2); c1 = r[1]; c2 = r[2]; d = r[3];
  l = pollead(d); c1 /= l; c2 /= l; d /= l;
  uu = (u1 * u2) \ d^2;
  vv = ((c1 * e1 * u1 * v2 + c1 * e2 * u2 * v1 + c2 * (v1 * v2 + ff)) \ d) % uu;
  while (poldegree(uu, t) > 2,
    un = monic((ff - vv^2) \ uu);
    vv = (-vv) % un; uu = un);
  if (poldegree(uu, t) == 0, return([1, 0]));
  [red(uu), red(vv % uu)];
}
jneg(D) = [D[1], red(-D[2])];
jmul(n, D, f) = { my(R = [1, 0], B = if (n < 0, jneg(D), D)); for (i = 1, abs(n), R = jadd(R, B, f)); R; }
\\ absolute field of K21[t]/(g) with the order maximal at plist; img maps a polynomial in t over K21 to the element
\\ (a polmod) obtained by t -> theta
absfield(g, plist) = {
  my(R = rnfequation(nf, o * g, 1), Pabs = R[1], al = R[2], kk = R[3], nfa, cz);
  nfa = nfinit([Pabs, plist]); cz = Mod(variable(Pabs), Pabs);
  if (type(nfa) == "t_VEC" && #nfa == 2, cz = nfa[2]; nfa = nfa[1]);
  my(az = subst(lift(Mod(al, Pabs)), variable(Pabs), cz));
  [nfa, P -> Mod(subst(subst(lift(o * P), t, cz - kk * az), b, az), nfa.pol)];
}
\\ N = K21[t]/(h) through the field of p21_29 (/tmp/k21c/sel/fields.bin: nfN in y, aN the image of b, thN a root of the
\\ unreversed quartic A^2 - d B^2), maximal at plist; theta = 1/thN is a root of the reversed factor h (checked below)
absfield_h(plist) = {
  my(FF = read("/tmp/k21c/sel/fields.bin"), PNy = FF[3].pol, aN = lift(FF[6]), th = lift(1 / FF[7]), nfa);
  nfa = nfinit([PNy, plist]);
  [nfa, P -> Mod(subst(subst(lift(o * P), t, th), b, aN), PNy)];
}
vP(nfa, x, PP) = if (x == 0, 10^6, nfeltval(nfa, lift(x), PP));
\\ evaluate a polynomial in t over K21 at an absolute element xx: coefficientwise images
evabs(img, P, xx) = { my(s = 0); forstep (i = poldegree(P, t), 0, -1, s = s * xx + img(polcoef(P, i, t))); s; }
bnf = bnfinit(K21, 1);
gen(I) = { my(r = bnfisprincipal(bnf, I, 1 + 4), g); if (r[1] != 0, error("not principal")); g = nfbasistoalg(nf, nffactorback(nf, r[2]));
  if (idealhnf(nf, g) != idealhnf(nf, I), error("generator check")); g; };
cont(P) = { my(I = idealhnf(nf, 1)); for (i = 0, poldegree(P, t), my(cc = polcoef(P, i, t)); if (cc != 0, I = idealadd(nf, I, cc))); I; };
{
  my(tot = [0, 0, 0, 0]);
  foreach(KLIST, k,
    my(F = if (k == 0, F0, F1), fr = polrecip(F), lc = pollead(fr, t), fa = nffactor(nf, fr), q, h, dfr);
    q = fa[1, 1]; h = fa[2, 1];
    chk(red(fr - lc * q * h) == 0, "fRev = lc q h");
    dfr = red(poldisc(o * fr));
    my(pr3 = 0, pr439 = 0, pr23 = List());
    foreach(idealprimedec(nf, 3), pr, if (idealval(nf, dfr, pr) > 0, chk(pr3 == 0, "one bad prime above 3"); pr3 = pr));
    foreach(idealprimedec(nf, 439), pr, if (idealval(nf, dfr, pr) > 0, chk(pr439 == 0, "one bad prime above 439"); pr439 = pr));
    foreach(idealprimedec(nf, 23), pr, if (idealval(nf, lc, pr) > 0, listput(pr23, pr)));
    printf("twist %d: bad primes pr3 (f %d), pr439 (f %d), %d primes above 23 with v(lc) > 0 (f %s)\n", k, pr3.f, pr439.f,
           #pr23, apply(pr -> pr.f, Vec(pr23)));
    \\ (M)
    my(piT = gen(idealmul(nf, pr3, pr439)), aT = -469, f1, d1, nd1);
    chk(idealval(nf, piT, pr3) == 1 && idealval(nf, piT, pr439) == 1 && abs(norm(o * piT)) == 3 * 439, "pi generates pr3 pr439");
    printf("  pi = %s (norm %d)\n", piT, norm(o * piT));
    f1 = red(subst(fr, t, aT + piT * t) / piT^6);
    chk(#select(cc -> my(dd = denominator(nfalgtobasis(nf, cc))); dd != 2^valuation(dd, 2) * 7^valuation(dd, 7), Vec(f1)) == 0, "f1 integral outside 14");
    chk(red(pollead(f1, t) - lc) == 0, "lc(f1) = lc(fRev)");
    d1 = red(poldisc(o * f1)); nd1 = factor(norm(o * d1));
    printf("  N(disc f1) = %s\n", nd1);
    chk(#setminus(Set(nd1[, 1]~), [-1, 2, 7]) == 0, "disc f1 supported on 2, 7");
    \\ (I)
    foreach([0, 1, 2], a2, my(v1a = subst(f1, t, a2));
      foreach(pr23, pr, chk(idealval(nf, v1a, pr) == 0, Str("f1(", a2, ") unit at a prime above 23")));
      printf("  odd primes != 7 of N(f1(%d)): %s\n", a2, select(pp -> pp % 2 && pp != 7, factor(norm(o * v1a), 10^6)[, 1]~)));
    \\ classes
    my(T = [q, 0], pts = List(), Ps);
    foreach(PHI, E, if (E[2] == k,
      my(U = E[4], V = E[5], Ur, Vr);
      Ur = red(polrecip(U) / polcoef(U, 0, t));
      Vr = red((polcoef(V, 0, t) * t^3 + polcoef(V, 1, t) * t^2) % (o * Ur));
      chk(modp(Vr^2 - fr, Ur) == 0, "phi(x_i) on the reversed model");
      listput(pts, [Ur, Vr])));
    my(Pa = pts[1], Pb = pts[2]);
    Ps = [Pa, Pb, jadd(Pa, Pb, fr), jadd(Pa, jneg(Pb), fr), jadd(Pa, T, fr), jadd(Pb, T, fr), jmul(2, Pa, fr), jmul(2, Pb, fr),
          jadd(jmul(2, Pa, fr), Pb, fr), jadd(Pa, jmul(2, Pb, fr), fr), jadd(jadd(Pa, Pb, fr), T, fr), jmul(3, Pa, fr)];
    my(cls = List(), plist = List());
    for (ip = 1, #Ps,
      my(P = Ps[ip], U, den);
      if (poldegree(P[1], t) != 2, next);
      U = P[1];
      if (poldegree(gcd(o * U, o * fr), t) > 0, next);
      listput(cls, [ip, U, P[2]]);
      den = lcm(apply(cc -> denominator(content(lift(o * cc))), Vec(U)));
      foreach([q, h], gi, my(Nq = norm(o * polresultant(o * U, o * gi, t)));
        foreach(concat(factor(numerator(Nq), PBOUND)[, 1]~, concat(factor(denominator(Nq), PBOUND)[, 1]~, factor(den, PBOUND)[, 1]~)), pp,
          if (pp < PBOUND && pp % 2 && pp % 7 && isprime(pp), listput(plist, pp)))));
    plist = Set(concat(Vec(plist), [3, 5, 11, 23, 439]));
    printf("  %d classes, parity primes %s\n", #cls, plist);
    foreach([q, h], gi,
      my(AF = if (poldegree(gi, t) == 2, absfield(gi, plist), absfield_h(plist)), nfa = AF[1], img = AF[2], prs = List(), th, th1, lcA, npar = 0, nnaive = 0);
      foreach(plist, pp, foreach(idealprimedec(nfa, pp), PP, listput(prs, PP)));
      printf("  factor of degree %d: %d primes of F above the parity primes\n", poldegree(gi, t), #prs);
      th = img(t); th1 = (th - img(aT)) / img(piT); lcA = img(lc);
      chk(evabs(img, gi, th) == 0 && evabs(img, f1, th1) == 0, "theta, theta1 roots");
      foreach(cls, C,
        my(ip = C[1], U = C[2], U1, c, c0, uth);
        U1 = red(subst(U, t, aT + piT * t) / piT^2);
        chk(pollead(U1, t) == 1 && poldegree(U1, t) == 2, "U1 monic quadratic");
        c = gen(cont(U1)); c0 = gen(cont(U));
        uth = evabs(img, U, th);
        foreach(prs, PP,
          my(vu = vP(nfa, uth, PP), vc = vP(nfa, img(c), PP), vc0 = vP(nfa, img(c0), PP));
          chk((vu - vc) % 2 == 0, Str("(C) parity with c at P above ", PP.p, ", class ", ip, ": v(U(theta)) = ", vu, ", v(c) = ", vc));
          npar++;
          if ((vu - vc0) % 2, nnaive++;
            printf("    naive c0 fails at P above %d (f %d), class %d: v(U(theta)) = %d, v(c0) = %d, v(c) = %d\n", PP.p, PP.f, ip, vu, vc0, vc));
          \\ (H)
          if (vP(nfa, lcA, PP) == 0,
            chk(vP(nfa, evabs(img, deriv(f1, t), th1), PP) == 0, Str("(H) f1'(theta1) unit at P above ", PP.p));
            chk(vP(nfa, th1, PP) >= 0, "theta1 integral");
            chk(vecmin(apply(cc -> vP(nfa, img(cc), PP), Vec(U1))) == vc, "v(c) = content of U1 at P"),
            \\ else: inverted model
            my(a2 = -1, f2, U2, th2, ua);
            chk(PP.p == 23, "lc of fRev non unit only above 23");
            for (j = 0, 2, if (subst(U1, t, j) != 0, a2 = j; break));
            ua = red(subst(U1, t, a2));
            f2 = red(polrecip(subst(f1, t, t + a2)));
            U2 = red(polrecip(subst(U1, t, t + a2)) / ua);
            chk(poldegree(f2, t) == 6 && pollead(U2, t) == 1 && poldegree(U2, t) == 2, "inverted model shapes");
            th2 = 1 / (th1 - a2);
            chk(evabs(img, f2, th2) == 0, "theta2 root of f2");
            chk(vP(nfa, img(pollead(f2, t)), PP) == 0, Str("(H) lc(f2) unit at P above 23, a2 = ", a2));
            chk(vP(nfa, evabs(img, deriv(f2, t), th2), PP) == 0, Str("(H) f2'(theta2) unit at P above 23, a2 = ", a2));
            chk(vP(nfa, th2, PP) >= 0, "theta2 integral");
            chk(vecmin(apply(cc -> vP(nfa, img(cc), PP), Vec(U2))) + vP(nfa, img(ua), PP) == vc, "content transport");
            chk(evabs(img, U, th) == img(piT)^2 * (th1 - a2)^2 * img(ua) * evabs(img, U2, th2), "U(theta) = pi^2 (theta1 - a2)^2 U1(a2) U2(theta2)");
            tot[4]++));
        tot[1]++);
      tot[2] += npar; tot[3] += nnaive;
      printf("  factor of degree %d: %d parity tests with c, %d failures of the naive c0\n", poldegree(gi, t), npar, nnaive)));
  printf("class-factor pairs %d, parity tests %d (naive c0 failures %d), inverted model uses %d; checks %d, failures %d\n",
         tot[1], tot[2], tot[3], tot[4], NCHK, NFAIL);
  print(if (NFAIL == 0 && tot[1] >= 16 * #KLIST && tot[4] > 0, "RESULT PASS", "RESULT FAIL"));
}
quit;
