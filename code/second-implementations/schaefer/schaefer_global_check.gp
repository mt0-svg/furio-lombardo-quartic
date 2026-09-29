\\ schaefer_global_check.gp: second implementation of the global Schaefer lemma for k = 0, 1, in its corrected form.
\\ Written from scratch; shares no code with the first implementation (code/selmer-global-bound/schaefer_identities.gp, schaefer_local_numeric.gp, schaefer_bad_models.gp, schaefer_global_models.gp).
\\ fRev k is rebuilt from the Lean data (lean_data.gp, extracted from DataField.lean, Basic.lean, DataBruin.lean by
\\ extract_lean_data.sh) and compared with polrecip(F_k) of code/earlier-computations/bruin_form.gp.
\\ Checks, for k = 0, 1:
\\  (D) diagnosis: primes above 3, 439 with v(disc fRev) > 0, primes above 23 with v(lc) > 0, fRev mod those primes;
\\  (M) pi a generator of pr3 pr439 (ideal equality checked), aT = -469, f1 = pi^-6 fRev(aT + pi X): coefficients in
\\      O_K21[1/14] (zk coordinates), lc(f1) = lc(fRev), disc(f1) = pi^-30 disc(fRev), N(disc f1), v(disc f1) at pr3,
\\      pr439, Res(f1, f1') = -lc disc(f1), the ideal (Res(f1, f1')) supported on 2, 7 and the primes of lc;
\\  (I) for i = 0, 1, 2: f2 = X^6 f1(i + 1/X): lc(f2) = f1(i), disc(f2) = disc(f1), and the ideal
\\      (14^N lc, 14^N f1(i) Res(f2, f2')) has norm supported on 2, 7 (so the certificate y lc + z f1(i) r2 = 14^N exists);
\\  (T) the changes of model (U2, V2, W2, content transport) exactly on each pair and each i with U1(i) != 0;
\\  (C) on Mumford pairs (u, V) of fRev k over K21 (from PHI of code/earlier-computations/phi_known_lifts.gp, reversed, and sums and doubles
\\      computed here): c a generator of the content ideal of U1 = pi^-2 u(aT + pi X), c0 of u; at every prime E of the
\\      factor fields above pr3, pr439 and the degree one prime above 23 (through Q_p, local factors of the good model),
\\      the parity of v_E(u(theta)) - v_E(c), and of v_E(u(theta)) - v_E(c0) for the record.
\\ Run from code/second-implementations/schaefer: gp -q -D parisizemax=900000000 schaefer_global_check.gp > schaefer_global_check.out 2>&1
[X, t, b];
read("lean_data.gp");
read("../../earlier-computations/bruin_form.gp");
read("../../earlier-computations/phi_known_lifts.gp");
NCHK = 0; NFAIL = 0;
chk(c, msg) = { NCHK++; if (!c, NFAIL++; print("FAIL: ", msg)); };
Kp = Polrev(LfL, b);
chk(Kp == K21, "Lean fL = K21 of bruin_form");
wz = vector(21, j, Polrev(LzkNum[j], b) / LDz);
el(v) = Mod(sum(j = 1, 21, v[j] * wz[j]), Kp);
fRevL(k) = sum(j = 0, 6, el(LFnData[k + 1][7 - j]) * X^j) / 4;
nf = nfinit(Kp); bnf = bnfinit(nf, 1);
chk(vector(21, j, Mod(nf.zk[j], Kp)) == vector(21, j, Mod(wz[j], Kp)), "Lean zk = PARI nf.zk");
print("K21: disc ", factor(nf.disc), ", index ", factor(nf.index), ", class group (GRH, not used: generators are checked by ideal equality) ", bnf.cyc, ", nfcertify ", nfcertify(nf));
chk(nfcertify(nf) == [], "maximal order certified");
V(x, pr) = if (x == 0, oo, idealval(nf, lift(x), pr));
isS(n) = { n = abs(n); n /= 2^valuation(n, 2); n /= 7^valuation(n, 7); n == 1; };   \\ n a {2,7}-number (n rational)
intout14(x) = isS(denominator(nfalgtobasis(nf, lift(x))));
supp(n) = { my(fa = factor(n)); Set(fa[, 1]~); };
gen(I) = { my(r = bnfisprincipal(bnf, I, 1 + 4), g); chk(r[1] == 0, "principal"); g = r[2]; if (type(g) == "t_MAT", g = nffactorback(nf, g)); g = Mod(nfbasistoalg(nf, g), Kp);
  chk(idealhnf(nf, lift(g)) == idealhnf(nf, I), "generator equality"); g; };
contI(P) = { my(I = idealhnf(nf, 1)); for (i = 0, poldegree(P, X), my(cc = polcoef(P, i, X)); if (cc != 0, I = idealadd(nf, I, lift(cc)))); I; };
\\ Mumford arithmetic (u monic, u | v^2 - f), own implementation
mred(D, f) = { my(u = D[1], v = D[2]); while (poldegree(u, X) > 2, u = (f - v^2) \ u; u /= pollead(u); v = (-v) % u); [u, v % u]; };
madd(D1, D2, f) = { my(u1 = D1[1], v1 = D1[2], u2 = D2[1], v2 = D2[2], g = gcdext(u1, u2), a, l);
  l = pollead(g[3]); if (poldegree(g[3], X) > 0, return(0)); a = g[1] / l;
  mred([u1 * u2, (v1 + (v2 - v1) * a * u1) % (u1 * u2)], f); };
mdbl(D, f) = { my(u1 = D[1], v1 = D[2], g = gcdext(2 * v1, u1), inv, kk);
  if (poldegree(g[3], X) > 0, return(0)); inv = g[1] / pollead(g[3]);
  kk = (((f - v1^2) \ u1) * inv) % u1; mred([u1^2, (v1 + kk * u1) % u1^2], f); };
mneg(D) = [D[1], -D[2]];
okpair(D, f) = D != 0 && poldegree(D[1], X) == 2 && pollead(D[1]) == 1 && poldegree(D[2], X) <= 1 && (D[2]^2 - f) % D[1] == 0 && poldegree(gcd(D[1], f), X) == 0;
\\ p-adic embedding of K21 at a degree one prime pr: the root of Kp in Q_p with the residue of b mod pr
PREC = 80;
emb(pr) = { my(p = pr.p, r = -1, rts = polrootspadic(Kp, p, PREC), be);
  for (j = 0, p - 1, if (idealval(nf, b - j, pr) >= 1, r = j; break));
  chk(pr.f == 1 && pr.e == 1, "degree one prime");
  be = select(z -> valuation(z - r, p) >= 1, Vec(rts)); chk(r >= 0 && #be == 1, "one p-adic root with the residue of b"); be = be[1];

  x -> subst(lift(x), b, be) };
sP(s, P) = { my(r = 0); forstep (i = poldegree(P, X), 0, -1, r = r * X + s(polcoef(P, i, X))); r; };
{
  my(allpairs = 0, allpar = 0, allnaive = 0);
  for (k = 0, 1,
    my(f = fRevL(k), lc = pollead(f), D, pr3 = List(), pr439 = List(), pr23 = List(), piT, aT = -469, f1, d1, R1);
    print("\n=== twist ", k, " ===");
    chk(f == Mod(1, Kp) * subst(polrecip(if (k == 0, F0, F1)), t, X), "Lean fRev k = polrecip(F_k)");
    chk(poldegree(f, X) == 6, "deg fRev = 6");
    chk(vecmin(apply(cc -> intout14(cc), Vec(f))) == 1, "fRev integral outside 14");
    D = poldisc(f);
    print("  N(lc fRev) = ", factor(norm(lc)), "; N(disc fRev) = ", factor(norm(D)));
    foreach(idealprimedec(nf, 3), pr, if (V(D, pr) > 0, listput(pr3, pr)));
    foreach(idealprimedec(nf, 439), pr, if (V(D, pr) > 0, listput(pr439, pr)));
    foreach(idealprimedec(nf, 23), pr, if (V(lc, pr) > 0, listput(pr23, pr)));
    chk(#pr3 == 1 && #pr439 == 1, "one bad prime above 3 and one above 439");
    pr3 = pr3[1]; pr439 = pr439[1];
    foreach([pr3, pr439], pr, my(mp = nfmodprinit(nf, pr));
      printf("  (D) pr above %d, f %d: v(disc fRev) = %d, v(lc) = %d, fRev mod pr = %s\n", pr.p, pr.f, V(D, pr), V(lc, pr),
             factor(Pol(apply(cc -> nfmodpr(nf, lift(cc), mp), Vec(f)), 'X))));
    printf("  (D) primes above 23 with v(lc) > 0: %d, residue degrees %s, v(lc) %s, v(disc) %s\n", #pr23,
           apply(pr -> pr.f, Vec(pr23)), apply(pr -> V(lc, pr), Vec(pr23)), apply(pr -> V(D, pr), Vec(pr23)));
    \\ (M)
    piT = gen(idealmul(nf, pr3, pr439));
    chk(abs(norm(piT)) == 1317 && V(piT, pr3) == 1 && V(piT, pr439) == 1, "pi: norm 1317, v = 1 at pr3, pr439");
    f1 = subst(f, X, aT + piT * X) / piT^6;
    chk(vecmin(apply(cc -> intout14(cc), Vec(f1))) == 1, "(M) f1 coefficients in O_K21[1/14]");
    chk(vecmin(apply(cc -> V(cc, pr3), Vec(f1))) >= 0 && vecmin(apply(cc -> V(cc, pr439), Vec(f1))) >= 0, "(M) f1 integral at pr3, pr439");
    chk(pollead(f1) == lc, "(M) lc(f1) = lc(fRev)");
    d1 = poldisc(f1);
    chk(d1 == D / piT^30, "(M) disc(f1) = pi^-30 disc(fRev)");
    printf("  (M) N(disc f1) = %s, v(disc f1) at pr3 = %d, at pr439 = %d\n", factor(norm(d1)), V(d1, pr3), V(d1, pr439));
    chk(isS(norm(d1)), "(M) N(disc f1) a {2,7}-number");
    R1 = polresultant(f1, deriv(f1, X), X);
    chk(R1 == -lc * d1, "(M) Res(f1, f1') = -lc disc(f1)");
    chk(#setminus(supp(norm(R1)), [-1, 2, 7, 23]) == 0, "(M) N(Res(f1, f1')) supported on 2, 7, 23");
    \\ the Bezout identity with integral cofactors: A f1 + B f1' = R1 with A, B in O_K21[1/14][X] (subresultant cofactors)
    my(bz = polresultantext(f1, deriv(f1, X), X));
    chk(bz[1] * f1 + bz[2] * deriv(f1, X) == bz[3] && bz[3] == R1, "(M) Bezout identity A f1 + B f1' = Res");
    chk(vecmin(apply(cc -> intout14(cc), concat(Vec(bz[1]), Vec(bz[2])))) == 1, "(M) Bezout cofactors in O_K21[1/14][X]");
    \\ (I)
    for (i = 0, 2,
      my(v1 = subst(f1, X, i), f2 = polrecip(subst(f1, X, X + i)), R2, I2, N);
      chk(pollead(f2) == v1 && poldegree(f2, X) == 6, "(I) lc(f2) = f1(i)");
      chk(poldisc(f2) == d1, "(I) disc(f2) = disc(f1)");
      R2 = polresultant(f2, deriv(f2, X), X);
      my(bz2 = polresultantext(f2, deriv(f2, X), X));
      chk(bz2[3] == R2 && vecmin(apply(cc -> intout14(cc), concat(Vec(bz2[1]), Vec(bz2[2])))) == 1, "(I) Bezout for f2 over O_K21[1/14]");
      N = 14^60;
      chk(intout14(lc) && intout14(v1 * R2), "(I) lc, f1(i) r2 in O_K21[1/14]");
      I2 = idealadd(nf, lift(N * lc), lift(N * v1 * R2));
      printf("  (I) i = %d: v(f1(i)) at the primes above 23 with v(lc) > 0: %s; N((14^60 lc, 14^60 f1(i) r2)) = %s\n", i,
             apply(pr -> V(v1, pr), Vec(pr23)), factor(idealnorm(nf, I2)));
      chk(isS(idealnorm(nf, I2)), Str("(I) lc and f1(", i, ") r2 coprime outside 14")));
    \\ (C) Mumford pairs
    my(q, h, fa = nffactor(nf, lift(f)), base = List(), pairs = List());
    chk(#fa~ == 2, "two factors");
    q = Mod(1, Kp) * fa[1, 1]; h = Mod(1, Kp) * fa[2, 1];
    chk(poldegree(q, X) == 2 && poldegree(h, X) == 4 && f == lc * q * h, "fRev = lc q h");
    foreach(PHI, E, if (E[2] == k, my(U = Mod(1, Kp) * subst(E[4], t, X), W = Mod(1, Kp) * subst(E[5], t, X), Ur, Vr);
      chk((W^2 - subst(if (k == 0, F0, F1), t, X)) % U == 0, "PHI pair on F_k");
      Ur = polrecip(U) / polcoef(U, 0, X);
      Vr = (polcoef(W, 0, X) * X^3 + polcoef(W, 1, X) * X^2) % Ur;
      listput(base, [Ur, Vr])));
    my(Pa = base[1], Pb = base[2], cand);
    cand = [Pa, Pb, madd(Pa, Pb, f), madd(Pa, mneg(Pb), f), mdbl(Pa, f), mdbl(Pb, f)];
    cand = concat(cand, [madd(cand[5], Pb, f), madd(cand[6], Pa, f), madd(cand[5], Pa, f), madd(cand[3], cand[3], f),
                         mdbl(cand[3], f), mdbl(cand[4], f), madd(cand[5], cand[6], f)]);
    for (j = 1, #cand, if (okpair(cand[j], f), listput(pairs, [j, cand[j]])));
    printf("  (C) %d Mumford pairs (u monic quadratic coprime to fRev, u | V^2 - fRev) out of %d candidates\n", #pairs, #cand);
    \\ (T) the two changes of model on every pair, exactly over K21: V1^2 - f1 = U1 W1 with deg W1 = 4; for each i in
    \\ {0, 1, 2} with U1(i) != 0: U2 = U1(i)^-1 X^2 U1(i + 1/X) monic quadratic, V2 = (X^3 V1(i + 1/X)) mod U2 of degree
    \\ <= 1, U2 | V2^2 - f2, deg W2 = 4, and the content ideal of U1(i) U2 equals the content ideal of U1
    my(nT = 0);
    foreach(pairs, PJ, my(u = PJ[2][1], vv = PJ[2][2], U1, V1, W1);
      U1 = subst(u, X, aT + piT * X) / piT^2; V1 = subst(vv, X, aT + piT * X) / piT^3;
      chk((V1^2 - f1) % U1 == 0, "(T) U1 | V1^2 - f1"); W1 = (V1^2 - f1) \ U1; chk(poldegree(W1, X) == 4, "(T) deg W1 = 4");
      for (i = 0, 2, my(ui = subst(U1, X, i), U2, V2, f2, W2);
        if (ui == 0, next);
        f2 = polrecip(subst(f1, X, X + i));
        U2 = polrecip(subst(U1, X, X + i)) / ui;
        V2 = (polcoef(V1, 1, X) * X^2 + (polcoef(V1, 1, X) * i + polcoef(V1, 0, X)) * X^3) % U2;
        chk(pollead(U2) == 1 && poldegree(U2, X) == 2 && poldegree(V2, X) <= 1, "(T) U2 monic quadratic, deg V2 <= 1");
        chk((V2^2 - f2) % U2 == 0, "(T) U2 | V2^2 - f2");
        W2 = (V2^2 - f2) \ U2; chk(poldegree(W2, X) == 4, "(T) deg W2 = 4");
        chk(contI(ui * U2) == contI(U1), "(T) content transport");
        nT++));
    printf("  (T) changes of model checked exactly on %d (pair, i)\n", nT);
    my(places = List([pr3, pr439]));
    foreach(pr23, pr, if (pr.f == 1, listput(places, pr)));
    foreach(places, pr,
      my(s = emb(pr), p = pr.p, lcu = V(lc, pr) == 0, ii, npar = 0, nnaive = 0);
      \\ the local model: model 1 if lc is a unit at pr, model 2 (i = 0: f1(0) is a unit at pr) otherwise
      foreach([q, h], g,
        my(g1 = subst(g, X, aT + piT * X) / piT^poldegree(g, X), gm, loc);
        gm = if (lcu, sP(s, g1), my(g2 = polrecip(g1) / polcoef(g1, 0, X)); sP(s, g2));
        loc = factorpadic(gm, p, PREC)[, 1];
        foreach(loc, gl,
          my(d = poldegree(gl, X), glb = Mod(1, p) * Pol(apply(cc -> truncate(cc), Vec(gl / pollead(gl))), 'X));
          chk(vecmin(apply(cc -> valuation(cc, p), Vec(gl / pollead(gl)))) >= 0 && polisirreducible(glb), Str("unramified local factor above ", p));
          foreach(pairs, PJ,
            my(j = PJ[1], u = PJ[2][1], U1 = subst(u, X, aT + piT * X) / piT^2, c = gen(contI(U1)), vc = V(c, pr), c0 = gen(contI(u)),
               vc0 = V(c0, pr), Nu, vU);
            \\ norm of u(theta) over the local field, from the roots of the model: theta = aT + pi theta1 (model 1),
            \\ theta = aT + pi (0 + 1/theta2) (model 2)
            if (lcu,
              Nu = polresultant(gl / pollead(gl), sP(s, subst(u, X, aT + piT * X)), X),
              my(nn = (aT * X + piT)^2 + polcoef(u, 1, X) * X * (aT * X + piT) + polcoef(u, 0, X) * X^2);   \\ X^2 u(aT + pi/X), i = 0
              Nu = polresultant(gl / pollead(gl), sP(s, nn), X) / polcoef(gl / pollead(gl), 0, X)^2);
            vU = valuation(Nu, p) / d;
            chk(type(vU) == "t_INT", "integral local valuation");
            chk((vU - vc) % 2 == 0, Str("(C) parity with c at a prime above ", p, " (local degree ", d, "), pair ", j,
                                         ": v(u(theta)) = ", vU, ", v(c) = ", vc));
            npar++;
            if ((vU - vc0) % 2, nnaive++;
              printf("    naive c0 fails above %d (local degree %d, factor of degree %d), pair %d: v(u(theta)) = %d, v(c0) = %d, v(c) = %d\n",
                     p, d, poldegree(g, X), j, vU, vc0, vc)))));
      printf("  (C) pr above %d (model %d): %d parity tests with c, %d naive c0 failures\n", p, if (lcu, 1, 2), npar, nnaive);
      allpar += npar; allnaive += nnaive);
    allpairs += #pairs);
  printf("\nMumford pairs %d, parity tests %d (naive c0 failures %d); checks %d, failures %d\n", allpairs, allpar, allnaive, NCHK, NFAIL);
  print(if (NFAIL == 0, "RESULT PASS", "RESULT FAIL"));
}
quit;
