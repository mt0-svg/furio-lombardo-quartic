\\ count_local_facts.gp: the local facts behind CountBound at v, w2, w3 (twists 0, 1) and at the place above 7 (twist 1).
\\ For each twist k, fRev k = polrecip(F_k) = lc q h over K21 (q quadratic, h quartic, monic), d = disc(q):
\\  (a) per place: e, f of the prime, valuations of lc, d, disc(h), disc(fRev), and whether each is a local square
\\      (nfislocalpower); GoodSextic needs lc a non square, #J[2] <= 4 at w2, w3 needs d a non square (no root of f),
\\      #J[2] <= 8 at 7 needs f not split over K_7 (implied by disc(h) a non square: if f splits, d, disc(h+), disc(h-) are
\\      squares, and disc(h) = disc(h+) disc(h-) Res(h+, h-)^2).
\\  (b) base points: integers a with |a| <= 30 and f0 = fRev(a) != 0; P = sqrt(fRev(X + a) / f0) truncated at degree 3
\\      (a power series over K21), R = fRev(X + a) - f0 P^2 = r4 X^4 + r5 X^5 + r6 X^6; R7's Setup needs r4 != 0, r6 != 0
\\      (then V0 = b P with b^2 = f0 and w0 = X^2 + (r5/r6) X + r4/r6); f0 a local square at the place gives b in K_w.
\\      Also: is f0 a square in K21 (a global base point)?
\\ Run from code/selmer-local-conditions: gp -q count_local_facts.gp < /dev/null > count_local_facts.out 2>&1
default(parisizemax, 2*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
o = Mod(1, K21);
red(g) = lift(o * g);
P2 = idealprimedec(nf, 2); P7 = idealprimedec(nf, 7);
pv = [pr | pr <- P2, pr.e == 3][1]; pw2 = [pr | pr <- P2, pr.e == 12][1]; pw3 = [pr | pr <- P2, pr.e == 6][1]; p7 = P7[1];
PL = [["v", pv], ["w2", pw2], ["w3", pw3], ["7", p7]];
print("primes above 2: ", apply(pr -> [pr.e, pr.f], P2), "; above 7: ", apply(pr -> [pr.e, pr.f], P7));
sq(x, pr) = nfislocalpower(nf, pr, x, 2);
vv(x, pr) = idealval(nf, x, pr);
{
  for (k = 0, 1,
    my(F = if (k == 0, F0, F1), fr = polrecip(F), lc = pollead(fr, t), fa = nffactor(nf, fr), q, h, d, dh, df);
    q = fa[1, 1]; h = fa[2, 1];
    if (poldegree(q, t) != 2, my(tmp = q); q = h; h = tmp);
    d = red(poldisc(o * q)); dh = red(poldisc(o * h)); df = red(poldisc(o * fr));
    print("twist ", k, ": degrees ", [poldegree(q, t), poldegree(h, t)], ", fRev = lc q h: ", red(fr - lc * q * h) == 0);
    foreach(PL, pl, my(pr = pl[2]);
      printf("  %s (e = %d, f = %d): v(lc) = %d sq %d; v(d) = %d sq %d; v(disc h) = %d sq %d; v(disc f) = %d sq %d\n",
        pl[1], pr.e, pr.f, vv(lc, pr), sq(lc, pr), vv(d, pr), sq(d, pr), vv(dh, pr), sq(dh, pr), vv(df, pr), sq(df, pr)));
    my(good = List());
    for (a = -30, 30,
      my(fT = red(subst(fr, t, t + a)), f0 = polcoef(fT, 0, t), P, R, r4, r5, r6, loc, glob);
      if (f0 == 0, next);
      P = truncate(sqrt(Ser(o * fT / f0, t, 4)));
      P = red(P);
      R = red(fT - f0 * P^2);
      if (valuation(R, t) < 4 || poldegree(R, t) > 6, error("bad remainder at a = ", a));
      r4 = polcoef(R, 4, t); r5 = polcoef(R, 5, t); r6 = polcoef(R, 6, t);
      loc = apply(pl -> sq(f0, pl[2]), PL);
      glob = #nfroots(nf, 'y^2 - f0) > 0;
      if (r4 != 0 && r6 != 0 && (vecsum(loc) > 0 || glob),
        listput(good, [a, loc, glob, vv(f0, pv), vv(f0, pw2), vv(f0, pw3), vv(f0, p7)])));
    print("  base points a (|a| <= 30, r4, r6 != 0, f0 a square somewhere): [a, [square at v, w2, w3, 7], global square, v_v, v_w2, v_w3, v_7 of f0]");
    foreach(good, g, print("    ", g)));
}
print("DONE");
