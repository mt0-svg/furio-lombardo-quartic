\\ class_group_n84_two.gp: Cl(N)[2] = 0 without GRH, for N = L[t]/(G2) (degree 84), L = K21(sqrt d) (degree 42), where
\\ h = A^2 - d B^2 = G2 G3 over L, G2 = A - sqrt(d) B (the quartic factor of the Weierstrass polynomial of F_delta).
\\
\\ Ambiguous class number formula (Chevalley) for the quadratic extension N/L, N = L(sqrt e), e = disc(G2):
\\   |Cl(N)^G| = h(L) 2^(t-1) / [E_L : E_L cap N(N^x)],  t = number of places of L ramified in N (finite and real).
\\ By Hasse's norm theorem a unit is a norm iff it is a local norm everywhere; units are local norms at unramified
\\ finite places, so [E_L : E_L cap N] = size of the image of E_L/E_L^2 -> (+-1)^t, u -> ((u, e)_w)_w ramified.
\\ h(L) is odd (Cl(L)[2] = 0: class_group_l42_two.gp). If the image has size
\\ 2^(t-1), |Cl(N)^G| is odd, and a nontrivial 2-group with an action of a group of order 2 has a nontrivial fixed
\\ point, so Cl(N)[2] = 0.
\\ E_L/E_L^2 unconditionally: dimension r1 + r2 = 24 (Dirichlet, -1 included); any 24 units of L independent modulo
\\ squares (quadratic characters at auxiliary primes, character matrix of rank 24) span it. The units come from a
\\ GRH bnf but are exact elements, checked to be units.
\\ Also printed: the primes of L above 2 and 7 and their decomposition in N (for #S_N).
\\ Run from code/earlier-computations: gp -q class_group_n84_two.gp < /dev/null
default(parisizemax, 6*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
read("richelot_data.gp");
read("field_l42_polynomial.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
charmat(nf, els, nprimes) = {
  my(rows = List(), cnt = 0);
  forprime(p = 101, 10^7,
    if (cnt >= nprimes, break);
    my(dec = idealprimedec(nf, p));
    for (j = 1, #dec, my(pr = dec[j]);
      if (pr.f != 1 || pr.e != 1 || cnt >= nprimes, next);
      my(ok = 1, row = vector(#els));
      for (i = 1, #els, my(v = idealval(nf, els[i], pr)); if (v != 0, ok = 0; break);
        my(r = nfmodpr(nf, els[i], nfmodprinit(nf, pr)));
        row[i] = if (issquare(r), 0, 1));
      if (ok, listput(rows, row); cnt++)));
  matrix(#rows, #els, i, j, rows[i][j]);
}
main() = {
  my(t0 = getabstime(), R = RIN[1], A = R[3], B = R[4], d = R[5], bnfL, nfL, emb, bL, sd, G2, e, EL, M, rd, ramf, ramfin, sg, ramreal, tt, Hs, rk, toL);
  bnfL = bnfinit(nfinit([Lpol, [2, 7]]), 1); nfL = bnfL.nf;
  printf("bnfinit(L): %d ms, signature %s\n", getabstime() - t0, nfL.sign);
  emb = nfisincl(K21, Lpol); chk(#emb >= 1, Str("K21 embeds into L (", #emb, " embeddings)"));
  bL = Mod(emb[1], Lpol);
  toL = (pk -> subst(lift(pk), b, bL));   \\ element of K21 (polynomial in b) -> element of L (polmod in u)
  sd = nfroots(nfL, t^2 - lift(toL(Mod(d, K21)))); chk(#sd == 2, "d is a square in L");
  sd = Mod(sd[1], Lpol);
  G2 = toL(A) - sd * toL(B); G2 = G2 / pollead(G2);
  \\ h = G2 G3 over L with G3 the conjugate
  chk(toL(A)^2 - toL(Mod(d, K21)) * toL(B)^2 == pollead(toL(A)^2 - toL(Mod(d, K21)) * toL(B)^2) * G2 * (toL(A) + sd * toL(B)) / pollead(toL(A) + sd * toL(B)), "h = G2 G3 over L");
  chk(poldegree(G2, t) == 2, "G2 is quadratic in t");
  e = poldisc(G2); e = e * denominator(content(lift(e)))^2;   \\ integral representative of the square class
  chk(#nfroots(nfL, t^2 - lift(e)) == 0, "e = disc(G2) is not a square in L (N/L quadratic)");
  EL = concat([bnfL.tu[2]], bnfL.fu);
  chk(#EL == nfL.sign[1] + nfL.sign[2], Str("E_L/E_L^2 candidate basis of size r1 + r2 = ", #EL));
  for (i = 1, #EL, if (abs(norm(Mod(lift(EL[i]), Lpol))) != 1 || denominator(content(nfalgtobasis(nfL, EL[i]))) != 1, error("not a unit")));
  M = charmat(nfL, apply(v -> lift(v), EL), 2 * #EL + 10);
  chk(matrank(Mod(M, 2)) == #EL, Str("the ", #EL, " units are independent modulo squares: they span E_L/E_L^2"));
  rd = rnfdisc(nfL, t^2 - lift(e));
  ramf = idealfactor(nfL, rd[1]);
  ramfin = vector(#ramf~, j, ramf[j, 1]);
  print("finite primes of L ramified in N: ", vector(#ramfin, j, [ramfin[j].p, ramfin[j].f, ramfin[j].e, ramf[j, 2]]));
  sg = nfeltsign(nfL, lift(e));
  ramreal = [j | j <- [1..#sg], sg[j] < 0];
  print("real places of L ramified in N (e < 0): ", ramreal, " of ", #sg);
  tt = #ramfin + #ramreal;
  Hs = matrix(#EL, tt);
  for (i = 1, #EL, for (j = 1, tt,
    Hs[i, j] = if (j <= #ramfin, (1 - nfhilbert(nfL, lift(EL[i]), lift(e), ramfin[j])) / 2, nfeltsign(nfL, lift(EL[i]), ramreal[j - #ramfin]) < 0)));
  rk = matrank(Mod(Hs, 2));
  printf("t = %d ramified places; rank of the unit symbol matrix = %d (%d ms)\n", tt, rk, getabstime() - t0);
  chk(rk == tt - 1, "[E_L : E_L cap N(N^x)] = 2^(t-1): |Cl(N)^G| = h(L) is odd, so Cl(N)[2] = 0");
  \\ primes of L above 2 and 7 and their behaviour in N = L(sqrt e)
  my(SL = concat(idealprimedec(nfL, 2), idealprimedec(nfL, 7)), nS = 0);
  for (j = 1, #SL, my(pr = SL[j], ram = 0, spl);
    for (k = 1, #ramfin, if (idealval(nfL, ramfin[k], pr) > 0 && ramfin[k].p == pr.p && idealval(nfL, pr.gen[1], ramfin[k]) > 0 && ramfin[k] == pr, ram = 1));
    spl = if (ram, 1, if (nfislocalpower(nfL, pr, lift(e), 2), 2, 1));
    nS += spl;
    printf("  prime of L above %d, e = %d, f = %d: %s in N\n", pr.p, pr.e, pr.f, if (ram, "ramified", if (spl == 2, "split", "inert"))));
  printf("#S_L = %d, #S_N = %d; expected dim N(S,2) = r1(N) + r2(N) + #S_N = %d\n", #SL, nS, 6 + 39 + nS);
  print("RESULT PASS");
}
main();
quit;
