\\ pgen_polynomials.gp: the 82 polynomials Pgen s in K21[X] of degree at most 5 with
\\   Pgen s (alpha) = gensL s, Pgen s (beta) = 1           for s < 29,
\\   Pgen s (alpha) = 1,       Pgen s (beta) = gensN (s - 29) for s >= 29,
\\ alpha, beta the roots of q, h of sb_5a, gensL, gensN the generators of sb_5b (data file sunit_generators_data.gp, see
\\ sunit_generators_recover.gp). Construction (CRT over K21):
\\ L generator x = c0 + c1 alpha (c1 = x1 / alpha1, c0 = x0 - c1 alpha0), Pgen = P + q ((1 - P) q^-1 mod h);
\\ N generator x = P(beta) with deg P <= 3 (4 x 4 solve on 1, beta, beta^2, beta^3), Pgen = P + h ((1 - P) h^-1 mod q).
\\ Export format: pgenDen s = the least common denominator of the zk coordinates of the 6 coefficients, pgen s = the
\\ 6 coefficients (constant term first) of pgenDen s * Pgen s as zk lists of length 21. Checks are exact, on the
\\ exported integer data. Power tables (for the Lean evaluation of Pgen s at alpha, beta): alphaPow i = (alphaDen alpha)^i
\\ in the format of gL, betaPow i = (betaPowDen beta)^i in the format of gN (b = c / 2), betaPowDen = 2 betaDen (the
\\ coordinates b of (betaDen beta)^1 are not all integral), i = 0..5, integral (checked), and
\\ sum_i pgen s i alphaPow i alphaDen^(5 - i) = pgenDen s alphaDen^5 Pgen s (alpha) (likewise beta over betaPowDen)
\\ exactly on the integer data. Output cache /tmp/sb5/pgen.bin. Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/pgen_polynomials.gp < /dev/null > ../selmer-global-bound/pgen_polynomials.out 2>&1
default(parisizemax, 900 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
read("../selmer-global-bound/tower_lib.gp");
OUT = "/tmp/sb5/pgen.bin";

\\ polynomial with polmod coefficients -> coefficient vector (columns, constant first) of length n
pvec(pol, n) = vector(n, i, Kc(polcoef(pol, i - 1, 'X)));

main() = {
  my(t0 = getabstime(), TW = read("/tmp/sb5/tower.bin"), GN = sb5_gens("../selmer-global-bound/sunit_generators_data.gp"), q, h, al, be, qp, hp, qinv, hinv, Bp, P6 = List(), dens = List(), lists = List());
  nfK = nfinit(K21); EPS = TW[1]; EN = TW[2]; q = TW[3]; h = TW[4]; al = TW[7]; be = TW[8];
  qp = Kpol(q); hp = Kpol(h);
  \\ tool test: inverse modulo a polynomial over K21 (polmod coefficients)
  qinv = lift(Mod(1, hp) / Mod(qp, hp)); hinv = lift(Mod(1, qp) / Mod(hp, qp));
  chk5(lift(Mod(qinv * qp, hp)) == 1 && lift(Mod(hinv * hp, qp)) == 1 && poldegree(qinv) <= 3 && poldegree(hinv) <= 1, "tool: q^-1 mod h and h^-1 mod q over K21");
  chk5(lift(Mod(qinv * qp + 1, hp)) != 1, "tool: negative control (q^-1 q + 1 is not 1 mod h)");
  Bp = vector(4, i, Npow(be, i - 1));
  my(genL = GN[1], genN = GN[2]);
  chk5(#genL == 29 && #genN == 53, "29 + 53 generators from sb_5b (data file)");
  for (s = 1, 82,
    my(P, Pg, cf, dn, ok1, ok2);
    if (s <= 29,
      my(xx = genL[s][1], c1 = Kd(xx[2], al[2]), c0 = xx[1] - Km(c1, al[1]));
      P = nfbasistoalg(nfK, c0) + nfbasistoalg(nfK, c1) * 'X;
      chk5(Lev([c0, c1], al) == xx, Str("generator ", s - 1, " of L42 = c0 + c1 alpha"));
      Pg = P + qp * lift(Mod((1 - P) * qinv, hp))
    ,
      my(xx = Nunfmt(genN[s - 29][1]), cc = Ksolve(Bp, xx));
      P = sum(i = 1, 4, nfbasistoalg(nfK, cc[i]) * 'X^(i - 1));
      chk5(Nev(cc, be) == xx, Str("generator ", s - 30, " of N84 = P(beta), deg P <= 3"));
      Pg = P + hp * lift(Mod((1 - P) * hinv, qp)));
    chk5(poldegree(Pg, 'X) <= 5, Str("deg Pgen ", s - 1, " <= 5"));
    cf = pvec(Pg, 6); dn = den5(cf);
    my(ls = vector(6, i, Klist(dn * cf[i])), cfe = vector(6, i, KofList(ls[i]) / dn));
    \\ exact checks on the exported data
    ok1 = Lev(cfe, al); ok2 = Nev(cfe, be);
    if (s <= 29, chk5(ok1 == genL[s][1] && ok2 == NofK(1), Str("Pgen ", s - 1, " (alpha) = gensL ", s - 1, ", Pgen ", s - 1, " (beta) = 1 (exported data)")),
      chk5(ok1 == [Kc(1), Kc(0)] && ok2 == Nunfmt(genN[s - 29][1]), Str("Pgen ", s - 1, " (alpha) = 1, Pgen ", s - 1, " (beta) = gensN ", s - 30, " (exported data)")));
    listput(dens, dn); listput(lists, ls));
  dens = Vec(dens); lists = Vec(lists);
  \\ ---- power tables
  my(aD = TW[20], bD = TW[22], aI = [KofList(TW[21][1]), KofList(TW[21][2])], bI = vector(4, i, KofList(TW[23][i])), aP, bP, aPl, bPl, bad = 0);
  chk5(aI == Lsc(aD, al) && bI == Nsc(bD, be), "alphaDen alpha = alphaL, betaDen beta = betaN (plain coordinates) of sb_5a");
  aP = vector(6, i, Lpow(aI, i - 1));
  printf("power tables: denominators of (alphaDen alpha)^i %s, of (betaDen beta)^i in the format of gN (b = c / 2) %s\n", apply(den5, aP), apply(den5, vector(6, i, Nfmt(Npow(bI, i - 1)))));
  \\ (betaDen beta)^1 has a coordinate b = c / 2 with c odd: the table uses betaPowDen = 2 betaDen
  bD = 2 * bD; bI = Nsc(2, bI); bP = vector(6, i, Nfmt(Npow(bI, i - 1)));
  chk5(vecmax(apply(den5, aP)) == 1, "alphaPow i = (alphaDen alpha)^i, i = 0..5: integral zk coordinates (format of gL)");
  chk5(vecmax(apply(den5, bP)) == 1, Str("betaPow i = (betaPowDen beta)^i, betaPowDen = 2 betaDen = ", bD, ", i = 0..5: integral zk coordinates in the format of gN (b = c / 2)"));
  aPl = apply(v -> [Klist(v[1]), Klist(v[2])], aP); bPl = apply(v -> vector(4, i, Klist(v[i])), bP);
  printf("power tables: bits of alphaPow %s, of betaPow %s\n", apply(bits5, aPl), apply(bits5, bPl));
  \\ exact identities on the integer data: sum_i c_i P_i D^(5 - i) = pgenDen D^5 target
  for (s = 1, 82, my(c = vector(6, i, KofList(lists[s][i])), la = [Kc(0), Kc(0)], nb = NofK(0), ta, tb);
    for (i = 1, 6, la = Ladd(la, Lsc(c[i] * aD^(6 - i), [KofList(aPl[i][1]), KofList(aPl[i][2])]));
      nb = Nadd(nb, Nsc(c[i] * bD^(6 - i), Nunfmt(vector(4, j, KofList(bPl[i][j]))))));
    ta = if (s <= 29, genL[s][1], [Kc(1), Kc(0)]); tb = if (s <= 29, NofK(1), Nunfmt(genN[s - 29][1]));
    if (la != Lsc(dens[s] * aD^5, ta) || nb != Nsc(dens[s] * bD^5, tb), bad++));
  chk5(bad == 0, "sum_i pgen s i alphaPow i alphaDen^(5-i) = pgenDen s alphaDen^5 Pgen s (alpha), sum_i pgen s i betaPow i betaPowDen^(5-i) = pgenDen s betaPowDen^5 Pgen s (beta) (82 x 2 exact identities on the exported integers)");
  my(ng = lists[3]); ng[2] = ng[2] + vector(21, j, j == 1);
  chk5(Lev(vector(6, i, KofList(ng[i]) / dens[3]), al) != genL[3][1], "negative control: pgen 2 with its X coefficient changed by 1 misses gensL 2");
  printf("pgenDen: bits min %d max %d; the distinct prime factors below 10^6 of the denominators: %s\n", vecmin(apply(d -> ceil(log(d + 1) / log(2)), dens)), vecmax(apply(d -> ceil(log(d + 1) / log(2)), dens)),
    Set(concat(apply(d -> factor(d, 10^6)[, 1]~, dens))));
  printf("pgen numerators: max bits per polynomial %s\n", apply(bits5, lists));
  printf("pgen: total size %d integers, %d decimal digits in all\n", 82 * 6 * 21, sum(s = 1, 82, sum(i = 1, 6, sum(j = 1, 21, #Str(abs(lists[s][i][j]))))));
  system(Str("rm -f ", OUT));
  writebin(OUT, [lists, dens, aPl, bPl, bD]);
  chk5(read(OUT)[2] == dens && read(OUT)[4] == bPl, "cache /tmp/sb5/pgen.bin written and read back");
  printf("DONE pgen_polynomials: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
