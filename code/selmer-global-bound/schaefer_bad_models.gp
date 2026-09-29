\\ schaefer_bad_models.gp: where the model fRev k = polrecip(F_k) fails the hypotheses of the local Schaefer lemma
\\ (f integral, leading coefficient a unit, f'(theta) a unit), prime by prime.
\\ For k = 0, 1 and every prime pr of K21 above an odd prime p != 7 dividing the norm of lc(fRev), lc(F), disc(fRev),
\\ Res(q, h), disc(q), disc(h) or a coefficient denominator of fRev: the valuations at pr of these quantities, the
\\ factorization of fRev mod pr, and whether F_k (the unreversed model) is good at pr.
\\ Also: a check that the PARI F_k is the Lean f_k (lc(fRev) = F_k(0) and fRev = lc q h with q, h monic).
\\ Run from code/selmer-global-bound: gp -q schaefer_bad_models.gp > schaefer_bad_models.out
default(parisizemax, 2*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
o = Mod(1, K21);
red(g) = lift(o * g);
\\ odd primes != 7 of a rational number, complete factorization (the cofactor above 10^7 is tested for primality)
oddprimes(r) = {
  my(L = List(), n = abs(numerator(r)) * denominator(r), fa, co);
  if (n == 0, return([]));
  fa = factor(n, 10^7);
  for (i = 1, #fa~, my(pp = fa[i, 1]);
    if (pp > 10^7 && !isprime(pp), error("unfactored cofactor ", pp));
    if (pp % 2 && pp != 7, listput(L, pp)));
  Vec(L);
}
vpr(x, pr) = if (x == 0, "inf", idealval(nf, x, pr));
{
  for (k = 0, 1,
    my(F = if (k == 0, F0, F1), fr = polrecip(F), lc = pollead(fr, t), fa = nffactor(nf, fr), q, h, cands = List());
    q = fa[1, 1]; h = fa[2, 1];
    print("twist ", k, ": deg q = ", poldegree(q, t), ", deg h = ", poldegree(h, t),
          ", fRev = lc q h: ", red(fr - lc * q * h) == 0, ", lc(fRev) = F(0): ", red(lc - polcoef(F, 0, t)) == 0);
    my(Rqh = red(polresultant(o * q, o * h, t)), dq = red(poldisc(o * q)), dh = red(poldisc(o * h)), dfr = red(poldisc(o * fr)),
       lcF = pollead(F, t));
    my(named = [["lc(fRev)", lc], ["lc(F)", lcF], ["disc(fRev)", dfr], ["Res(q,h)", Rqh], ["disc(q)", dq], ["disc(h)", dh]]);
    foreach(named, nd, my(ps = oddprimes(norm(o * nd[2])));
      print("  odd primes != 7 of N(", nd[1], "): ", ps); foreach(ps, pp, listput(cands, pp)));
    my(dens = lcm(apply(cc -> denominator(content(lift(o * cc))), Vec(fr))));
    print("  lcm of the coefficient denominators of fRev: ", factor(dens));
    foreach(oddprimes(dens), pp, listput(cands, pp));
    cands = Set(Vec(cands));
    foreach(cands, pp,
      foreach(idealprimedec(nf, pp), pr,
        my(vl = vpr(lc, pr), vlF = vpr(lcF, pr), vd = vpr(dfr, pr), vR = vpr(Rqh, pr), vq = vpr(dq, pr), vh = vpr(dh, pr),
           vint = vecmin(apply(cc -> if (cc == 0, 10^6, idealval(nf, cc, pr)), Vec(fr))));
        if (vl == 0 && vd == 0 && vint >= 0 && vlF == 0, next);
        my(modpr = nfmodprinit(nf, pr), frb, fab, Fb);
        frb = if (vint >= 0, Pol(apply(cc -> nfmodpr(nf, cc, modpr), Vec(fr)), 't), "not integral");
        printf("  pr above %d (f = %d, e = %d): v(lc fRev) = %s, v(lc F) = %s, v(disc) = %s, min v(coeff fRev) = %d, v(Res(q,h)) = %s, v(disc q) = %s, v(disc h) = %s\n",
               pp, pr.f, pr.e, vl, vlF, vd, vint, vR, vq, vh);
        if (vint >= 0, print("     fRev mod pr = ", factor(frb)));
        \\ the three hypotheses of the lemma at the primes of F_q, F_h above pr: f integral, lc unit, f'(theta) unit
        \\ f'(theta) is a unit at every prime above pr of both factor fields iff v_pr(disc) = 0 given the other two;
        \\ printed separately for the record
        print("     hypotheses on fRev at pr: integral ", vint >= 0, ", lc unit ", vl == 0, ", disc unit (so f'(theta) units) ", vd == 0);
        print("     hypotheses on F at pr: integral ", vecmin(apply(cc -> if (cc == 0, 10^6, idealval(nf, cc, pr)), Vec(F))) >= 0,
              ", lc unit ", vlF == 0, ", disc unit ", vd == 0))));
}
quit;
