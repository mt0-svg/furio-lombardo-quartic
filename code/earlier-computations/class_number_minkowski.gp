\\ class_number_minkowski.gp: unconditional proof that the class number of K21 is 1, by explicit principal generators.
\\
\\ Statement. Every ideal class of O_K (K = K21) contains an integral ideal of norm <= M_K, the Minkowski bound
\\ M_K = sqrt|D| (4/pi)^r2 n!/n^n (n = 21, r2 = 9). Such an ideal is a product of prime ideals of norm <= M_K. So if
\\ every prime ideal P with N(P) <= M_K is principal, then h(K) = 1.
\\ Certificate per prime ideal P: an element t of O_K with t in P and |N(t)| = N(P); then (t) is contained in P and
\\ has the same norm, so (t) = P. The generator t is found by bnfisprincipal (which uses the GRH-conditional bnf), but
\\ the two checks are exact and unconditional, so GRH plays no role in the conclusion.
\\ Inputs checked here: the maximal order (nfcertify, unconditional), disc(O_K) = -2^22 7^27, signature [3, 9].
\\ Prime ideals: for p not dividing disc(K21 polynomial) (the index of Z[b] and disc(O_K)), the degree one primes
\\ above p are (p, b - r) for the roots r of K21 mod p (Dedekind); primes of degree >= 2 have norm p^f <= M_K only for
\\ p <= sqrt(M_K); for those p, and for p dividing the polynomial discriminant, the full idealprimedec is used.
\\
\\ Run from code/earlier-computations, one range of primes (LO, HI] per job (environment variables), NT threads:
\\   LO=0 HI=4100000 gp -q class_number_minkowski.gp < /dev/null   (all ranges: sh class_number_minkowski_run.sh)
\\ HI larger than M_K is clipped to floor(M_K).
default(parisizemax, 10^9); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
K21 = b^21 - 7*b^20 + 14*b^19 - 84*b^16 + 98*b^15 + 2*b^14 + 175*b^13 - 609*b^12 + 980*b^11 - 770*b^10 - 280*b^9 + 1008*b^8 - 1072*b^7 + 560*b^6 + 28*b^5 - 336*b^4 + 252*b^3 - 112*b^2 + 28*b - 4;
LO = eval(getenv("LO")); HI = eval(getenv("HI"));   \\ the installed GP has the single threading engine: parallelism is by separate processes on disjoint ranges (class_number_minkowski_run.sh)
default(nbthreads, 1);
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
\\ certify one prime ideal given by its HNF P, of norm NP; r = root (degree one case) or 0 with pr = prid.
\\ Checks: t has integral coordinates on the integral basis (t in O_K), |N(t)| = N(P), t in P. Then (t) = P.
cert1(P, NP, r, pr) = {
  my(g = bnfisprincipal(bnf, P, 1), tb, al);
  if (#g[1] != 0, error("nontrivial class at ", P));
  tb = g[2]; if (type(tb) != "t_COL", tb = nfalgtobasis(nf, tb));
  if (#tb != 21, error("generator of wrong size at ", P));
  for (i = 1, 21, if (type(tb[i]) != "t_INT", error("generator not integral at ", P)));
  al = nfbasistoalg(nf, tb);
  if (abs(norm(al)) != NP, error("norm of generator at ", P));
  if (pr == 0,
    if (subst(lift(al), 'b, Mod(r, NP)) != 0, error("generator not in P at ", P)),
    if (idealval(nf, tb, pr) < 1, error("generator not in P at ", P)));
  1;
}
\\ all prime ideals of norm <= B above primes in (lo, hi]; returns [#primes, #prime ideals certified]
block(lo, hi) = {
  my(np = 0, ni = 0);
  forprime(p = lo + 1, hi,
    np++;
    if (p <= SQ || setsearch(BAD, p),
      my(dec = idealprimedec(nf, p), sef = 0);
      for (j = 1, #dec, sef += dec[j].e * dec[j].f);
      if (sef != 21, error("idealprimedec incomplete at ", p));
      for (j = 1, #dec, my(pr = dec[j], NP = p^pr.f);
        if (NP <= B, ni += cert1(idealhnf(nf, pr), NP, 0, pr))),
      my(rts = polrootsmod(K21, p));
      for (i = 1, #rts, my(r = lift(rts[i]));
        ni += cert1(idealhnf(nf, p, 'b - r), p, r, 0))));
  [np, ni];
}
\\ everything inside one function: GP 2.17.4 keeps executing top-level statements after an error, so no check may
\\ live at top level; any error here aborts main before the RESULT line.
main() = {
  my(t0, STEP = 50000, lo = LO, hi, nb, res, tot = [0, 0], MK, pdisc);
  nf = nfinit(K21);
  chk(nfcertify(nf) == [], "maximal order certified (nfcertify, no GRH)");
  chk(nf.disc == -2^22 * 7^27 && nf.sign == [3, 9], "disc(O_K) = -2^22 7^27, signature [3, 9]");
  MK = sqrt(abs(nf.disc)) * (4 / Pi)^9 * 21! / 21^21;
  B = floor(MK);
  print("Minkowski bound M_K = ", MK, ", B = floor(M_K) = ", B);
  hi = min(HI, B);
  bnf = bnfinit(nf, 1);
  chk(bnf.cyc == [], "class group trivial under GRH (only used to find generators)");
  pdisc = abs(poldisc(K21));
  BAD = Set(factor(pdisc)[, 1]~);   \\ pdisc = index^2 |disc(O_K)|
  chk(pdisc % abs(nf.disc) == 0 && issquare(pdisc / abs(nf.disc)) && vecprod(apply(q -> isprime(q), BAD)) == 1, "polynomial discriminant = index^2 |disc(O_K)|, prime divisors proven prime");
  print("primes dividing the polynomial discriminant: ", BAD);
  SQ = sqrtint(B);
  t0 = getabstime();
  nb = ceil((hi - lo) / STEP);
  res = vector(nb, k, block(lo + (k - 1) * STEP, min(lo + k * STEP, hi)));
  for (k = 1, nb, tot += res[k]);
  printf("range (%d, %d]: %d primes, %d prime ideals of norm <= B, each principal with a verified integral generator (%d s wall)\n", lo, hi, tot[1], tot[2], (getabstime() - t0) \ 1000);
  chk(tot[1] == primepi(hi) - primepi(lo), "every prime of the range visited");
  print("RESULT PASS");
}
main();
quit;
