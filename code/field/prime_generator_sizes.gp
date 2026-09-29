\\ prime_generator_sizes.gp: sizes of generator coordinates (zk basis) for a sample of prime ideals below the Zimmert bound.
default(parisizemax, 4*10^9); default(nbthreads, 1);
f = x^21 - 7*x^20 + 14*x^19 - 84*x^16 + 98*x^15 + 2*x^14 + 175*x^13 - 609*x^12 + 980*x^11 - 770*x^10 - 280*x^9 + 1008*x^8 - 1072*x^7 + 560*x^6 + 28*x^5 - 336*x^4 + 252*x^3 - 112*x^2 + 28*x - 4;
bnf = read("field_bnf.bin");
nf = bnf.nf; B = 100618;
dig(v) = if (v == 0, 0, #Str(abs(v)));
maxdig(col) = vecmax(apply(dig, col));
probe(lo, hi) = {
  my(cnt = 0, mA = 0, mC = 0, t0 = getwalltime());
  forprime(p = lo, hi,
    my(dec = idealprimedec(nf, p));
    for (j = 1, #dec, my(pr = dec[j], g, a, c);
      if (p^pr.f > B, next);
      g = bnfisprincipal(bnf, pr, 1); a = g[2];
      c = nfeltdiv(nf, p, a);
      if (denominator(c) != 1, error("c"));
      cnt++; mA = max(mA, maxdig(a)); mC = max(mC, maxdig(c))));
  print("[", lo, ",", hi, "] count ", cnt, " max digits a ", mA, " c ", mC, " time ", getwalltime() - t0);
}
probe(3, 2000);
probe(99000, 100618);
quit
