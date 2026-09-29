\\ valuation_certs_w12_w6.gp: valuation certificates of 2 at w2 (e = 12) and w3 (e = 6)
\\ for AdicPlace.lean, in the coordinates of PARI's integral basis nfinit(K21).zk (M1's zkNum / Dz, equal to
\\ M2's WL / DD, AdicPlace.lean `elt_eq_zkO`). For w = (al) with v_w(2) = e: a with al^e * a = 2 and
\\ c with a = 1 + al * c (the residue field is F_2, so a is 1 modulo al). Lean checks
\\ al^e * a - 2 = 0 and a - (1 + al * c) = 0 by M1's checkK; nothing here is trusted beyond the data.
\\ The place above 7 needs no data: M2's 7 = eps7 * al7^7 with eps7 * eps7i = 1 is used.
\\ Run: gp -q valuation_certs_w12_w6.gp < /dev/null > valuation_certs_w12_w6.out
K21 = b^21 - 7*b^20 + 14*b^19 - 84*b^16 + 98*b^15 + 2*b^14 + 175*b^13 - 609*b^12 + 980*b^11 - 770*b^10 - 280*b^9 + 1008*b^8 - 1072*b^7 + 560*b^6 + 28*b^5 - 336*b^4 + 252*b^3 - 112*b^2 + 28*b - 4;
nf = nfinit(subst(K21, b, x));
NF = 0;
chk(c, m) = if (!c, NF++; print("CHECK FAILED: ", m), print("ok: ", m));
al2 = [-2, 2, 0, 1, 0, -2, 1, -1, 0, 2, 0, 1, 2, -1, 0, 2, 1, -1, 0, 1, -1]~;
al3 = [1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]~;
one = vectorv(21, i, i == 1);
chk(nf.zk[1] == 1, "zk[1] = 1");
chk(idealnorm(nf, al2) == 2 && idealnorm(nf, al3) == 2, "N(al2) = N(al3) = 2");
lst(v) = Str(Vec(v));
integral(v) = denominator(content(v)) == 1;
cert(name, al, e) = {
  my(dec = idealprimedec(nf, 2), P, a, c);
  my(js = select(pr -> idealval(nf, al, pr) > 0, dec));
  chk(#js == 1 && idealval(nf, al, js[1]) == 1, Str(name, ": al lies in exactly one prime above 2, to the first power"));
  P = js[1];
  chk(idealval(nf, 2, P) == e, Str(name, ": v(2) = ", e));
  a = nfeltdiv(nf, 2 * one, nfeltpow(nf, al, e));
  chk(integral(a), Str(name, ": a = 2 / al^e is integral"));
  chk(nfeltmul(nf, nfeltpow(nf, al, e), a) == 2 * one, Str(name, ": al^e * a = 2"));
  c = nfeltdiv(nf, a - one, al);
  chk(integral(c), Str(name, ": c = (a - 1) / al is integral"));
  chk(a == one + nfeltmul(nf, al, c), Str(name, ": a = 1 + al * c"));
  printf("%s a = %s\n%s c = %s\n", name, lst(a), name, lst(c));
}
cert("w2", al2, 12);
cert("w3", al3, 6);
printf("DONE, %d failed checks\n", NF);
