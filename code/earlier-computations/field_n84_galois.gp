\\ field_n84_galois.gp: the degree 84 field N inside the Galois closure M (group PGL(2,7)) of K21, and the
\\ cost of the compositum factorisations needed by the generalised norm relation for N (code/earlier-computations/norm_relation_n84.g).
\\ Group side (GAP): N = M^H with H a Klein four group outside PSL(2,7) (6 real places, unit rank 44), contained
\\ in the order 8 group fixing L = K21(sqrt(-e0)); the norm relation for N exists with respect to L and
\\ K13 = K21(sqrt(7 e0)) (fixed field of the cyclic group of order 8 in the Sylow 2-subgroup D16).
\\ Fingerprints checked here (factor degrees = orbit sizes): A3 over L: [4, 4]; A3 over N: [2, 2, 4];
\\ K21 over N: [1, 2, 2, 2, 2, 4, 4, 4]. Then times nffactor of the L and K13 polynomials over N, and bnfinit(K13).
\\ Run from code/earlier-computations: gp -q field_n84_galois.gp < /dev/null
default(parisizemax, 6*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b, c];
K21 = b^21 - 7*b^20 + 14*b^19 - 84*b^16 + 98*b^15 + 2*b^14 + 175*b^13 - 609*b^12 + 980*b^11 - 770*b^10 - 280*b^9 + 1008*b^8 - 1072*b^7 + 560*b^6 + 28*b^5 - 336*b^4 + 252*b^3 - 112*b^2 + 28*b - 4;
A3 = a^8 + 2*a^7 + 7*a^4 - 14*a^2 - 8*a + 5;
read("field_kprime_data.gp"); read("field_l42_polynomial.gp");
read("field_n84_polynomial.gp"); PNglob = PN;   \\ polredbest polynomial of N (field_n84.gp), in t
DIR = "/tmp/k21c/nr/";
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
degs(fa) = vecsort(apply(poldegree, fa[, 1]~));
main() = {
  my(t0 = getabstime(), nfK = nfinit([K21, [2, 7]]), nfL, nfN, e0b = lift(e0), P13, nf13, fa, bnf13, PN);
  nfL = nfinit([subst(Lpol, u, y), [2, 7]]);
  printf("nfinit(L): %d ms, disc 2^%d 7^%d, rest %d\n", getabstime() - t0, valuation(nfL.disc, 2), valuation(nfL.disc, 7), nfL.disc / 2^valuation(nfL.disc, 2) / 7^valuation(nfL.disc, 7));
  fa = nffactor(nfL, subst(A3, a, x)); printf("A3 over L: degrees %s (%d ms)\n", degs(fa), getabstime() - t0);
  chk(degs(fa) == [4, 4], "A3 factors as 4 + 4 over L (L is the fixed field of the order 8 class 12)");
  P13 = subst(polredbest(rnfequation(nfK, t^2 - 7 * e0b)), t, y); nf13 = nfinit([P13, [2, 7]]);
  printf("K13 = K21(sqrt(7 e0)): %d ms, signature %s, disc 2^%d 7^%d, rest %d\n", getabstime() - t0, nf13.sign, valuation(nf13.disc, 2), valuation(nf13.disc, 7), nf13.disc / 2^valuation(nf13.disc, 2) / 7^valuation(nf13.disc, 7));
  write(Str(DIR, "P13.gp"), "P13 = ", P13, ";");
  fa = nffactor(nf13, subst(A3, a, x)); printf("A3 over K13: degrees %s (%d ms)\n", degs(fa), getabstime() - t0);
  bnf13 = bnfinit(nf13, 1); printf("bnfinit(K13) (GRH): %d ms, class group %s\n", getabstime() - t0, bnf13.cyc);
  writebin(Str(DIR, "bnf13.bin"), bnf13);
  PN = subst(PNglob, t, y);
  nfN = nfinit([PN, [2, 3, 7, 439, 253447]]); printf("nfinit(N): %d ms, signature %s\n", getabstime() - t0, nfN.sign);
  writebin(Str(DIR, "nfN.bin"), nfN);
  fa = nffactor(nfN, subst(A3, a, x)); printf("A3 over N: degrees %s (%d ms)\n", degs(fa), getabstime() - t0);
  chk(degs(fa) == [2, 2, 4], "A3 factors as 2 + 2 + 4 over N (H is the class 7 Klein four group)");
  fa = nffactor(nfN, subst(K21, b, x)); printf("K21 over N: degrees %s (%d ms)\n", degs(fa), getabstime() - t0);
  chk(degs(fa) == [1, 2, 2, 2, 2, 4, 4, 4], "K21 polynomial factors as 1 + 2 2 2 2 + 4 4 4 over N");
  fa = nffactor(nfN, subst(Lpol, u, x)); printf("L over N: degrees %s (%d ms)\n", degs(fa), getabstime() - t0);
  writebin(Str(DIR, "faL_N.bin"), fa);
  fa = nffactor(nfN, subst(P13, y, x)); printf("K13 over N: degrees %s (%d ms)\n", degs(fa), getabstime() - t0);
  writebin(Str(DIR, "fa13_N.bin"), fa);
  print("DONE");
}
main();
quit;
