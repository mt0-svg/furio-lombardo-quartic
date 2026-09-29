\\ field_n84.gp: feasibility of the global part of a full 2-descent over K21. The etale
\\ algebra of F_0 : Y^2 = c G1 h (h = A^2 - d B^2 quartic over K21) is M x N with M = K21[t]/(G1) (degree 42) and
\\ N = K21[t]/(h) (degree 84, a quadratic extension of L = K21(sqrt d)). This script builds absolute polynomials for
\\ M and N, reduces them, and times nfinit and bnfinit (GRH) on N, printing progress, to decide whether N(S,2) can
\\ come from a GRH bnf (then made unconditional by an ambiguous class argument over L and independence mod squares).
\\ Run from code/earlier-computations: gp -q field_n84.gp < /dev/null
default(parisizemax, 7*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
read("richelot_data.gp");
main() = {
  my(t0 = getabstime(), nfK = nfinit([K21, [2, 7]]), R = RIN[1], G1 = R[2], A = R[3], B = R[4], d = R[5], h, eqN, eqM, PN, PM, nfN, bnfN);
  h = lift(Mod(A^2 - d * B^2, K21));
  printf("h: degree %d in t; G1 degree %d\n", poldegree(h, t), poldegree(G1, t));
  eqM = rnfequation(nfK, G1); eqN = rnfequation(nfK, h);
  printf("rnfequation: M degree %d, N degree %d (%d ms)\n", poldegree(eqM), poldegree(eqN), getabstime() - t0);
  PN = polredbest(eqN); printf("polredbest(N): %d ms, max log10 coefficient %d\n", getabstime() - t0, round(log(vecmax(apply(abs, Vec(PN))))/log(10)));
  write("/tmp/k21c/n84/PN.gp", "PN = ", PN, ";");
  PM = polredbest(eqM); write("/tmp/k21c/n84/PM.gp", "PM = ", PM, ";");
  nfN = nfinit([PN, [2, 3, 7, 439, 253447]]);
  printf("nfinit(N) with partial factorisation: %d ms, signature %s, disc 2^%d 7^%d, other primes of disc: %s\n", getabstime() - t0, nfN.sign, valuation(nfN.disc, 2), valuation(nfN.disc, 7), factor(nfN.disc / 2^valuation(nfN.disc, 2) / 7^valuation(nfN.disc, 7), 10^6));
  bnfN = bnfinit(nfN, 1);
  printf("bnfinit(N) (GRH): %d ms, class group %s\n", getabstime() - t0, bnfN.cyc);
  writebin("/tmp/k21c/n84/bnfN.bin", bnfN);
  print("DONE");
}
main();
quit;
