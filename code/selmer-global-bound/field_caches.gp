\\ field_caches.gp: rebuilds the field and place caches of p21_29 that sb_5a and
\\ sb_5e read, with the code of the Prym pipeline itself (same inputs, same functions, same order of calls):
\\   nfN = nfinit([PN, [2, 3, 7, 439, 253447]]) and faL = nffactor(nfN, Lpol) as sunits_n84.gp,
\\   [nfK, nfL, nfN, aL, thL, aN, thN] = sel_fields() and the places sel_places(sel_alg(., 0)) of prym_two_descent_lib.gp.
\\ Cache directory /tmp/sb5 (sel/fields.bin, sel/places.bin, nr/nfN.bin, nr/faL_N.bin), not the shared /tmp/k21c.
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/field_caches.gp < /dev/null > ../selmer-global-bound/field_caches.out 2>&1
default(parisizemax, 1700 * 10^6); default(nbthreads, 1); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp"); read("field_l42_polynomial.gp"); read("field_n84_polynomial.gp");
read("../lib/richelot.gp"); read("../lib/td2loc.gp");
read("norm_relation_lib.gp"); read("prym_two_descent_lib.gp");
DIR = "/tmp/sb5/nr/"; SEL = "/tmp/sb5/sel/";
main() = {
  my(t0 = getabstime(), PNy = subst(PN, t, y), nfN, fa, FF, A, PL);
  system(Str("mkdir -p ", DIR, " ", SEL));
  if (fexists(Str(DIR, "nfN.bin")), nfN = read(Str(DIR, "nfN.bin")),
    nfN = nfinit([PNy, [2, 3, 7, 439, 253447]]); wbin(Str(DIR, "nfN.bin"), nfN));
  chk(nfN.pol == PNy && nfN.sign == [6, 39], "nf of N (degree 84, signature [6, 39]), as p21_25");
  printf("nfN: %d ms\n", getabstime() - t0);
  if (fexists(Str(DIR, "faL_N.bin")), fa = read(Str(DIR, "faL_N.bin")),
    fa = nffactor(nfN, subst(subst(Lpol, u, y), y, x)); wbin(Str(DIR, "faL_N.bin"), fa));
  printf("faL = nffactor(nfN, Lpol): factor degrees %s (%d ms)\n", apply(poldegree, Vec(fa[, 1])), getabstime() - t0);
  FF = sel_fields();
  chk(abs(FF[2].disc) == 2^48 * 7^54 && abs(FF[3].disc) == 2^96 * 7^111, "|disc nfL| = 2^48 7^54, |disc nfN| = 2^96 7^111");
  printf("fields: %d ms\n", getabstime() - t0);
  A = sel_alg(FF, 0);
  PL = sel_places(A);
  printf("places: %d finite, %d real (%d ms)\n", #PL[1], #PL[2], getabstime() - t0);
  printf("DONE field_caches (%d ms)\n", getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
