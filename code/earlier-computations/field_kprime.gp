\\ field_kprime.gp: the field K' = K21(sqrt(lam0)) over which the order 4 automorphism r of the 21-orbit Prym
\\ is defined: lam0 reduced to a unit mod squares, absolute polynomial of K' (maximal order certified by the
\\ discriminant: only 2 and 7), primes above 2 and 7, splitting of the quartic factor h of F0 over K'.
\\ Writes field_kprime_data.gp.  Run from code/earlier-computations: gp -q field_kprime.gp < /dev/null
default(parisizemax, 6*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b, c];
read("bruin_form.gp");
read("prym_involution_data.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
bnf21 = bnfinit(K21, 1); nf21 = bnf21.nf;
print("K21: disc ", factor(nf21.disc), ", signature ", nf21.sign, ", class group ", bnf21.cyc, " (GRH)");
\\ lam0 = unit * square
{
  my(fa = idealfactor(nf21, lam0), I = 1, g, uu, ex);
  for (i = 1, #fa~, if (fa[i,2] % 2, error("lam0 has an odd valuation")); I = idealmul(nf21, I, idealpow(nf21, fa[i,1], fa[i,2] / 2)));
  g = bnfisprincipal(bnf21, I, 3); chk(g[1] == vector(#g[1], i, 0)~, "square root ideal of (lam0) principal");
  g = nfbasistoalg(nf21, g[2]);
  uu = lam0 / g^2;
  ex = bnfisunit(bnf21, uu); chk(#ex > 0, "lam0 / g^2 is a unit");
  e0 = prod(i = 1, #bnf21.fu, bnf21.fu[i]^(ex[i] % 2)) * bnf21.tu[2]^(ex[#ex] % 2);
  chk(#nfroots(nf21, t^2 - lift(lam0 / e0)) > 0, "lam0 / e0 is a square");
}
print("e0 = lam0 mod squares (unit): exponent vector mod 2 computed; e0 = ", lift(e0));
rq = rnfequation(nf21, t^2 - lift(e0), 1);
pol = rq[1]; print("absolute degree ", poldegree(pol));
nf42 = nfinit([pol, [2, 7]]);
{
  my(d = abs(nf42.disc)); d = d / 2^valuation(d, 2); d = d / 7^valuation(d, 7);
  chk(d == 1, "order maximal at 2 and 7 has discriminant 2^a 7^b, hence it is the maximal order");
}
print("K': disc ", factor(nf42.disc), ", signature ", nf42.sign);
T = getabstime(); pb = polredbest(nf42, 1); print("polredbest time ", getabstime() - T, " ms");
KpC = subst(pb[1], t, c);
b_in = Mod(subst(lift(subst(lift(rq[2]), t, Mod(lift(pb[2]), pb[1]))), t, c), KpC);   \\ Horner in Q[t]/(new polynomial)
chk(subst(K21, b, b_in) == 0, "K21 embeds into K' (root of K21 expressed in K')");
toKp(e) = subst(lift(Mod(e, K21)), b, b_in);
nfp = nfinit([KpC, [2, 7]]);
{
  my(d = abs(nfp.disc)); d = d / 2^valuation(d, 2); d = d / 7^valuation(d, 7);
  chk(d == 1, "maximal order of K' (reduced polynomial) certified by the discriminant");
}
chk(#nfroots(nfp, t^2 - lift(toKp(lam0))) > 0, "lam0 is a square in K'");
print("primes above 2 in K': ", apply(pr -> [pr.e, pr.f], idealprimedec(nfp, 2)));
print("primes above 7 in K': ", apply(pr -> [pr.e, pr.f], idealprimedec(nfp, 7)));
print("primes above 2 in K21: ", apply(pr -> [pr.e, pr.f], idealprimedec(nf21, 2)));
print("primes above 7 in K21: ", apply(pr -> [pr.e, pr.f], idealprimedec(nf21, 7)));
\\ quartic factor h of F0 over K'
hK = sum(i = 0, 4, lift(toKp(polcoef(lift(h0), i, t))) * t^i);
fh = nffactor(nfp, lift(hK));
print("h0 over K': factor degrees ", vector(#fh~, i, poldegree(fh[i,1])));
fn = "field_kprime_data.gp"; system(Str("rm -f ", fn));
write(fn, "\\\\ field_kprime.gp output: K' = Q[c]/(KpC) = K21(sqrt(e0)), e0 = lam0 mod squares; b_in = image of b");
write(fn, "KpC = ", KpC, ";");
write(fn, "e0 = ", lift(e0), ";");
write(fn, "b_in = ", lift(b_in), ";");
quit;
