\\ class_number_zimmert_satz2.gp (referee): independent unconditional proof of h(K21) = 1 through Zimmert's Satz 2.
\\
\\ Zimmert (Invent. Math. 62 (1981), Satz 2, transcribed and tested against his Table 1 in zimmert_bounds.gp): every ideal
\\ class of a number field of degree n = r1 + 2 r2 and discriminant d contains an integral ideal a with, for all gamma > alpha > 0,
\\   log(|d|^(1/2) / N a) >= S2(gamma, alpha).
\\ So every class contains an integral ideal of norm <= BZ = |d|^(1/2) exp(-S2(gamma, alpha)) for any fixed admissible pair.
\\ Such an ideal is a product of prime ideals of norm <= BZ. If each of them is principal, h = 1. No twin class, no different.
\\ (The twin version, Korollar 1, needs in addition the class of the different; it is checked too, as a bonus.)
\\
\\ Checks per prime ideal P (all P of norm <= BZ, from idealprimedec for every prime p <= BZ, no Dedekind shortcut):
\\   t = generator proposed by bnfisprincipal (GRH bnf, used only as an oracle);
\\   t has integral coordinates on the integral basis (t in O_K) and idealhnf(nf, t) == idealhnf(nf, P) (so (t) = P exactly);
\\   redundant: |N(t)| = N(P) and v_P(t) = 1.
\\ All checks run inside main(), so any error aborts before the final PASS line (GP 2.17.4 continues with the next
\\ top-level statement after an error).
\\ Run from code/second-implementations/class-number: gp -q class_number_zimmert_satz2.gp < /dev/null
default(parisizemax, 2*10^9); default(nbthreads, 1); default(realprecision, 80);
[t, x, y, z, X, u, w, a, s, b];
K21 = b^21 - 7*b^20 + 14*b^19 - 84*b^16 + 98*b^15 + 2*b^14 + 175*b^13 - 609*b^12 + 980*b^11 - 770*b^10 - 280*b^9 + 1008*b^8 - 1072*b^7 + 560*b^6 + 28*b^5 - 336*b^4 + 252*b^3 - 112*b^2 + 28*b - 4;
KOWN = K21;
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
S2(r1, r2, g, al) = r1 * (-psi((1+g)/2) - lngamma(1/2+g) + lngamma(1+g) + log(Pi)/2) + r2 * (-2*psi(1+g) + 2*log(2) + log(1/2+g) + log(Pi)) - 2/(g-al) - log((1 + 1/al) * (1 + 1/g)^(-2) * (1 + 1/(2*g-al))^(-1));

certP(nf, bnf, P) = {
  my(g = bnfisprincipal(bnf, P, 1), tt, NP = P.p^P.f);
  if (#g[1] && g[1] != 0, error("nontrivial class (GRH bnf) at ", [P.p, P.f]));
  tt = g[2];
  if (type(tt) != "t_COL" || #tt != poldegree(nf.pol), error("no generator returned at ", [P.p, P.f]));
  for (i = 1, #tt, if (type(tt[i]) != "t_INT", error("generator not integral at ", [P.p, P.f])));
  if (idealhnf(nf, tt) != idealhnf(nf, P), error("(t) != P at ", [P.p, P.f]));
  if (abs(nfeltnorm(nf, tt)) != NP || idealval(nf, tt, P) != 1, error("redundant check failed at ", [P.p, P.f]));
  1;
}

main() = {
  my(t0 = getabstime(), pd, fa, nf, bnf, D, BZ, BZt, MK, g = 45/100, al, np = 0, ni = 0, maxN = 0, diff, gd);
  \\ the polynomial is the author's
  read("../../earlier-computations/bruin_form.gp");
  if (K21 != KOWN, error("polynomial differs from bruin_form.gp"));
  pd = poldisc(KOWN); fa = factor(abs(pd));
  for (i = 1, #fa~, if (!isprime(fa[i, 1]), error("unproven prime factor of disc")));
  print("poldisc = ", fa);
  nf = nfinit(KOWN);
  chk(nfcertify(nf) == [], "maximal order certified (nfcertify)");
  D = nf.disc;
  chk(D == -2^22 * 7^27 && nf.sign == [3, 9], "disc(O_K) = -2^22 7^27, signature [3, 9]");
  chk(issquare(pd / D) && pd / D == nf.index^2, "poldisc = index^2 disc(O_K)");
  al = g - g*(g+1)/sqrt(1 + 3*g + 3*g^2);
  chk(0 < al && al < g, "0 < alpha < gamma");
  BZ = sqrt(abs(D)) * exp(-S2(3, 9, g, al));
  MK = sqrt(abs(D)) * (4/Pi)^9 * 21!/21^21;
  print("Zimmert Satz 2 at gamma = 45/100, alpha = ", al, ": BZ = ", BZ, " (Minkowski ", MK, ")");
  BZ = floor(BZ);
  setrand(20260926); bnf = bnfinit(nf, 1);
  print("GRH class group (oracle only): ", bnf.cyc);
  forprime(p = 2, BZ, np++;
    my(dec = idealprimedec(nf, p));
    if (vecsum(vector(#dec, j, dec[j].e * dec[j].f)) != 21, error("idealprimedec incomplete at ", p));
    for (j = 1, #dec, my(P = dec[j], NP = p^P.f);
      if (NP <= BZ, ni += certP(nf, bnf, P); maxN = max(maxN, NP))));
  chk(np == primepi(BZ), "every prime p <= BZ visited");
  printf("%d primes p <= %d, %d prime ideals of norm <= %d, each principal with a verified generator ((t) = P exactly)\n", np, BZ, ni, BZ);
  \\ bonus, Korollar 1: class of the different; D = product of primes above 2 and 7, each of norm <= BZ
  diff = nf.diff;
  chk(idealnorm(nf, diff) == abs(D), "N(different) = |disc|");
  gd = bnfisprincipal(bnf, diff, 1)[2];
  for (i = 1, #gd, if (type(gd[i]) != "t_INT", error("generator of the different not integral")));
  chk(idealhnf(nf, gd) == idealhnf(nf, diff), "the different is principal (verified generator)");
  printf("wall time %d s\n", (getabstime() - t0) \ 1000);
  print("RESULT PASS: h(K21) = 1 (Zimmert Satz 2 bound, no GRH)");
}
main();
quit;
