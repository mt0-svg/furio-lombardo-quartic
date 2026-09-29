\\ local_divisors_bad_combination.gp: the combination c of the x - T classes of D_1..D_7 (per twist) that neither the K_v test on
\\ N_{L/K}(x_L) nor the L_w test on N_{N/L}(x_N) excludes (local_divisors_info.gp); check that it is excluded by the full test
\\ z = x_N phi(x_L) not a square in N_w (N = K21[x]/(h) of degree 84, w the prime above pr; phi : L -> N).
\\ Run: gp -q local_divisors_bad_combination.gp
default(parisizemax, 7*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
DIR = "../earlier-computations/";
read(Str(DIR, "bruin_form.gp")); read(Str(DIR, "richelot_data.gp"));
FF = read("/tmp/k21c/sel/fields.bin");
nfK = FF[1]; nfL = FF[2]; nfN = FF[3]; aL = FF[4]; thL = FF[5]; aN = FF[6]; thN = FF[7];
pr = [q | q <- idealprimedec(nfK, 2), q.e == 3][1];
red(g) = lift(Mod(1, K21) * g);
toL(e) = { my(l = lift(Mod(e, K21))); if (type(l) == "t_POL", Mod(subst(l, b, lift(aL)), nfL.pol), Mod(l, nfL.pol)); }
toN(e) = { my(l = lift(Mod(e, K21))); if (type(l) == "t_POL", Mod(subst(l, b, lift(aN)), nfN.pol), Mod(l, nfN.pol)); }
polL(P) = Pol(apply(c -> toL(c), Vec(P)), 'x);
gen2L = toL(nfbasistoalg(nfK, pr.gen[2])); gen2N = toN(nfbasistoalg(nfK, pr.gen[2]));
PL = [P | P <- idealprimedec(nfL, 2), idealval(nfL, idealadd(nfL, 2, lift(gen2L)), P) > 0];
printf("primes of L above pr: %d, (e, f) = %s\n", #PL, apply(P -> [P.e, P.f], PL));
isqK(a) = nfislocalpower(nfK, pr, a, 2);
isqL(a) = nfislocalpower(nfL, PL[1], lift(a), 2);
\\ primes of N above 2 and above pr
PN2 = idealprimedec(nfN, 2);
printf("primes of N above 2: %s\n", apply(P -> [P.e, P.f, idealval(nfN, lift(gen2N), P)], PN2));
PN = [P | P <- PN2, idealval(nfN, idealadd(nfN, 2, lift(gen2N)), P) > 0];
printf("primes of N above pr: %d\n", #PN);
isqN(a) = nfislocalpower(nfN, PN[1], lift(a), 2);
\\ an embedding L -> N: a root of Lpol in N compatible with b (aL -> aN)
{
  my(rts = nfroots(nfN, subst(nfL.pol, variable(nfL.pol), 'x)), emb = 0);
  foreach (rts, r0, if (subst(lift(aL), variable(nfL.pol), Mod(r0, nfN.pol)) == aN, emb = Mod(r0, nfN.pol); break));
  chq = emb != 0; if (!chq, error("no compatible embedding L -> N"));
  EMB = emb;
}
LtoN(e) = subst(lift(e), variable(nfL.pol), EMB);
{
  for (k = 0, 1,
    my(R = read(Str(DIR, "local_images_twist", k, "_e3.bin")), Dv = R[7], RI = RIN[k + 1], G1 = subst(RI[2], t, 'x), A = subst(RI[3], t, 'x),
       B = subst(RI[4], t, 'x), dd = RI[5], G1m, sdL, G2m, al = vector(7), be = vector(7), xL = vector(7), xN = vector(7), thLx);
    G1m = red(G1 / pollead(G1));
    sdL = nfroots(nfL, 'x^2 - lift(toL(dd))); sdL = Mod(sdL[1], nfL.pol);
    G2m = polL(A) - sdL * polL(B); G2m = G2m / pollead(G2m);
    \\ a root of G1 in L and a root of h in N; theta_L -> N must be a root of G1 in N compatible with the chosen phi
    for (i = 1, 7, my(uu = Dv[i][1]);
      al[i] = red(polresultant(Mod(1, K21) * G1m, Mod(1, K21) * uu, 'x));
      be[i] = polresultant(G2m, polL(uu), 'x);
      xL[i] = subst(Pol(apply(c -> toL(c), Vec(uu)), 'x), 'x, thL);
      xN[i] = subst(Pol(apply(c -> toN(c), Vec(uu)), 'x), 'x, thN));
    printf("---- twist %d\n", k);
    forvec (c = vector(7, j, [0, 1]), if (c != 0,
      my(ap = red(prod(j = 1, 7, al[j]^c[j])), bp = prod(j = 1, 7, be[j]^c[j]), sa = isqK(ap), sb = isqL(bp));
      if (sa && sb,
        my(zL = prod(j = 1, 7, xL[j]^c[j]), zN = prod(j = 1, 7, xN[j]^c[j]), zz = zN * LtoN(zL), sq1 = isqN(zz), sq2 = isqN(zN));
        printf("  bad combination %s: z = x_N phi(x_L) square in N_w: %d (x_N alone: %d)\n", c, sq1, sq2)))));
}
quit;
