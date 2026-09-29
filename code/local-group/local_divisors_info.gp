\\ local_divisors_info.gp: the local divisors D_1..D_7 of M4's basis (code/earlier-computations/local_images_twist<k>_e3.bin: u_i, v_i in
\\ K21[x], original model; V_i is the square root of f modulo u_i near v_i over K_v) on the reversed model of the
\\ M3a discharge (fRev = t^6 f(1/t), u^rev = t^2 u(1/t) / u(0), v^rev = t^3 v(1/t) mod u^rev), and a cheap
\\ criterion for the independence of their x - T classes in H(f_v) = L_v^x / K_v^x L_v^x2.
\\ Psi(x) = (N_{L/K}(x_L) mod K_v^x2, N_{N/L}(x_N) mod L_w^x2), L = K21[x]/(G1) = K21(sqrt d), N = K21[x]/(h) contains
\\ L, h = lc G2 G2bar over L with G2 = A - sqrt(d) B. Psi kills K_v^x and L_v^x2; for x = u(T): N_{L/K}(u(theta_L)) =
\\ Res(G1m, u) and N_{N/L}(u(theta_N)) = Res(G2m, u) (G1m, G2m monic). If span(d_i) meets ker Psi only in 0, the
\\ independence reduces to square tests in K_v and in L_w (degree 6 over Q_2).
\\ Run: gp -q local_divisors_info.gp
default(parisizemax, 5*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
DIR = "../earlier-computations/";
read(Str(DIR, "bruin_form.gp")); read(Str(DIR, "richelot_data.gp"));
FF = read("/tmp/k21c/sel/fields.bin");
nfK = FF[1]; nfL = FF[2]; aL = FF[4];
pr = [q | q <- idealprimedec(nfK, 2), q.e == 3][1];
red(g) = lift(Mod(1, K21) * g);
toL(e) = { my(l = lift(Mod(e, K21))); if (type(l) == "t_POL", Mod(subst(l, b, lift(aL)), nfL.pol), Mod(l, nfL.pol)); }
polL(P) = Pol(apply(c -> toL(c), Vec(P)), 'x);
\\ primes of L above pr
gen2L = toL(nfbasistoalg(nfK, pr.gen[2]));
PL = [P | P <- idealprimedec(nfL, 2), idealval(nfL, idealadd(nfL, 2, lift(gen2L)), P) > 0];
printf("primes of L above pr: %d (e, f): %s\n", #PL, apply(P -> [P.e, P.f], PL));
isqK(a) = nfislocalpower(nfK, pr, a, 2);
isqL(a) = nfislocalpower(nfL, PL[1], lift(a), 2);
zksize(e) = { my(v = nfalgtobasis(nfK, lift(Mod(e, K21)))); [denominator(content(v)), exponent(v * denominator(content(v)))]; }
{
  for (k = 0, 1,
    my(R = read(Str(DIR, "local_images_twist", k, "_e3.bin")), Dv = R[7], RI = RIN[k + 1], G1 = subst(RI[2], t, 'x), A = subst(RI[3], t, 'x),
       B = subst(RI[4], t, 'x), dd = RI[5], f = subst(if (k == 0, F0, F1), t, 'x), fr = red(polrecip(subst(f, 'x, t))), G1m, sdL, G2m,
       al = vector(7), be = vector(7), bad = 0, nker = 0);
    G1m = red(G1 / pollead(G1));
    sdL = nfroots(nfL, 'x^2 - lift(toL(dd))); if (#sdL != 2, error("sqrt d in L")); sdL = Mod(sdL[1], nfL.pol);
    G2m = polL(A) - sdL * polL(B); G2m = G2m / pollead(G2m);
    printf("---- twist %d\n", k);
    for (i = 1, 7,
      my(uu = Dv[i][1], vv = Dv[i][2], u0 = polcoef(uu, 0, 'x), ur, vr, rs, dsc);
      if (u0 == 0, error("u(0) = 0"));
      ur = red(polrecip(subst(uu, 'x, t)) / u0);
      vr = red(lift(Mod(Mod(1, K21) * (t^3 * subst(vv, 'x, 1/t)), Mod(1, K21) * ur)));
      rs = red(polresultant(Mod(1, K21) * ur, Mod(1, K21) * fr, t));
      dsc = red(polcoef(ur, 1, t)^2 - 4 * polcoef(ur, 0, t));
      al[i] = red(polresultant(Mod(1, K21) * G1m, Mod(1, K21) * uu, 'x));
      be[i] = polresultant(G2m, polL(uu), 'x);
      printf("  D_%d: u^rev coefficient sizes %s %s; v^rev %s %s; Res(u^rev, fRev) != 0: %d; disc u^rev local square: %d, val %d; val(u^rev coefs) %s\n",
        i, zksize(polcoef(ur, 0, t)), zksize(polcoef(ur, 1, t)), zksize(polcoef(vr, 0, t)), zksize(polcoef(vr, 1, t)), rs != 0,
        isqK(dsc), nfeltval(nfK, dsc, pr), [nfeltval(nfK, polcoef(ur, 0, t), pr), nfeltval(nfK, polcoef(ur, 1, t), pr)]));
    forvec (c = vector(7, j, [0, 1]), if (c != 0,
      my(ap = red(prod(j = 1, 7, al[j]^c[j])), bp = prod(j = 1, 7, be[j]^c[j]), sa = isqK(ap), sb = isqL(bp));
      if (sa && sb, bad++);
      if (sa, nker++)));
    printf("  combinations with N_{L/K} part a local square: %d of 127; combinations killed by neither test: %d\n", nker, bad));
}
quit;
