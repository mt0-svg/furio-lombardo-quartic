\\ abel_prym_sizes.gp: sizes of the certificate data of the swapped Bruin construction at the known lifts, for a few
\\ normalizations of the tangent vector T (T_z = 0, then scaled). Exploration only.
\\ Run from code/genus2-curves: gp -q abel_prym_sizes.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/abel_prym_lib.gp");
red(g) = lift(Mod(1, K21) * g);
den(v) = denominator(content(v));
mx(v) = vecmax(apply(e -> abs(e), concat([0], Vec(v))));
sz(e) = { my(v = zkc(e)); [den(v), #Str(mx(den(v) * v))] };
Pts = [[0, 0, 1], [1, 1, 1], [2, 0, 1], [-1, 0, 1]];
dd = [Mod(d0, K21), Mod(d1, K21)];
Ev(Q, P) = Mod(substvec(Q, [x, y, z], P), K21);
{ for (i = 1, 4,
    my(P0 = Pts[i], k = if (i == 1 || i == 3, 1, 2), dl = dd[k], v = vector(3, j, Ev(Qs[j], P0)), r, s, P2, S2, Jm, K, T, c, a);
    if (v[1] != 0,
      r = nfroots(nf, 'X^2 - lift(v[1] / dl)); r = Mod(r[1], K21); s = v[2] / (dl * r),
      r = Mod(0, K21); s = nfroots(nf, 'X^2 - lift(v[3] / dl)); s = Mod(s[1], K21));
    P2 = concat(P0 * Mod(1, K21), [s, r]);
    S2 = apm_init(Q3 * Mod(1, K21), Q2 * Mod(1, K21), Q1 * Mod(1, K21), dl);
    printf("x%d: P' coordinates sizes %s\n", i - 1, apply(sz, P2));
    Jm = matrix(3, 5, ii, jj, (S2[3 + ii] * P2~)[jj]);
    K = matker(Jm);
    T = K[, 1]~; if (T[3] == 0 && matrank(Mat([P2~, T~])) < 2, T = K[, 2]~);
    T = T - T[3] / P2[3] * P2;
    if (T == 0, T = K[, 2]~; T = T - T[3] / P2[3] * P2);
    printf("  T (T_z = 0) raw: %s\n", apply(sz, T));
    for (j = 1, 5, if (T[j] != 0, c = T[j]; break));
    printf("  T / first nonzero: %s\n", apply(sz, T / c));
    my(T1 = T / c, dn = lcm(apply(e -> den(zkc(e)), T1)));
    printf("  T integral (lcm denominators %s): %s\n", dn, apply(sz, dn * T1));
    a = vector(3, j, T1 * S2[3 + j] * T1~);
    printf("  a_i for T / first: %s\n", apply(sz, a));
    printf("  jacobian columns of P' (3x5) sizes: %s\n", apply(e -> sz(e)[2], Jm));
  );
}
quit;
