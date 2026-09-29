\\ local_divisors_explore.gp: exploration of the Lean construction of the local divisors D_1..D_7 (M4's basis, code/earlier-computations
\\ local_images_twist<k>_e3.bin) on the reversed model: U = t^2 + p t + r (p = u1/u0, r = 1/u0 in K21), R = fRev mod U =
\\ z1 t + z0', D = p^2/4 - r, z0 = z0' - z1 p/2, N = z0^2 - D z1^2, n = sqrt N, a = sqrt((z0 + s n)/2), b = z1/(2a),
\\ V = b t + (a + b p/2) over K_v; the sign choices that match the stored approximation v^rev = t^3 v(1/t) mod U.
\\ Prints valuations (pi units) for the precision budget of the Lean certificates.
\\ Run from code/local-group: gp -q local_divisors_explore.gp
default(parisizemax, 3*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];  \\ variable order of the p21 binaries
read("../descent/descent_data_lib.gp");
read("completion_kv_lib.gp");
dd = [d0, d1];
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
kvpol(P) = Pol(apply(c -> sg(c), Vec(P)), 't);
{
  for (k = 1, 2,
    my(f = red(-dd[k] * matdet(Msym(Qc[1]) + 2*t*Msym(Qc[2]) + t^2*Msym(Qc[3]))), fr = polrecip(f), R = read(Str("../earlier-computations/local_images_twist", k - 1, "_e3.bin")));
    printf("---- twist %d\n", k - 1);
    for (i = 1, 7,
      my(uu = subst(lift(R[7][i][1]), 'x, t), vv = subst(lift(R[7][i][2]), 'x, t), u0 = polcoef(uu, 0, t), u1 = polcoef(uu, 1, t), p, r, U, Rm, z1, z0p, D, z0, N, vr, best = [-1]);
      p = red(lift(Mod(u1, K21) / Mod(u0, K21))); r = red(lift(1 / Mod(u0, K21))); U = t^2 + p*t + r;
      chq(red(U * u0 - polrecip(uu)) == 0, "U = u^rev");
      Rm = red(lift(Mod(Mod(1, K21) * fr, Mod(1, K21) * U))); z1 = polcoef(Rm, 1, t); z0p = polcoef(Rm, 0, t);
      D = red(p^2 / 4 - r); z0 = red(z0p - z1 * p / 2); N = red(z0^2 - D * z1^2);
      vr = red(lift(Mod(Mod(1, K21) * (t^3 * subst(vv, t, 1/t)), Mod(1, K21) * U)));
      my(Nl = sg(N), n0 = ksqrt(Nl));
      foreach ([1, -1], sn, my(n = sn * n0, w = (sg(z0) + n) / 2);
        if (ksq(w), my(a0 = ksqrt(w));
          foreach ([1, -1], sa, my(a = sa * a0, bb = sg(z1) / (2 * a), V = bb * 't + (a + bb * sg(p) / 2), dv = kvpol(vr) - V, dmin);
            dmin = min(vpi(polcoef(dv, 0, 't)), vpi(polcoef(dv, 1, 't)));
            if (dmin > best[1], best = [dmin, sn, sa, vpi(n), vpi(w), vpi(a), vpi(bb)]))));
      printf("  D_%d: v(p) %d v(r) %d v(z1) %d v(z0') %d v(D) %d v(z0) %d v(N) %d; best sign (n, a) = (%d, %d), v(V - v^rev) = %d; v(n) %d v((z0+n)/2) %d v(a) %d v(b) %d; U local square disc %d; den p %d r %d\n",
        i, vl(p), vl(r), vl(z1), vl(z0p), vl(D), vl(z0), vl(N), best[2], best[3], best[1], best[4], best[5], best[6], best[7], lsq(red(p^2 - 4*r)),
        valuation(den(zkc(p)), 2), valuation(den(zkc(r)), 2))));
}
quit;
