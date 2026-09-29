\\ abel_prym_explore.gp (WP4 of the M3a discharge): Bruin's Abel-Prym map at the known lifts, original and swapped.
\\ Swapped construction: abel_prym_lib.gp applied to (Q3, Q2, Q1, delta) at (x, y, z, s, r). Claim checked here: it is the
\\ image of apm_phi(Q1, Q2, Q3, delta; x, y, z, r, s) under (t, Y) -> (1/t, Y/t^3), i.e. U' = U^rev / U(0) and
\\ V' = t^3 V(1/t) mod U', on the reversed sextic fRev = polrecip(f).
\\ Also: independence of the choice of T in the tangent line (T -> l T + m P), of the scaling of P, and
\\ phi(iota P) = (U, -V). And agreement with code/earlier-computations/phi_known_lifts.gp (the phi(x_i) used by the certified computations).
\\ Run from code/genus2-curves: gp -q abel_prym_explore.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/abel_prym_lib.gp");
read("../earlier-computations/phi_known_lifts.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
red(g) = lift(Mod(1, K21) * g);
sq21(d) = { my(rr = nfroots(nf, 'X^2 - lift(d))); if (#rr, Mod(rr[1], K21), []); };
\\ U, V from a given tangent vector T (the conjugate roots branch of apm_phi, valid whenever the entry used is a unit mod U)
phiT(S, P, T) = {
  my(a = vector(3, i, T * S[3 + i] * T~), U, Y);
  U = t^2 + 2*a[2]/a[3]*t + a[1]/a[3];
  Y = apm_ruling(S, P, T, Mod(t, U));
  [U, lift(Y)];
}
Pts = [[0, 0, 1], [1, 1, 1], [2, 0, 1], [-1, 0, 1]];
dd = [Mod(d0, K21), Mod(d1, K21)];
Ev(Q, P) = Mod(substvec(Q, [x, y, z], P), K21);
{ for (i = 1, 4,
    my(P0 = Pts[i], k = if (i == 1 || i == 3, 1, 2), dl = dd[k], v = vector(3, j, Ev(Qs[j], P0)), r, s, P, P2, S, S2, ph, ph2,
       U, V, U2, V2, Ur, Vr, T, T2, ph3, Pi, fr);
    if (v[1] != 0,
      r = nfroots(nf, 'X^2 - lift(v[1] / dl)); r = Mod(r[1], K21); s = v[2] / (dl * r),
      r = Mod(0, K21); s = nfroots(nf, 'X^2 - lift(v[3] / dl)); s = Mod(s[1], K21));
    P = concat(P0 * Mod(1, K21), [r, s]);
    P2 = concat(P0 * Mod(1, K21), [s, r]);
    S = apm_init(Q1 * Mod(1, K21), Q2 * Mod(1, K21), Q3 * Mod(1, K21), dl);
    S2 = apm_init(Q3 * Mod(1, K21), Q2 * Mod(1, K21), Q1 * Mod(1, K21), dl);
    chk(apm_ondp(S, P) && apm_ondp(S2, P2), Str("x", i - 1, " on D (original and swapped)"));
    chk(lift(P) == PHI[i][3], Str("x", i - 1, " = the lift of phi_known_lifts.gp"));
    fr = polrecip(S[8]);
    chk(S2[8] == fr, "swapped sextic = polrecip(f) (= fRev)");
    ph = apm_phi(S, P, sq21);
    chk(lift(ph[1]) == PHI[i][4] && lift(ph[2]) == PHI[i][5], Str("apm_phi(x", i - 1, ") = phi_known_lifts.gp"));
    U = ph[1]; V = ph[2];
    printf("x%d: twist %d, U(0) != 0: %d, U irreducible over K21: %d, deg V = %d\n", i - 1, k - 1, polcoef(U, 0, t) != 0,
      #nfroots(nf, lift(U)) == 0, poldegree(V, t));
    ph2 = apm_phi(S2, P2, sq21);
    U2 = ph2[1]; V2 = ph2[2];
    Ur = polrecip(U) / polcoef(U, 0, t);
    Vr = (polcoef(V, 0, t) * t^3 + polcoef(V, 1, t) * t^2) % Ur;
    chk(U2 == Ur, Str("x", i - 1, ": swapped U = reversed U"));
    chk(V2 == Vr, Str("x", i - 1, ": swapped V = t^3 V(1/t) mod U'"));
    chk((V2^2 - fr) % U2 == 0, Str("x", i - 1, ": U' | V'^2 - fRev"));
    \\ the Mod(t, U) branch agrees with apm_phi
    T2 = apm_tangent(S2, P2);
    chk(phiT(S2, P2, T2) == [U2, V2], Str("x", i - 1, ": ruling in K21[t]/(U') gives the same V'"));
    \\ other tangent vectors and scalings
    ph3 = phiT(S2, P2, 3 * T2 - 5 * P2);
    chk(ph3 == [U2, V2], Str("x", i - 1, ": T -> 3T - 5P"));
    ph3 = phiT(S2, 7 * P2, -2 * T2 + P2);
    chk(ph3 == [U2, V2], Str("x", i - 1, ": P -> 7P, T -> -2T + P"));
    Pi = apm_iota(P2);
    ph3 = phiT(S2, Pi, apm_iota(T2));
    chk(ph3 == [U2, -V2], Str("x", i - 1, ": iota gives (U', -V')"));
    printf("  swapped: a = %s\n", apply(e -> #Str(lift(e)), vector(3, j, T2 * S2[3 + j] * T2~)));
  );
}
quit;
