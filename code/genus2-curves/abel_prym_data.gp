\\ abel_prym_data.gp: writes lean/FurioLombardo/Discharge/M3a/AbelPrymData.lean (WP4 of the M3a discharge).
\\ Certificates of Bruin's Abel-Prym map (abel_prym_lib.gp) on the reversed model at the four known lifts x0, x1, x2, x3
\\ (P0 = (0:0:1), P1 = (1:1:1), P2 = (2:0:1), P3 = (-1:0:1); twist 0 for x0, x2, twist 1 for x1, x3).
\\ The reversed model uses the swapped forms (Q3, Q2, Q1) at the swapped point P' = (p, s, r) (Lean's `phiRev`,
\\ `swapPt`); the data of point i (0-based, the index of liftData in DataBruin.lean):
\\   apM[i]        a positive integer m;
\\   apT[i]        zk coordinates of [t1, t3, t4], where T = (m, t1, 0, t3, t4) is a tangent vector of D at P',
\\                 not proportional to P' (normalized by T_z = 0 and T_x = m);
\\   apUd[i], apU[i]   Ud and zk coordinates of [Ud u0, Ud u1]: U' = t^2 + u1 t + u0 = t^2 + 2 (a2/a3) t + a1/a3
\\                 with a_j = QD'_j(T) (Lean's `bruinU`);
\\   apD[i], apV[i], apW[i]   D and zk coordinates of [D v0, D v1] and [D w0, D w1]: V' = v1 t + v0 and
\\                 w = w1 t + w0 with (G A G)_{2,4} - m V' = (a3 t^2 + 2 a2 t + a1) w (1-based PARI indices; Lean's
\\                 entry (1, 3); the Hodge entry there is the constant m);
\\   apNj[i], apN[i]   an index j0 and the zk coordinates of 2 N_{j0}, where N = (r^2 M3 - 2 r s M2 + s^2 M1) p is
\\                 nonzero (Lean's rank condition `rank_of`, for the swapped forms);
\\   (printed) a degree one prime among (13, 11), (23, 5), (3, 2) where 2 N_{j0} has a nonzero residue.
\\ Checks here, exactly in K21[t]: the tangent equations, independence, a3 != 0, the ruling identity in K21[t]/(U')
\\ (abel_prym_lib's apm_ruling, via wp4_a's phiT), U' | V'^2 - fRev, and agreement of (U', V') with phi_known_lifts.gp transported
\\ to the reversed model (U' = U^rev / U(0), V' = t^3 V(1/t) mod U').
\\ Run from code/genus2-curves: gp -q abel_prym_data.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
LEANDIR = if (type(getenv("LEANOUT")) == "t_STR", getenv("LEANOUT"), "../../");  \\ LEANOUT=<dir>/ writes the Lean file under <dir> instead of lean/
read("../descent/descent_data_lib.gp");
read("../earlier-computations/abel_prym_lib.gp");
read("../earlier-computations/phi_known_lifts.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg));
red(g) = lift(Mod(1, K21) * g);
den(v) = denominator(content(v));
zkl(e) = { my(v = zkc(e)); if (den(v) != 1, error("non integral zk coordinates")); v~ };
cden(l) = lcm(apply(e -> den(zkc(e)), l));
phiT(S, P, T) = {
  my(a = vector(3, i, T * S[3 + i] * T~), U, Y);
  U = t^2 + 2*a[2]/a[3]*t + a[1]/a[3];
  Y = apm_ruling(S, P, T, Mod(t, U));
  [U, lift(Y)];
};
resz(a, p, r) = { my(u = Mod(Dz, p)^(-1), s = Mod(0, p)); for (j = 1, 21, s += a[j] * subst(Pol(Vecrev(zkNum[j]), 'w), 'w, Mod(r, p))); lift(u * s) };
RP = [[13, 11], [23, 5], [3, 2]];
Pts = [[0, 0, 1], [1, 1, 1], [2, 0, 1], [-1, 0, 1]];
dd = [d0, d1];
Ev(Q, P) = red(substvec(Q, [x, y, z], P));
AM = vector(4); AT = vector(4); AUd = vector(4); AU = vector(4); AD = vector(4); AV = vector(4); AW = vector(4);
ANj = vector(4); AN = vector(4); ARP = vector(4);
{ for (i = 1, 4,
    my(P0 = Pts[i], k = if (i == 1 || i == 3, 1, 2), dl = Mod(dd[k], K21), v = vector(3, j, Ev(Qs[j], P0)), r, s, P2, S2,
       Jm, Kr, T, m, av, U, V, ph, Ur, Vr, Mt, G, A, GA, e24, Ut, wq, rm, Dn, N, j0, fr);
    \\ the lift, exactly as bruin_data.gp
    if (v[1] != 0,
      r = nfroots(nf, 'X^2 - red(v[1] / dd[k])); r = r[1]; s = red(v[2] / (dd[k] * r)),
      r = 0; s = nfroots(nf, 'X^2 - red(v[3] / dd[k])); s = s[1]);
    chk(lift(concat(P0 * Mod(1, K21), [Mod(r, K21), Mod(s, K21)])) == PHI[i][3], "lift = the lift of phi_known_lifts.gp");
    zkl(r); zkl(s);
    P2 = concat(P0 * Mod(1, K21), [Mod(s, K21), Mod(r, K21)]);
    S2 = apm_init(Q3 * Mod(1, K21), Q2 * Mod(1, K21), Q1 * Mod(1, K21), dl);
    chk(apm_ondp(S2, P2), "P' on D (swapped forms)");
    fr = S2[8];
    \\ tangent vector: T_z = 0, T_x = m
    Jm = matrix(3, 5, ii, jj, (S2[3 + ii] * P2~)[jj]);
    Kr = matker(Jm);
    chk(#Kr == 2, "tangent space of dimension 2 (rank 3)");
    T = Kr[, 1]~; if (matrank(Mat([P2~, T~])) < 2, T = Kr[, 2]~);
    T = T - T[3] / P2[3] * P2;
    chk(T[1] != 0, "T_x != 0");
    T = T / T[1];
    m = cden([T[2], T[4], T[5]]);
    T = m * T;
    chk(T[1] == m && T[3] == 0 && Jm * T~ == 0, "T normalized and tangent");
    AM[i] = m; AT[i] = [zkl(T[2]), zkl(T[4]), zkl(T[5])];
    \\ U'
    av = vector(3, j, T * S2[3 + j] * T~);
    chk(av[3] != 0, "a3 != 0");
    U = t^2 + 2*av[2]/av[3]*t + av[1]/av[3];
    AUd[i] = cden([polcoef(U, 0, t), polcoef(U, 1, t)]);
    AU[i] = [zkl(AUd[i] * polcoef(U, 0, t)), zkl(AUd[i] * polcoef(U, 1, t))];
    \\ V' from the ruling in K21[t]/(U'), and the transported phi_known_lifts.gp values
    ph = phiT(S2, P2, T);
    chk(ph[1] == U, "phiT U");
    V = ph[2];
    Ur = polrecip(PHI[i][4]) / polcoef(PHI[i][4], 0, t);
    Vr = red((polcoef(PHI[i][5], 0, t) * t^3 + polcoef(PHI[i][5], 1, t) * t^2) % Ur);
    chk(red(U - Ur) == 0, "U' = transported U of phi_known_lifts.gp");
    chk(red(V - Vr) == 0, "V' = transported V of phi_known_lifts.gp");
    chk(red(Mod(1, K21) * (V^2 - fr) % U) == 0, "U' | V'^2 - fRev");
    chk(poldegree(V, t) <= 1, "deg V' <= 1");
    \\ the entry (2, 4) of G A G and the quotient w
    Mt = S2[1] + 2*t*S2[2] + t^2*S2[3];
    G = matconcat([Mt, matrix(3, 1); matrix(1, 3), Mat(-dl)]);
    A = [P2[1], P2[2], P2[3], P2[4] + t*P2[5]]~ * [T[1], T[2], T[3], T[4] + t*T[5]] -
        [T[1], T[2], T[3], T[4] + t*T[5]]~ * [P2[1], P2[2], P2[3], P2[4] + t*P2[5]];
    chk(apm_star(A)[2, 4] == m, "Hodge entry (2, 4) = m");
    GA = G * A * G;
    e24 = red(lift(GA[2, 4]));
    Ut = red(av[3] * t^2 + 2 * av[2] * t + av[1]);
    wq = divrem(Mod(1, K21) * (e24 - m * V), Mod(1, K21) * Ut, t);
    rm = red(lift(wq[2]));
    chk(rm == 0, "(G A G)_{2,4} - m V' = (a3 U') w exactly");
    wq = red(lift(wq[1]));
    chk(poldegree(wq, t) <= 1 && poldegree(e24, t) <= 3, "degrees");
    chk(red(e24 - m * V - Ut * wq) == 0, "ruling entry identity");
    Dn = cden([polcoef(V, 0, t), polcoef(V, 1, t), polcoef(wq, 0, t), polcoef(wq, 1, t)]);
    AD[i] = Dn;
    AV[i] = [zkl(Dn * polcoef(V, 0, t)), zkl(Dn * polcoef(V, 1, t))];
    AW[i] = [zkl(Dn * polcoef(wq, 0, t)), zkl(Dn * polcoef(wq, 1, t))];
    \\ the rank condition
    N = (Mod(r, K21)^2 * S2[1] - 2 * Mod(r, K21) * Mod(s, K21) * S2[2] + Mod(s, K21)^2 * S2[3]) * (P0 * Mod(1, K21))~;
    j0 = 0; ARP[i] = 0;
    for (j = 1, 3, if (N[j] != 0 && j0 == 0,
      my(zl = zkl(2 * N[j]));
      for (q = 1, #RP, if (ARP[i] == 0 && resz(zl, RP[q][1], RP[q][2]) != 0, ARP[i] = RP[q]; j0 = j))));
    chk(j0 != 0, "a component of N with a nonzero residue");
    ANj[i] = j0 - 1; AN[i] = zkl(2 * N[j0]);
    printf("x%d (twist %d): m = %d, Ud = %d, D = %d, N index %d, residue prime %s; all checks passed\n",
      i - 1, k - 1, m, AUd[i], Dn, j0 - 1, ARP[i]);
  );
}
out = Str(LEANDIR, "FurioLombardo/Discharge/M3a/AbelPrymData.lean");
system(Str("rm -f ", out));
lst3(V) = { my(s = "["); for (i = 1, #V, s = Str(s, lstl(V[i]), if (i < #V, ",\n  ", ""))); Str(s, "]") };
write(out, "/-! Data of WP4 of the M3a discharge (generated by code/genus2-curves/abel_prym_data.gp, PARI/GP):\ncertificates of Bruin's Abel-Prym map on the reversed model at the known lifts `x0`, `x1`, `x2`, `x3` (index `i`\nof `liftData`). Every element of K21 is a list of zk coordinates (lane M1's `zkE`); every identity between these\ndata is rechecked by the Lean kernel in `FurioLombardo.Discharge.M3a.AbelPrymCheck`. See the generator for the\nmeaning of each list. -/\n\nnamespace FurioLombardo.Discharge.M3a.Bruin\n\nset_option maxRecDepth 100000\n");
write(out, "/-- `apM[i] = m`: the tangent vector is `T = (m, t1, 0, t3, t4)`. -/\ndef apM : List Nat := ", lst(AM), "\n");
write(out, "/-- `apT[i] = [t1, t3, t4]`. -/\ndef apT : List (List (List Int)) :=\n  ", lst3(AT), "\n");
write(out, "/-- `U' = X^2 + (apU[i][1] / apUd[i]) X + apU[i][0] / apUd[i]`. -/\ndef apUd : List Nat := ", lst(AUd), "\n\ndef apU : List (List (List Int)) :=\n  ", lst3(AU), "\n");
write(out, "/-- `V' = (apV[i][0] + apV[i][1] X) / apD[i]`, `w = (apW[i][0] + apW[i][1] X) / apD[i]`. -/\ndef apD : List Nat := ", lst(AD), "\n\ndef apV : List (List (List Int)) :=\n  ", lst3(AV), "\n\ndef apW : List (List (List Int)) :=\n  ", lst3(AW), "\n");
write(out, "/-- `2 N_j` for `j = apNj[i]`, `N = (r^2 M3 - 2 r s M2 + s^2 M1) p`. -/\ndef apNj : List Nat := ", lst(ANj), "\n\ndef apN : List (List Int) :=\n  ", lstl(AN), "\n");
write(out, "end FurioLombardo.Discharge.M3a.Bruin");
print("written ", out);
quit;
