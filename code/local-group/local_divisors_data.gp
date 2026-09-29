\\ local_divisors_data.gp: writes lean/FurioLombardo/Discharge/SelmerSpan/DData.lean, the data of the local divisors D_1..D_7 of
\\ M4's basis (code/earlier-computations/local_images_twist<k>_e3.bin) on the reversed model Y^2 = g, g = (fRev k)^sigma over K_v.
\\ For each twist k and i: U = X^2 + p X + r with p = u1/u0, r = 1/u0 in K21 (the reversed u_i, exact), given by zk
\\ coordinates pL, rL over the denominators pM, rM; with F_j = 4 fRev_j (the Lean FnData), Z1 = 4 z1, Z0 = 4 z0 where
\\ z1 X + z0 = g mod U (the recurrence divR1, divR0 of Mumford.lean), the local square roots
\\   n^2 = Z0^2 - p Z1 Z0 + r Z1^2 (Hensel certificate b1, s1 at precision Pv),
\\   a^2 = 2 Z0 - p Z1 + 2 n       (Hensel certificate b2, s2 at precision Pv - s1 - 2),
\\ with the signs for which V = Z1/(2a) X + (a/4 + Z1 p/(4a)) is the stored v_i (reversed, t^3 v(1/t) mod U) at v.
\\ Every condition is replayed with the exact triple arithmetic of the Lean checks (completion_kv_lib.gp, as M4Cert), and the
\\ p-adic model (completion_kv_lib.gp) gives the signs and an independent check of every residue.
\\ Run from code/local-group: gp -q local_divisors_data.gp (LEANOUT=<dir>/ writes DData.lean to <dir> instead)
default(parisizemax, 3*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../descent/descent_data_lib.gp");
read("completion_kv_lib.gp");
read("lean_data_reader.gp");
Pv = 24;
\\ triple arithmetic with reduction, as the Lean evaluator (addT, subT, mulT reduce modulo 2^P)
addT(x, y, P) = modT(x + y, P);
subT(x, y, P) = modT(x - y, P);
mulT(x, y, P) = modT(mulZ(x, y), P);
cT(c) = [c, 0, 0];
\\ Lean's divR1T, divR0T (Mumford.lean recurrence on triples), F = [F0, .., F6]
divWT(p, r, F, P) = { my(w4 = F[7], w3, w2, w1, w0);
  w3 = subT(F[6], mulT(p, w4, P), P);
  w2 = subT(subT(F[5], mulT(p, w3, P), P), mulT(r, w4, P), P);
  w1 = subT(subT(F[4], mulT(p, w2, P), P), mulT(r, w3, P), P);
  w0 = subT(subT(F[3], mulT(p, w1, P), P), mulT(r, w2, P), P);
  [w4, w3, w2, w1, w0] };
divR1T(p, r, F, P) = { my(W = divWT(p, r, F, P)); subT(subT(F[2], mulT(p, W[5], P), P), mulT(r, W[4], P), P) };
divR0T(p, r, F, P) = { my(W = divWT(p, r, F, P)); subT(F[1], mulT(r, W[5], P), P) };
\\ n^2 target Z0^2 - p Z1 Z0 + r Z1^2 and a^2 target 2 Z0 - p Z1 + 2 n
nTT(p, r, Z1, Z0, P) = addT(subT(mulT(Z0, Z0, P), mulT(mulT(p, Z1, P), Z0, P), P), mulT(r, mulT(Z1, Z1, P), P), P);
aTT(p, Z1, Z0, bn, P) = addT(subT(mulT(cT(2), Z0, P), mulT(p, Z1, P), P), mulT(cT(2), bn, P), P);
minv2(v) = min(v2(v[1]), min(v2(v[2]), v2(v[3])));
atomD(e) = { my(m = den(zkc(e)), js = splitm(m)); [zkl(m * e), m, js[1], js[2], oinv(js[2])] };
FD = vector(2); PD = vector(2); RD = vector(2); HD = vector(2);
{
  for (k = 1, 2,
    my(R = read(Str("../earlier-computations/local_images_twist", k - 1, "_e3.bin")), Fl = vector(7, j, FnDataL[k][8 - j]), tF, fr, Fk);
    \\ F_j = 4 fRev_j: atoms with denominator 1
    foreach (Fl, l, chq(sQok(l, 0, 1, 1, Pv), "sQok F_j"));
    tF = vector(7, j, sQres(Fl[j], 0, 1, Pv));
    Fk = vector(7, j, sg(nfbasistoalg(nf, Fl[j]~)));
    for (j = 1, 7, chq(modT(tF[j], Pv) == trip(Fk[j], Pv), "tF agrees with the p-adic sigma(F_j)"));
    fr = sum(j = 1, 7, nfbasistoalg(nf, Fl[j]~) / 4 * t^(j - 1));
    PD[k] = vector(7); RD[k] = vector(7); HD[k] = vector(7);
    printf("---- twist %d\n", k - 1);
    for (i = 1, 7,
      my(uu = subst(lift(R[7][i][1]), 'x, t), vv = subst(lift(R[7][i][2]), 'x, t), u0 = polcoef(uu, 0, t), u1 = polcoef(uu, 1, t),
         p, r, Ap, Ar, tp, tr, Z1, Z0, tN, pk, rk, Z1k, Z0k, nk, best = [-1], vr, U);
      p = red(lift(Mod(u1, K21) / Mod(u0, K21))); r = red(lift(1 / Mod(u0, K21))); U = t^2 + p*t + r;
      chq(red(U * u0 - polrecip(uu)) == 0, "U = u^rev");
      vr = red(lift(Mod(Mod(1, K21) * (t^3 * subst(vv, t, 1/t)), Mod(1, K21) * U)));
      Ap = atomD(p); Ar = atomD(r);
      chq(Ap[3] + Pv <= 28 && Ar[3] + Pv <= 28, "precision budget of the atoms");
      chq(sQok(Ap[1], Ap[3], Ap[4], Ap[5], Pv) && sQok(Ar[1], Ar[3], Ar[4], Ar[5], Pv), "sQok p, r");
      tp = sQres(Ap[1], Ap[3], Ap[5], Pv); tr = sQres(Ar[1], Ar[3], Ar[5], Pv);
      pk = sg(p); rk = sg(r);
      chq(modT(tp, Pv) == trip(pk, Pv) && modT(tr, Pv) == trip(rk, Pv), "tp, tr agree with the p-adic sigma");
      Z1 = divR1T(tp, tr, tF, Pv); Z0 = divR0T(tp, tr, tF, Pv);
      \\ p-adic: g mod U
      my(Rm = red(lift(Mod(Mod(1, K21) * fr, Mod(1, K21) * U))));
      Z1k = 4 * sg(polcoef(Rm, 1, t)); Z0k = 4 * sg(polcoef(Rm, 0, t));
      chq(modT(Z1, Pv) == trip(Z1k, Pv) && modT(Z0, Pv) == trip(Z0k, Pv), "Z1, Z0 agree with g mod U");
      tN = nTT(tp, tr, Z1, Z0, Pv);
      nk = ksqrt(Z0k^2 - pk * Z1k * Z0k + rk * Z1k^2);
      chq(vpi(nk^2 - (Z0k^2 - pk * Z1k * Z0k + rk * Z1k^2)) > 2000, "n");
      foreach ([1, -1], sn, my(n1 = sn * nk, w2 = 2 * Z0k - pk * Z1k + 2 * n1);
        if (ksq(w2), my(a1 = ksqrt(w2));
          foreach ([1, -1], sa, my(aa = sa * a1, bb = Z1k / (2 * aa), cc = aa / 4 + bb * pk / 2, dv, dmin);
            dv = [sg(polcoef(vr, 1, t)) - bb, sg(polcoef(vr, 0, t)) - cc];
            dmin = min(vpi(dv[1]), vpi(dv[2]));
            if (dmin > best[1], best = [dmin, n1, aa]))));
      chq(best[1] >= 60, "V agrees with the stored v_i");
      my(n1 = best[2], a1 = best[3], b1, s1, P1, ta, b2, s2, P2);
      b1 = trip(n1, Pv); s1 = minv2(b1);
      chq(2 * s1 + 4 <= Pv && lowOK(b1, s1), "Hensel 1 precision");
      chq(modT(mulZ(b1, b1), Pv) == modT(tN, Pv), "b1^2 = N mod 2^Pv");
      chq(modT(tN, Pv) != [0, 0, 0], "N != 0 (coprimality)");
      P1 = Pv - (s1 + 2);
      ta = aTT(modT(tp, P1), modT(Z1, P1), modT(Z0, P1), modT(b1, P1), P1);
      b2 = trip(a1, P1); s2 = minv2(b2);
      chq(2 * s2 + 4 <= P1 && lowOK(b2, s2), "Hensel 2 precision");
      chq(modT(mulZ(b2, b2), P1) == modT(ta, P1), "b2^2 = 2 Z0 - p Z1 + 2 n mod 2^P1");
      P2 = P1 - (s2 + 2);
      chq(modT(b2, P2) != [0, 0, 0], "a != 0");
      PD[k][i] = Ap; RD[k][i] = Ar; HD[k][i] = [b1, s1, b2, s2];
      printf("  D_%d: p den 2^%d, r den 2^%d; v(n) %d, v(a) %d; b1 = %s (s1 %d), b2 = %s (s2 %d); precisions %d, %d, %d; V - v^rev: %d\n",
        i, Ap[3], Ar[3], vpi(n1), vpi(a1), b1, s1, b2, s2, Pv, P1, P2, best[1])));
}
\\ ---------------------------------------------------------------- Lean output
lstl(V) = { my(s = "["); for (i = 1, #V, s = Str(s, V[i], if (i < #V, ", ", ""))); Str(s, "]") };
trl(v) = Str("(", v[1], ", ", v[2], ", ", v[3], ")");
out = Str(if (#getenv("LEANOUT"), getenv("LEANOUT"), "../../FurioLombardo/Discharge/SelmerSpan/"), "DData.lean");
system(Str("rm -f ", out));
write(out, "/-! Data of the local divisors D_1..D_7 (lane SelmerSpan; generated by code/local-group/local_divisors_data.gp, PARI/GP).\n`pData[k][i]`, `pDen[k][i]` (and `r`): zk coordinates and denominator of `p = u1/u0`, `r = 1/u0` (the reversed\n`u_i` of code/earlier-computations/local_images_twist<k>_e3.bin); `pJO[k][i] = [j, o]` with `pDen = 2^j o` and `pOi[k][i]` an inverse of\n`o` modulo `2^28`; `hens[k][i] = (b1, s1, b2, s2)`: the Hensel certificates of `n` and `a`. -/\n\nnamespace FurioLombardo.Discharge.SelmerSpan\n\nset_option maxRecDepth 100000\n");
{
  my(sp = "[", sr = "[", dp = "[", dr = "[", jp = "[", jr = "[", op = "[", orr = "[", hs = "[");
  for (k = 1, 2,
    sp = Str(sp, "["); sr = Str(sr, "["); dp = Str(dp, "["); dr = Str(dr, "["); jp = Str(jp, "["); jr = Str(jr, "[");
    op = Str(op, "["); orr = Str(orr, "["); hs = Str(hs, "[");
    for (i = 1, 7, my(sep = if (i < 7, ",\n   ", ""), sep2 = if (i < 7, ", ", ""));
      sp = Str(sp, lstl(PD[k][i][1]), sep); sr = Str(sr, lstl(RD[k][i][1]), sep);
      dp = Str(dp, PD[k][i][2], sep2); dr = Str(dr, RD[k][i][2], sep2);
      jp = Str(jp, "[", PD[k][i][3], ", ", PD[k][i][4], "]", sep2); jr = Str(jr, "[", RD[k][i][3], ", ", RD[k][i][4], "]", sep2);
      op = Str(op, PD[k][i][5], sep2); orr = Str(orr, RD[k][i][5], sep2);
      hs = Str(hs, "(", trl(HD[k][i][1]), ", ", HD[k][i][2], ", ", trl(HD[k][i][3]), ", ", HD[k][i][4], ")", sep2));
    my(sepk = if (k < 2, ",\n  ", "]"));
    sp = Str(sp, "]", sepk); sr = Str(sr, "]", sepk); dp = Str(dp, "]", sepk); dr = Str(dr, "]", sepk); jp = Str(jp, "]", sepk);
    jr = Str(jr, "]", sepk); op = Str(op, "]", sepk); orr = Str(orr, "]", sepk); hs = Str(hs, "]", sepk));
  write(out, "/-- `Pv`: the working precision (powers of 2) of the local certificates. -/\ndef Pv : Nat := ", Pv, "\n");
  write(out, "def pData : List (List (List Int)) :=\n  ", sp, "\n");
  write(out, "def rData : List (List (List Int)) :=\n  ", sr, "\n");
  write(out, "def pDen : List (List Nat) :=\n  ", dp, "\n");
  write(out, "def rDen : List (List Nat) :=\n  ", dr, "\n");
  write(out, "def pJO : List (List (List Nat)) :=\n  ", jp, "\n");
  write(out, "def rJO : List (List (List Nat)) :=\n  ", jr, "\n");
  write(out, "def pOi : List (List Int) :=\n  ", op, "\n");
  write(out, "def rOi : List (List Int) :=\n  ", orr, "\n");
  write(out, "def hens : List (List ((Int × Int × Int) × Nat × (Int × Int × Int) × Nat)) :=\n  ", hs, "\n");
  write(out, "end FurioLombardo.Discharge.SelmerSpan");
}
print("written ", out);
quit;
