\\ assembly_data.gp: the data of the assembly of SelmerBasisK21 k T_k.SB in Lean
\\ (lean/FurioLombardo/Discharge/SelmerBasis/AssemblyData.lean), with every kernel check emulated.
\\
\\ Rows. For each twist the rows of the local conditions, in the order of the Lean place family:
\\   twist 0: v (11, VPlace.CvRows), w2 (39), w3 (21, the Lean rows of W3.C3 printed by w6_rows_print.lean),
\\            real places 5, 6 (2 each, from the signs of Pgen s at the four real roots);
\\   twist 1: v (11), w2 (39), w3 (21), the place above 7 (5).
\\ The w2 and 7 rows are those of stage 6 of code/selmer-local-conditions/selmer_rows_twist<k>_<place>.out
\\ (code/selmer-local-conditions/selmer_rows_twist<k>_<place>.gp). A row is a natural number, bit s = entry s (generator s).
\\ Span. W = beta_0..beta_3 (VPlace.betaRows) and kappa_1..kappa_15 (columns 2..16 of SBX_kappa of
\\ code/selmer-global-bound/sunit_export_data.gp; kappa_0 is the sum of the others in the relation SBX_kapRel).
\\ Certificate. kerSpanOK M m 82 T piv q W 19 U (Echelon.lean): T k combines the stacked rows into the reduced
\\ row with pivot piv k; U j writes the kernel vector of the free column j on W.
\\ Signs. Sg k s j = 1 iff Pgen s is negative at the root j (increasing order) of fRev 0 at realEmb k
\\ (places 5, 6 = realEmb 0, 1 = nfK.roots[1], [2], code/selmer-local-conditions/real_roots.out); numerical, with a
\\ margin check (|value| > 10^-30 times the sum of the absolute values of its terms); the Lean proof of SignOK
\\ uses the data of code/selmer-local-conditions/local_data_real.gp.
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-assembly/assembly_data.gp < /dev/null > ../selmer-assembly/assembly_data.out 2>&1
\\ Output: /tmp/sa2/AssemblyData.lean (installed by hand into lean/FurioLombardo/Discharge/SelmerBasis/).
default(parisizemax, 2000 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp");
read("../selmer-local-conditions/selmer_rows_lib.gp"); read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
SB = "../selmer-local-conditions/";
OUTD = "/tmp/sa2/";
T00 = getabstime();
default(realprecision, 200);
sb_init();
read("../selmer-global-bound/sunit_export_data.gp");
tobits(M) = vector(matsize(M)[1], i, sum(s = 1, matsize(M)[2], lift(M[i, s]) * 2^(s - 1)));
frombits(v, n) = matrix(#v, n, i, s, bittest(v[i], s - 1));
f2rank(M) = if (#M == 0, 0, matrank(Mod(M, 2)));
lst(v) = { my(s = "["); for (i = 1, #v, s = Str(s, if (i > 1, ", ", ""), v[i])); Str(s, "]"); }
\\ the rows of a stage 6 certificate file
rows_of(k, pl) = { SB2_ROWS = 0; read(Str(SB, "selmer_rows_twist", k, "_", pl, ".gp")); SB2_ROWS[1]; }
\\ ---------------------------------------------------------------- generators and signs (as selmer_rows.gp)
gens_from_lean(fn) = {
  my(pg = vector(82, s1, leandef5(fn, Str("pgen_", s1 - 1))), pd = leandef5(fn, "pgenDen"));
  chq(#pg == 82 && #pd == 82, "SUnitData.lean: 82 Pgen");
  vector(82, s1, lift(Mod(1, K21) * sum(i = 1, 6, nfbasistoalg(nfK, Col(pg[s1][i])) * x^(i - 1)) / pd[s1]));
}
\\ Sg as 4-bit masks per generator, at the real embedding i (1 or 2) of nfK.roots, for fRev_0 (SBf[1])
sign_masks(i, G) = {
  my(emb = (c -> subst(lift(Mod(c, K21)), b, real(nfK.roots[i]))), fr = Pol(apply(emb, Vec(SBf[1])), x),
    rr = vecsort(real(select(z -> abs(imag(z)) < 10^-40, polroots(fr)))), msk = vector(82));
  chq(#rr == 4, Str("fRev_0 has 4 real roots at the real embedding ", i, ": ", apply(r -> precision(r, 20), rr)));
  for (s1 = 1, 82, my(Gr = Pol(apply(emb, Vec(G[s1])), x));
    for (l = 1, 4, my(v = subst(Gr, x, rr[l]), bd = subst(Pol(apply(abs, Vec(Gr)), x), x, abs(rr[l])));
      if (abs(v) < 10^-30 * bd, error("sign_masks: margin"));
      if (v < 0, msk[s1] += 2^(l - 1))));
  msk;
}
real_rows_of(msk) = {
  [sum(s1 = 1, 82, ((bittest(msk[s1], 0) + bittest(msk[s1], 3)) % 2) * 2^(s1 - 1)),
    sum(s1 = 1, 82, ((bittest(msk[s1], 1) + bittest(msk[s1], 2)) % 2) * 2^(s1 - 1))];
}
\\ ---------------------------------------------------------------- F_2 certificate
xorSel(R, m, c) = { my(r = 0); for (i = 1, m, if (bittest(c, i - 1), r = bitxor(r, R[i]))); r; }
freeVec(Rp, piv, j, q) = { my(f = 2^j); for (k = 1, q, if (bittest(Rp[k], j), f = bitxor(f, 2^piv[k]))); f; }
\\ reduced row echelon with the combinations: [piv, T, Rp]
ech(M, n) = {
  my(m = #M, R = M, C = vector(m, i, 2^(i - 1)), used = vector(m), piv = List(), prow = List());
  for (j = 0, n - 1, my(r = 0);
    for (i = 1, m, if (!used[i] && bittest(R[i], j), r = i; break));
    if (!r, next);
    used[r] = 1; listput(piv, j); listput(prow, r);
    for (i = 1, m, if (i != r && bittest(R[i], j), R[i] = bitxor(R[i], R[r]); C[i] = bitxor(C[i], C[r]))));
  [Vec(piv), vector(#prow, k, C[prow[k]]), vector(#prow, k, R[prow[k]])];
}
\\ kerSpanOK M m n T piv q W nw U, emulated (lists are 1-based here, indices 0-based in Lean)
kerSpanOK(M, m, n, T, piv, q, W, nw, U) = {
  for (k = 1, q, if (piv[k] >= n, return(0));
    my(r = xorSel(M, m, T[k])); for (k2 = 1, q, if (bittest(r, piv[k2]) != (k == k2), return(0))));
  my(Rp = vector(q, k, xorSel(M, m, T[k])));
  for (j = 0, n - 1, if (setsearch(Set(piv), j), next);
    if (xorSel(W, nw, U[j + 1]) != freeVec(Rp, piv, j, q), return(0)));
  1;
}
\\ U j: the combination of the rows W giving v (a bitmask over the rows), or -1
comb_of(W, v, n) = {
  my(A = matrix(n, #W, s, l, bittest(W[l], s - 1)), B = vector(n, s, bittest(v, s - 1))~, sol);
  sol = matinverseimage(Mod(A, 2), Mod(B, 2));
  if (#sol == 0, return(-1));
  sum(l = 1, #W, lift(sol[l]) * 2^(l - 1));
}
{
  my(G = gens_from_lean(Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean")), CvL = leandef5(Str(LEAN, "Discharge/SelmerBasis/VPlace.lean"), "CvRows"),
    BtL = leandef5(Str(LEAN, "Discharge/SelmerBasis/VPlace.lean"), "βRows"), W3 = eval(strsplit(readstr("../selmer-assembly/w6_rows_print.out")[1], "= ")[2]),
    C2 = vector(2), C7, Sg = vector(2), RR = vector(2), kap, Wl, out = vector(2), f = Str(OUTD, "AssemblyData.lean"));
  \\ rows of the places
  for (k = 0, 1, my(cv = tobits(rows_of(k, "v")), c3 = rows_of(k, "w6"));
    chq(CvL[k + 1] == cv, Str("twist ", k, ": VPlace.CvRows = the stage 6 rows at v"));
    C2[k + 1] = tobits(rows_of(k, "w12"));
    chq(#C2[k + 1] == 39 && f2rank(frombits(C2[k + 1], 82)) == 39, Str("twist ", k, ": 39 rows of rank 39 at w2"));
    chq(#W3[k + 1] == 21 && f2rank(frombits(W3[k + 1], 82)) == f2rank(matconcat([frombits(W3[k + 1], 82); c3])) && f2rank(c3) == f2rank(frombits(W3[k + 1], 82)),
      Str("twist ", k, ": the Lean rows C3 and the stage 6 rows at w3 have the same row space (rank ", f2rank(c3), ")")));
  C7 = tobits(rows_of(1, "w7"));
  chq(#C7 == 5 && f2rank(frombits(C7, 82)) == 5, "twist 1: 5 rows of rank 5 at the place above 7");
  for (i = 1, 2, Sg[i] = sign_masks(i, G); RR[i] = real_rows_of(Sg[i]));
  \\ the rows of real_rows of selmer_rows.gp (independent formula on the same numbers): the same
  for (i = 1, 2, chq(f2rank(frombits(RR[i], 82)) == 2, Str("real place ", 4 + i, ": 2 rows of rank 2")));
  \\ the span
  chq(matsize(SBX_kappa) == [82, 16] && SBX_kapRel[1] == 1 && lift(Mod(SBX_kappa * SBX_kapRel, 2)) == 0,
    "kappa_0 is the sum of the kappa_t in the relation SBX_kapRel (bit 0 set), so kappa_1..kappa_15 span the same space");
  kap = tobits(SBX_kappa~)[2 .. 16];
  for (k = 0, 1, my(bt = BtL[k + 1]);
    chq(bt == tobits(SBX_beta[k + 1]~), Str("twist ", k, ": VPlace.betaRows = SBX_beta"));
    Wl = concat(bt, kap);
    chq(f2rank(frombits(Wl, 82)) == 19, Str("twist ", k, ": beta_0..3, kappa_1..15 independent (dim 19)"));
    my(M = if (k == 0, concat([CvL[1], C2[1], W3[1], RR[1], RR[2]]), concat([CvL[2], C2[2], W3[2], C7])), m = #M, e = ech(M, 82), piv = e[1], T = e[2], Rp = e[3], q = #piv, U, ok, M2, cnt);
    printf("  twist %d: %d stacked rows, rank %d, kernel dimension %d\n", k, m, q, 82 - q);
    chq(q == 63, Str("twist ", k, ": the stacked rows have rank 63 (kernel of dimension 19)"));
    U = vector(82, j, if (setsearch(Set(piv), j - 1), 0, comb_of(Wl, freeVec(Rp, piv, j - 1, q), 82)));
    chq(vecmin(U) >= 0, Str("twist ", k, ": every kernel vector is a combination of beta and kappa"));
    ok = kerSpanOK(M, m, 82, T, piv, q, Wl, 19, U);
    chq(ok, Str("twist ", k, ": kerSpanOK holds (emulated)"));
    \\ negative controls
    my(U2 = U, jf = 0); for (j = 1, 82, if (!setsearch(Set(piv), j - 1), jf = j; break)); U2[jf] = bitxor(U2[jf], 1);
    chq(!kerSpanOK(M, m, 82, T, piv, q, Wl, 19, U2), Str("twist ", k, ": negative control: one bit of U flipped fails"));
    M2 = concat([M[1 .. 11], M[51 .. m]]); cnt = f2rank(frombits(M2, 82));
    chq(cnt < 63, Str("twist ", k, ": negative control: without w2 the rank drops to ", cnt));
    out[k + 1] = [M, T, piv, U]);
  \\ write the Lean data
  system(Str("mkdir -p ", OUTD)); system(Str("rm -f ", f));
  write(f, "import Mathlib\n\n/-!\n# Data of the assembly of `SelmerBasisK21` (generated)\n\nWritten by code/selmer-assembly/assembly_data.gp (output assembly_data.out); every datum is checked by the kernel or used\nonly through a statement proved elsewhere. Rows are natural numbers with bit `s` the entry of generator `s`.\n\n* `C2Rows k`: the 39 rows at w2 (stage 6 of code/selmer-local-conditions/selmer_rows_twist<k>_w12.out).\n* `C7Rows`: the 5 rows at the place above 7 (twist 1, stage 6 of selmer_rows_twist1_w7.out).\n* `SgRows k`: for each generator `s` the 4-bit mask of the signs of `Pgen s` at the real roots of `fRev 0` at\n  `realEmb k` (bit `j`: negative at the root `j`, increasing order); numerical in PARI, proved in Lean by `signOK`.\n* `kapRows`: `κ_1, ..., κ_15` (columns of `SBX_kappa` of code/selmer-global-bound/sunit_export_data.gp).\n* `stk k`, `Tk k`, `pivk k`, `Uk k`: the stacked rows and the certificate of `kerSpanOK` for twist `k`.\n-/\n\nnamespace FurioLombardo.Discharge.SelmerBasis.Assembly\n");
  write(f, "/-- The rows at w2. -/\ndef C2Rows : Fin 2 → List ℕ :=\n  ![", lst(C2[1]), ",\n    ", lst(C2[2]), "]\n");
  write(f, "/-- The rows at the place above 7 (twist 1). -/\ndef C7Rows : List ℕ := ", lst(C7), "\n");
  write(f, "/-- The sign masks at the real places 5, 6 (`realEmb 0`, `realEmb 1`). -/\ndef SgRows : Fin 2 → List ℕ :=\n  ![", lst(Sg[1]), ",\n    ", lst(Sg[2]), "]\n");
  write(f, "/-- The two rows at each real place. -/\ndef RealRows : Fin 2 → List ℕ :=\n  ![", lst(RR[1]), ",\n    ", lst(RR[2]), "]\n");
  write(f, "/-- `κ_1, ..., κ_15`. -/\ndef kapRows : List ℕ := ", lst(kap), "\n");
  for (k = 0, 1, my(o = out[k + 1]);
    write(f, "/-- The stacked rows of twist ", k, ". -/\ndef stk", k, " : List ℕ := ", lst(o[1]), "\n");
    write(f, "/-- The combinations of the reduced rows, twist ", k, ". -/\ndef T", k, " : List ℕ := ", lst(o[2]), "\n");
    write(f, "/-- The pivots, twist ", k, ". -/\ndef piv", k, " : List ℕ := ", lst(o[3]), "\n");
    write(f, "/-- The kernel vectors on `β, κ`, twist ", k, ". -/\ndef U", k, " : List ℕ := ", lst(o[4]), "\n"));
  write(f, "end FurioLombardo.Discharge.SelmerBasis.Assembly");
  printf("wrote %s\n", f);
  printf("DONE, %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00);
}
