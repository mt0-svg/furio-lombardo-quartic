\\ sunit_data_lean.gp: writes the candidate of
\\ lean/FurioLombardo/Discharge/SelmerBasis/SUnitData.lean to /tmp/sb5/SUnitData.cand.lean from sb_5a (tower.bin:
\\ alpha, beta), the generator data file sunit_generators_data.gp (sb_5b, sb_5s), sb_5c (pgen.bin: Pgen, power tables) and
\\ sb_5d (chars.bin: residue characters), sb_5t (muT.bin: the certificate of mu(T), k = 0, 1), one def per list
\\ entry (gL_s, gN_s, gLw_s, gNw_s, pgen_s, alphaPow_i, betaPow_i) and the lists of these names (gL := [gL_0, ...,
\\ gL_28], ...). Then it reads the candidate back (leandefs5, leanentries5 of tower_lib.gp: every list checked to be
\\ exactly the list of its entry defs) and rechecks every datum from the text, exactly:
\\   lengths (gL, gLw, gLab 29; gN, gNw, gNab 53; pgen, pgenDen 82; alphaPow, betaPow 6; chL, RL, TL 29;
\\   chN, RN, TN 53), every zk list of length 21, no zero denominator, every generator nonzero;
\\   q k (alpha) = 0, h k (beta) = 0 for k = 0, 1 (DataBruin.lean);
\\   gL s * gLw s = 2^a 7^b, gN s * gNw s = 2^a 7^b with (a, b) = gLab s, gNab s;
\\   the 82 x 2 Pgen identities, by Horner at alpha, beta and through the power tables (alphaPow 0 = 1,
\\   alphaPow (i + 1) = alphaPow i * alphaL, betaPow 0 = 1, betaPow (i + 1) = betaPow i * betaPow 1 with
\\   betaPow 1 = betaPowDen beta, betaPowDen = 2 betaDen; sum_i pgen s i P i D^(5 - i) = pgenDen s D^5 target);
\\   the characters: the conditions on (p, t, s, t2), the rows RL, RN recomputed from the generators of the text
\\   (every generator nonzero mod p), leftInvOK RL 29 29 TL and leftInvOK RN 53 53 TN;
\\   the mu(T) certificates (k = 0, 1): shapes, aT_k in {0, 1}^82, prodLT_k and prodNT_k the products of the generators
\\   of the text selected by aT_k, kappa, y1, y2 nonzero, and the two identities of GlobalCRT.lean (A = alphaPow 1,
\\   B = betaPow 1, D_L = alphaDen, D_N = betaPowDen, FE, hData, hDen, qData, qDen of DataBruin.lean):
\\     -(FE k 0) [sum_i hL_i A^i D_L^(4-i)] prodLT kapTDen y1TDen^2 = 4 hDen D_L^4 kapT y1T^2,
\\     [sum_i qL_i B^i D_N^(2-i)] prodNT kapTDen y2TDen^2 = qDen D_N^2 kapT y2T^2;
\\ and equality with the sources. Negative controls: a changed coordinate breaks the S-unit identity, a changed row
\\ breaks leftInvOK, -kapT breaks the mu(T) identity in L42. The candidate is installed in the tree only after this run passes and the candidate compiles
\\ (sunit_data_install.sh, output sunit_data_install.out).
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/sunit_data_lean.gp < /dev/null > ../selmer-global-bound/sunit_data_lean.out 2>&1
default(parisizemax, 900 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
CAND = "/tmp/sb5/SUnitData.cand.lean";
DATA = "../selmer-global-bound/sunit_generators_data.gp";

ltup(v) = { my(s = "["); for (i = 1, #v, s = Str(s, if (i > 1, ", ", ""), "(", v[i][1], ", ", v[i][2], ")")); Str(s, "]"); }
wdef(F, doc, name, ty, val) = filewrite(F, Str("/-- ", doc, " -/\ndef ", name, " : ", ty, " :=\n  ", val, "\n"));
\\ one def per entry (name_0, name_1, ...), then the list of the entries
wentries(F, doc, name, ety, V) = {
  my(names = "[");
  for (i = 1, #V, filewrite(F, Str("def ", name, "_", i - 1, " : ", ety, " := ", V[i])); names = Str(names, if (i > 1, ", ", ""), name, "_", i - 1));
  filewrite(F, "");
  wdef(F, doc, name, Str("List (", ety, ")"), Str(names, "]"));
}

\\ residue data at (p, t): rho of the zk basis; rho of K21, L42, N84 (format of gN) elements
rhozk(zkNum, Dz, p, t) = vector(21, j, Mod(subst(Pol(Vecrev(zkNum[j]), 'b), 'b, t), p) / Dz);
rhoK(rz, a) = sum(j = 1, 21, a[j] * rz[j]);
rhoL(rz, sv, g) = rhoK(rz, g[1]) + sv * rhoK(rz, g[2]);
rhoN(rz, sv, tv, g) = rhoK(rz, g[1]) + sv * rhoK(rz, g[2]) + (rhoK(rz, g[3]) + sv * rhoK(rz, g[4])) * tv;
xorSel5(R, c) = { my(r = 0); for (j = 0, #R - 1, if (bittest(c, j), r = bitxor(r, R[j + 1]))); r; }
leftInvOK5(R, m, T) = { for (k = 0, m - 1, if (xorSel5(R, T[k + 1]) != 2^k, return(0))); 1; }
\\ the rows of the characters ch on the generators gens (kind 1: L, 2: N); -1 if a generator vanishes mod p
charrows(ch, gens, kind, zkNum, Dz) = {
  vector(#ch, j, my(d = ch[j], rz = rhozk(zkNum, Dz, d[1], d[2]), r = 0);
    for (s = 1, #gens, my(v = if (kind == 1, rhoL(rz, d[3], gens[s]), rhoN(rz, d[3], d[4], gens[s])));
      if (v == 0, return(-1));
      if (v^((d[1] - 1) / 2) == -1, r += 2^(s - 1)));
    r);
}

main() = {
  my(t0 = getabstime(), TW = read("/tmp/sb5/tower.bin"), GN = sb5_gens(DATA), PG = read("/tmp/sb5/pgen.bin"), CH = read("/tmp/sb5/chars.bin"), MU = read("/tmp/sb5/muT.bin"),
     genL, genN, gL, gN, gLw, gNw, gLab, gNab, F, sha);
  nfK = nfinit(K21); EPS = TW[1]; EN = TW[2];
  genL = GN[1]; genN = GN[2];
  gL = apply(g -> [Klist(g[1][1]), Klist(g[1][2])], genL);
  gN = apply(g -> vector(4, i, Klist(g[1][i])), genN);
  gLw = apply(g -> [Klist(g[4][1]), Klist(g[4][2])], genL);
  gNw = apply(g -> vector(4, i, Klist(g[4][i])), genN);
  gLab = apply(g -> g[5], genL); gNab = apply(g -> g[5], genN);
  chk5(gL == SB5_gL && gN == SB5_gN && gLw == SB5_gLw && gNw == SB5_gNw && gLab == SB5_gLab && gNab == SB5_gNab, "the generators of the data file sunit_generators_data.gp");
  chk5(#CH == 3 && #CH[2] == 6 && #PG == 5 && PG[5] == 2 * TW[22], "sources: tower.bin, pgen.bin (with the power tables, betaPowDen = 2 betaDen), chars.bin (6 defs)");
  system(Str("rm -f ", CAND));
  F = fileopen(CAND, "w");
  filewrite(F, "/-!\n# Data of the global generators (code/selmer-global-bound/sunit_data_lean.gp)\n");
  filewrite(F, "PARI/GP data of sb_5a (tower, roots), sb_5b (generators, cofactors; data file sunit_generators_data.gp), sb_5c\n(Pgen, power tables) and sb_5d (residue characters). Every datum below is rechecked from the text of this file\nby sunit_data_lean.gp (output sunit_data_lean.out). Lists are split into one def per entry (`gL_0`, ..., `gL_28`, then\n`gL := [gL_0, ..., gL_28]`), and likewise `gN`, `gLw`, `gNw`, `pgen`, `alphaPow`, `betaPow`.\n");
  filewrite(F, "Formats (frozen):\n");
  filewrite(F, "* `gL` (29 entries): `[a0, a1]`, zk lists of length 21: the generator `⟨zkE a0, zkE a1⟩` of `L42`.");
  filewrite(F, "* `gN` (53 entries): `[a0, a1, b0, b1]`: the generator `⟨⟨zkE a0, zkE a1⟩, ⟨2 zkE b0, 2 zkE b1⟩⟩`\n  of `N84`, i.e. `a0 + a1 ω + (b0 + b1 ω) (2 ω_N)`.");
  filewrite(F, "* `pgen` (82 entries) with `pgenDen`: the coefficients (constant term first, zk lists) of\n  `pgenDen s * Pgen s`, `Pgen s ∈ K21[X]` of degree at most 5.");
  filewrite(F, "* `alphaL = [a0, a1]`, `alphaDen`: `α = ⟨zkE a0, zkE a1⟩ / alphaDen ∈ L42`, a root of `q k`.");
  filewrite(F, "* `betaN = [a0, a1, b0, b1]`, `betaDen`: `β = ⟨⟨zkE a0, zkE a1⟩, ⟨zkE b0, zkE b1⟩⟩ / betaDen ∈ N84`,\n  a root of `h k`.\n");
  filewrite(F, "Membership certificates:\n");
  filewrite(F, "* `gLw` (29 entries, the format of `gL`) and `gLab` (29 pairs `(a, b)`): `mkL (gL s) * mkL (gLw s) = 2 ^ a * 7 ^ b`\n  in `L42`.");
  filewrite(F, "* `gNw` (53 entries, the format of `gN`) and `gNab` (53 pairs): `mkN (gN s) * mkN (gNw s) = 2 ^ a * 7 ^ b` in `N84`.\n");
  filewrite(F, "Power tables (evaluation of `Pgen s` at `α`, `β`):\n");
  filewrite(F, "* `alphaPow` (6 entries, the format of `gL`): `alphaPow i = (alphaDen α) ^ i`, so\n  `Pgen s (α) = ∑ i, pgen s i * alphaPow i / (pgenDen s * alphaDen ^ i)`.");
  filewrite(F, "* `betaPow` (6 entries, the format of `gN`) and `betaPowDen = 2 * betaDen`: `betaPow i = (betaPowDen β) ^ i`\n  (the coordinates `b` of `(betaDen β) ^ 1` in the format of `gN` are not all integral), so\n  `Pgen s (β) = ∑ i, pgen s i * betaPow i / (pgenDen s * betaPowDen ^ i)`.\n");
  filewrite(F, CH[1]);
  filewrite(F, "Certificate of `μ(T)` (mu_t_cert.gp; GlobalCRT.lean, `muT_components`), for `k = 0, 1`:\n\n* `kapT_k` (zk list), `kapTDen_k`: `κ = zkE kapT_k / kapTDen_k ∈ K21^×`; `aT_k`: 82 bits `a s`;\n  `y1T_k` (format of `gL`) over `y1TDen_k`, `y2T_k` (format of `gN`) over `y2TDen_k`: with `x1 = -c_k h(α)`,\n  `x2 = q(β)`, `x1 ∏_{s < 29} gensL_s ^ (a s) = κ y1²` and `x2 ∏_{s ≥ 29} gensN_(s - 29) ^ (a s) = κ y2²`.\n* `prodLT_k` (format of `gL`) `= ∏_{s < 29, a s = 1} gensL_s`, `prodNT_k` (format of `gN`) `= ∏_{s ≥ 29, a s = 1} gensN_(s - 29)`.\n* Checked identities (`A = alphaPow 1`, `B = betaPow 1`, `D_L = alphaDen`, `D_N = betaPowDen`):\n  `-(FE k 0) [∑ i, hL_i A^i D_L^(4-i)] prodLT kapTDen y1TDen² = 4 hDen D_L^4 kapT y1T²` and\n  `[∑ i, qL_i B^i D_N^(2-i)] prodNT kapTDen y2TDen² = qDen D_N² kapT y2T²`.\n");
  filewrite(F, "Every zk list has length exactly 21, every `pgen s` has exactly 6 coefficients, every generator is nonzero.\nOrder: `gL` is 28 LLL reduced S-units, then `-1`; `gN` is `-1`, then 52 LLL reduced S-units (the positions of the\np21_29 generators they replace, code/earlier-computations/prym_two_descent.gp); `Pgen s` for `s < 29` belongs to\n`gL s`, for `s ≥ 29` to `gN (s - 29)`.");
  filewrite(F, "-/\n\nnamespace FurioLombardo.Discharge.SelmerBasis.SUnitData\n");
  wentries(F, "The 29 generators of `L42`.", "gL", "List (List Int)", gL);
  wentries(F, "The 53 generators of `N84` (format `a0 + a1 ω + (b0 + b1 ω) (2 ω_N)`).", "gN", "List (List Int)", gN);
  wentries(F, "`pgenDen s * Pgen s`: 6 coefficients, constant term first.", "pgen", "List (List Int)", PG[1]);
  wdef(F, "The denominators of `Pgen`.", "pgenDen", "List Nat", Str(PG[2]));
  wdef(F, "`α · alphaDen`, a root of `q k` (`k = 0, 1`).", "alphaL", "List (List Int)", Str(TW[21]));
  wdef(F, "The denominator of `α`.", "alphaDen", "Nat", Str(TW[20]));
  wdef(F, "`β · betaDen` in plain coordinates `a0 + a1 ω + (b0 + b1 ω) ω_N`, a root of `h k`.", "betaN", "List (List Int)", Str(TW[23]));
  wdef(F, "The denominator of `β`.", "betaDen", "Nat", Str(TW[22]));
  wentries(F, "Cofactors: `mkL (gL s) * mkL (gLw s) = 2 ^ a * 7 ^ b`, `(a, b) = gLab s`.", "gLw", "List (List Int)", gLw);
  wdef(F, "Exponents `(a, b)` of the L cofactors.", "gLab", "List (Nat × Nat)", ltup(gLab));
  wentries(F, "Cofactors: `mkN (gN s) * mkN (gNw s) = 2 ^ a * 7 ^ b`, `(a, b) = gNab s`.", "gNw", "List (List Int)", gNw);
  wdef(F, "Exponents `(a, b)` of the N cofactors.", "gNab", "List (Nat × Nat)", ltup(gNab));
  wentries(F, "`alphaPow i = (alphaDen α) ^ i`, `i = 0..5`, in the format of `gL`.", "alphaPow", "List (List Int)", PG[3]);
  wdef(F, "The denominator of the table `betaPow`, `2 * betaDen`.", "betaPowDen", "Nat", Str(PG[5]));
  wentries(F, "`betaPow i = (betaPowDen β) ^ i`, `i = 0..5`, in the format of `gN`.", "betaPow", "List (List Int)", PG[4]);
  foreach (CH[2], d, wdef(F, d[1], d[2], d[3], d[4]));
  for (k = 0, 1, my(E = MU[k + 1]);
    wdef(F, Str("`κ` of the `μ(T)` certificate, twist ", k, " (zk numerators)."), Str("kapT_", k), "List Int", Str(E[1]));
    wdef(F, Str("Denominator of `κ`, twist ", k, "."), Str("kapTDen_", k), "Nat", Str(E[2]));
    wdef(F, Str("The 82 exponent bits of the `μ(T)` certificate, twist ", k, "."), Str("aT_", k), "List Nat", Str(E[3]));
    wdef(F, Str("`y1T_", k, " / y1TDen_", k, "` (format of `gL`): `x1 ∏ gensL^a = κ y1²`."), Str("y1T_", k), "List (List Int)", Str(E[4]));
    wdef(F, Str("Denominator of `y1`, twist ", k, "."), Str("y1TDen_", k), "Nat", Str(E[5]));
    wdef(F, Str("`y2T_", k, " / y2TDen_", k, "` (format of `gN`): `x2 ∏ gensN^a = κ y2²`."), Str("y2T_", k), "List (List Int)", Str(E[6]));
    wdef(F, Str("Denominator of `y2`, twist ", k, "."), Str("y2TDen_", k), "Nat", Str(E[7]));
    wdef(F, Str("`∏_{s < 29, a s = 1} gensL_s` (format of `gL`), twist ", k, "."), Str("prodLT_", k), "List (List Int)", Str(E[8]));
    wdef(F, Str("`∏_{s ≥ 29, a s = 1} gensN_(s - 29)` (format of `gN`), twist ", k, "."), Str("prodNT_", k), "List (List Int)", Str(E[9])));
  filewrite(F, "end FurioLombardo.Discharge.SelmerBasis.SUnitData");
  fileclose(F);
  printf("wrote the candidate %s (%s bytes, %s lines)\n", CAND, externstr(Str("wc -c < ", CAND))[1], externstr(Str("wc -l < ", CAND))[1]);
  \\ ---- recheck from the text of the candidate
  my(M = leandefs5(CAND), rgL, rgN, rpg, rpd, raL, raD, rbN, rbD, rgLw, rgLab, rgNw, rgNab, raP, rbP, rbPD, rchL, rchN, rRL, rTL, rRN, rTN, qD, hD, qDen, hDen, q, h, al, be, nbad);
  rgL = leanentries5(M, "gL", 29); rgN = leanentries5(M, "gN", 53); rpg = leanentries5(M, "pgen", 82); rpd = leanval5(M, "pgenDen");
  raL = leanval5(M, "alphaL"); raD = leanval5(M, "alphaDen"); rbN = leanval5(M, "betaN"); rbD = leanval5(M, "betaDen");
  rgLw = leanentries5(M, "gLw", 29); rgLab = leanval5(M, "gLab", 1); rgNw = leanentries5(M, "gNw", 53); rgNab = leanval5(M, "gNab", 1);
  raP = leanentries5(M, "alphaPow", 6); rbP = leanentries5(M, "betaPow", 6); rbPD = leanval5(M, "betaPowDen");
  rchL = leanval5(M, "chL"); rchN = leanval5(M, "chN"); rRL = leanval5(M, "RL"); rTL = leanval5(M, "TL"); rRN = leanval5(M, "RN"); rTN = leanval5(M, "TN");
  printf("the candidate has %d defs\n", #M);
  chk5(#M == 29 + 53 + 82 + 29 + 53 + 6 + 6 + 7 + 14 + 18, "the candidate has exactly the 297 expected defs (258 entries, 21 named data, 18 of the mu(T) certificates)");
  chk5(rgL == gL && rgN == gN && rpg == PG[1] && rpd == PG[2] && raL == TW[21] && raD == TW[20] && rbN == TW[23] && rbD == TW[22] && rgLw == gLw && rgNw == gNw && rgLab == gLab && rgNab == gNab
       && raP == PG[3] && rbP == PG[4] && rbPD == PG[5] && rchL == CH[3][1][2] && rchN == CH[3][2][2] && rRL == CH[3][1][1] && rTL == CH[3][3] && rRN == CH[3][2][1] && rTN == CH[3][4], "the candidate reads back to the source data");
  chk5(#rgL == 29 && #rgLw == 29 && #rgLab == 29 && #rgN == 53 && #rgNw == 53 && #rgNab == 53 && #rpg == 82 && #rpd == 82 && #raP == 6 && #rbP == 6
       && #rchL == 29 && #rRL == 29 && #rTL == 29 && #rchN == 53 && #rRN == 53 && #rTN == 53, "lengths: gL, gLw, gLab, chL, RL, TL 29; gN, gNw, gNab, chN, RN, TN 53; pgen, pgenDen 82; alphaPow, betaPow 6");
  chk5(vecmin(apply(g -> #g == 2 && #g[1] == 21 && #g[2] == 21, concat(concat(rgL, rgLw), raP))) && vecmin(apply(g -> #g == 4 && vecmin(apply(l -> #l == 21, g)), concat(concat(rgN, rgNw), rbP))), "every generator, cofactor, power: 2 (L) or 4 (N) zk lists of length exactly 21");
  chk5(vecmin(apply(P -> #P == 6 && vecmin(apply(l -> #l == 21, P)), rpg)) && vecmin(apply(d -> d > 0, rpd)), "every pgen s: 6 zk lists of length exactly 21; every pgenDen s > 0");
  chk5(#raL == 2 && #raL[1] == 21 && #raL[2] == 21 && #rbN == 4 && vecmin(apply(l -> #l == 21, rbN)) && raD > 0 && rbD > 0 && rbPD == 2 * rbD, "alphaL, betaN: zk lists of length 21; alphaDen, betaDen > 0; betaPowDen = 2 betaDen");
  qD = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qData"); hD = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hData");
  qDen = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qDen"); hDen = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hDen");
  al = [KofList(raL[1]) / raD, KofList(raL[2]) / raD]; be = vector(4, i, KofList(rbN[i]) / rbD);
  for (k = 1, 2,
    q = [KofList(qD[k][1]) / qDen[k], KofList(qD[k][2]) / qDen[k], Kc(1)];
    h = [KofList(hD[k][1]) / hDen[k], KofList(hD[k][2]) / hDen[k], KofList(hD[k][3]) / hDen[k], KofList(hD[k][4]) / hDen[k], Kc(1)];
    chk5(Lis0(Lev(q, al)) && Nis0(Nev(h, be)), Str("from the text: q ", k - 1, " (alpha) = 0 in L42, h ", k - 1, " (beta) = 0 in N84 (q k, h k of DataBruin.lean)")));
  \\ S-unit certificates
  my(sunitL = (G, W, AB) -> my(nb = 0); for (s = 1, #G, my(xl = [KofList(G[s][1]), KofList(G[s][2])], wl = [KofList(W[s][1]), KofList(W[s][2])]);
       if (Lis0(xl) || Lmul(xl, wl) != [Kc(2^AB[s][1] * 7^AB[s][2]), Kc(0)], nb++)); nb,
     sunitN = (G, W, AB) -> my(nb = 0); for (s = 1, #G, my(xn = Nunfmt(vector(4, i, KofList(G[s][i]))), wn = Nunfmt(vector(4, i, KofList(W[s][i]))));
       if (Nis0(xn) || Nmul(xn, wn) != NofK(2^AB[s][1] * 7^AB[s][2]), nb++)); nb);
  chk5(sunitL(rgL, rgLw, rgLab) == 0, "from the text: every gL s is nonzero and gL s * gLw s = 2^a 7^b in L42 (29 exact identities)");
  chk5(sunitN(rgN, rgNw, rgNab) == 0, "from the text: every gN s is nonzero and gN s * gNw s = 2^a 7^b in N84 (53 exact identities)");
  my(bgL = rgL, bgN = rgN); bgL[5][2][3] += 1; bgN[11][3][1] += 1;
  chk5(sunitL(bgL, rgLw, rgLab) == 1 && sunitN(bgN, rgNw, rgNab) == 1, "negative control: one coordinate of gL 4, of gN 10 changed by 1 breaks exactly that identity");
  \\ Pgen by Horner
  nbad = 0;
  for (s = 1, 82, my(cf = vector(6, i, KofList(rpg[s][i]) / rpd[s]), va = Lev(cf, al), vb = Nev(cf, be));
    if (s <= 29, if (va != [KofList(rgL[s][1]), KofList(rgL[s][2])] || vb != NofK(1), nbad++),
      if (va != [Kc(1), Kc(0)] || vb != Nunfmt(vector(4, i, KofList(rgN[s - 29][i]))), nbad++)));
  chk5(nbad == 0, "from the text: Pgen s (alpha) = gensL s, Pgen s (beta) = 1 (s < 29); Pgen s (alpha) = 1, Pgen s (beta) = gensN (s - 29) (s >= 29): 82 x 2 exact identities (Horner)");
  \\ power tables, step by step, and Pgen through them
  my(aPt = apply(v -> [KofList(v[1]), KofList(v[2])], raP), bPt = apply(v -> Nunfmt(vector(4, i, KofList(v[i]))), rbP), aI = [KofList(raL[1]), KofList(raL[2])], okp = 1);
  if (aPt[1] != [Kc(1), Kc(0)] || bPt[1] != NofK(1) || aPt[2] != aI || bPt[2] != Nsc(rbPD / rbD, vector(4, i, KofList(rbN[i]))), okp = 0);
  for (i = 2, 5, if (aPt[i + 1] != Lmul(aPt[i], aPt[2]) || bPt[i + 1] != Nmul(bPt[i], bPt[2]), okp = 0));
  chk5(okp, "from the text: alphaPow 0 = 1, alphaPow 1 = alphaL, alphaPow (i + 1) = alphaPow i * alphaPow 1; betaPow 0 = 1, betaPow 1 = (betaPowDen / betaDen) betaN, betaPow (i + 1) = betaPow i * betaPow 1");
  nbad = 0;
  for (s = 1, 82, my(c = vector(6, i, KofList(rpg[s][i])), la = [Kc(0), Kc(0)], nb = NofK(0), ta, tb);
    for (i = 1, 6, la = Ladd(la, Lsc(c[i] * raD^(6 - i), aPt[i])); nb = Nadd(nb, Nsc(c[i] * rbPD^(6 - i), bPt[i])));
    ta = if (s <= 29, [KofList(rgL[s][1]), KofList(rgL[s][2])], [Kc(1), Kc(0)]); tb = if (s <= 29, NofK(1), Nunfmt(vector(4, i, KofList(rgN[s - 29][i]))));
    if (la != Lsc(rpd[s] * raD^5, ta) || nb != Nsc(rpd[s] * rbPD^5, tb), nbad++));
  chk5(nbad == 0, "from the text: sum_i pgen s i alphaPow i alphaDen^(5-i) = pgenDen s alphaDen^5 Pgen s (alpha), the same at beta with betaPow, betaPowDen (82 x 2 exact identities)");
  \\ characters
  my(zkNum = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"), Dz = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz"), DB = leandef5(Str(LEAN, "M1/DataBezout.lean"), "DB"),
     fL = leandef5(Str(LEAN, "M1/Basic.lean"), "fL"), epsL = leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL"), eaL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL"),
     ebL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL"), okd = 1);
  foreach (concat(rchL, rchN), d, my(p = d[1], rz = rhozk(zkNum, Dz, p, d[2]));
    if (!isprime(p) || p == 2 || p == 7 || Dz % p == 0 || DB % p == 0 || subst(Pol(Vecrev(fL), 'X), 'X, Mod(d[2], p)) != 0 || Mod(d[3], p)^2 != rhoK(rz, epsL), okd = 0);
    if (#d == 4 && (d[4] % p == 0 || Mod(d[4], p)^2 != 2 * (rhoK(rz, eaL) + d[3] * rhoK(rz, ebL))), okd = 0));
  chk5(okd && vecmin(apply(d -> #d == 3, rchL)) && vecmin(apply(d -> #d == 4, rchN)), "from the text: every character datum is [p, t, s] (L) or [p, t, s, t2] (N), p an odd prime, p != 7, p prime to Dz and DB, fL(t) = 0, s^2 = rho(eps), t2 != 0, t2^2 = 2 (rho(ea) + s rho(eb)) mod p");
  my(cRL = charrows(rchL, rgL, 1, zkNum, Dz), cRN = charrows(rchN, rgN, 2, zkNum, Dz));
  chk5(cRL == rRL && cRN == rRN, "from the text: RL and RN are the rows of the characters on the generators of the text (bit s of row j iff rho_j(gen s)^((p-1)/2) = -1; no generator vanishes mod any chosen p)");
  chk5(vecmax(rRL) < 2^29 && vecmin(rRL) >= 0 && vecmax(rRN) < 2^53 && vecmin(rRN) >= 0 && vecmax(rTL) < 2^29 && vecmin(rTL) >= 0 && vecmax(rTN) < 2^53 && vecmin(rTN) >= 0, "row and inverse bitmasks below 2^29 (L), 2^53 (N)");
  chk5(leftInvOK5(rRL, 29, rTL) && leftInvOK5(rRN, 53, rTN), "from the text: leftInvOK RL 29 29 TL and leftInvOK RN 53 53 TN");
  my(bRN = rRN); bRN[17] = bitxor(bRN[17], 2^40);
  chk5(!leftInvOK5(bRN, 53, rTN), "negative control: RN with one bit flipped fails leftInvOK");
  \\ mu(T) certificates
  my(Fn = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "FnData"), negd = 0);
  for (k = 0, 1,
    my(kT = leanval5(M, Str("kapT_", k)), kD = leanval5(M, Str("kapTDen_", k)), aT = leanval5(M, Str("aT_", k)), y1 = leanval5(M, Str("y1T_", k)),
       y1D = leanval5(M, Str("y1TDen_", k)), y2 = leanval5(M, Str("y2T_", k)), y2D = leanval5(M, Str("y2TDen_", k)), pLT = leanval5(M, Str("prodLT_", k)),
       pNT = leanval5(M, Str("prodNT_", k)), pl, pn, KT, Y1, Y2, PL, PN, hL, qL, sL, sN, Ai, Bi, lhsL, rhsL, lhsN, rhsN, FE0 = KofList(Fn[k + 1][1]));
    chk5([kT, kD, aT, y1, y1D, y2, y2D, pLT, pNT] == MU[k + 1], Str("k = ", k, ": the mu(T) certificate reads back to muT.bin"));
    chk5(#kT == 21 && kD > 0 && #aT == 82 && vecmin(apply(e -> e == 0 || e == 1, aT)) && #y1 == 2 && #y1[1] == 21 && #y1[2] == 21 && y1D > 0 && #y2 == 4 && vecmin(apply(l -> #l == 21, y2)) && y2D > 0
         && #pLT == 2 && vecmin(apply(l -> #l == 21, pLT)) && #pNT == 4 && vecmin(apply(l -> #l == 21, pNT)), Str("k = ", k, ": shapes (kapT, zk lists of length 21, aT 82 bits in {0, 1}, denominators > 0)"));
    KT = KofList(kT); Y1 = [KofList(y1[1]), KofList(y1[2])]; Y2 = Nunfmt(vector(4, i, KofList(y2[i])));
    PL = [KofList(pLT[1]), KofList(pLT[2])]; PN = Nunfmt(vector(4, i, KofList(pNT[i])));
    chk5(KT != 0 && !Lis0(Y1) && !Nis0(Y2), Str("k = ", k, ": kappa, y1, y2 nonzero"));
    pl = [Kc(1), Kc(0)]; for (s = 1, 29, if (aT[s], pl = Lmul(pl, [KofList(rgL[s][1]), KofList(rgL[s][2])])));
    pn = NofK(1); for (s = 30, 82, if (aT[s], pn = Nmul(pn, Nunfmt(vector(4, i, KofList(rgN[s - 29][i]))))));
    chk5(pl == PL && pn == PN, Str("k = ", k, ": prodLT = prod_{s < 29, aT s = 1} gL s and prodNT = prod_{s >= 29, aT s = 1} gN (s - 29), products of the generators of the text"));
    hL = concat(vector(4, i, KofList(hD[k + 1][i])), [Kc(hDen[k + 1])]); qL = concat(vector(2, i, KofList(qD[k + 1][i])), [Kc(qDen[k + 1])]);
    sL = [Kc(0), Kc(0)]; Ai = [Kc(1), Kc(0)]; for (i = 0, 4, sL = Ladd(sL, Lsc(Km(hL[i + 1], raD^(4 - i)), Ai)); Ai = Lmul(Ai, aPt[2]));
    sN = NofK(0); Bi = NofK(1); for (i = 0, 2, sN = Nadd(sN, Nsc(Km(qL[i + 1], rbPD^(2 - i)), Bi)); Bi = Nmul(Bi, bPt[2]));
    lhsL = Lsc(Km(-FE0, kD * y1D^2), Lmul(sL, PL)); rhsL = Lsc(Km(4 * hDen[k + 1] * raD^4, KT), Lmul(Y1, Y1));
    lhsN = Nsc(kD * y2D^2, Nmul(sN, PN)); rhsN = Nsc(Km(qDen[k + 1] * rbPD^2, KT), Nmul(Y2, Y2));
    chk5(lhsL == rhsL, Str("k = ", k, ": -(FE k 0) [sum_i hL_i A^i D_L^(4-i)] prodLT kapTDen y1TDen^2 = 4 hDen D_L^4 kapT y1T^2 in L42 (A = alphaPow 1, D_L = alphaDen)"));
    chk5(lhsN == rhsN, Str("k = ", k, ": [sum_i qL_i B^i D_N^(2-i)] prodNT kapTDen y2TDen^2 = qDen D_N^2 kapT y2T^2 in N84 (B = betaPow 1, D_N = betaPowDen)"));
    if (Lsc(Km(4 * hDen[k + 1] * raD^4, -KT), Lmul(Y1, Y1)) != lhsL, negd++));
  chk5(negd == 2, "negative control: -kapT in place of kapT breaks the L42 identity (both twists)");
  printf("sizes: pgen %d digits, gN %d digits, gNw %d digits, betaPow %d digits (decimal digits of the integers)\n",
    sum(s = 1, 82, sum(i = 1, 6, sum(j = 1, 21, #Str(abs(rpg[s][i][j]))))), sum(s = 1, 53, sum(i = 1, 4, sum(j = 1, 21, #Str(abs(rgN[s][i][j]))))),
    sum(s = 1, 53, sum(i = 1, 4, sum(j = 1, 21, #Str(abs(rgNw[s][i][j]))))), sum(s = 1, 6, sum(i = 1, 4, sum(j = 1, 21, #Str(abs(rbP[s][i][j]))))));
  sha = externstr(Str("sha256sum ", CAND))[1];
  printf("candidate sha256 %s\n", sha);
  printf("DONE sunit_data_lean: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
