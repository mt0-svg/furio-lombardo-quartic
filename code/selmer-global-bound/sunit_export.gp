\\ sunit_export.gp: writes the gp data file sunit_export_data.gp for the local
\\ side, then reads it back and rechecks it from its own text.
\\ Contents (all variables SBX_*, formats in the header of the data file): the 82 polynomials Pgen s (sb_5c; the same
\\ integers as pgen, pgenDen of SUnitData.lean), the local coordinate system of p21_29 (offsets, images KM_w of K_w^x,
\\ local images W_w per twist), the 164 x 82 matrix G of the new generators, per twist the Selmer space X, the D basis
\\ at v (Dpt order), SB, beta_j, and a_T with its kappa (sb_5t), and kappa_t (t = 0..15) with M1's gO 0..15 (sb_5e).
\\ Checks on the text read back: (a) it equals the checked caches (pgen.bin, selmer.bin, muT.bin, ss_1_data) and the
\\ text of SUnitData.lean (pgen, pgenDen, aT_k, kapT_k, kapTDen_k); (b) Pgen s (alpha), Pgen s (beta) by Horner in the
\\ tower, with alpha, beta, gL, gN from the text of SUnitData.lean and eps, eN from M3b (82 x 2 exact identities);
\\ (c) the F_2 statements from the matrices of the file alone: rank G = 82; X = the kernel of the local conditions
\\ (dim 19); D basis and KM_v span W_v; beta_j in X with res_v(G beta_j) = D SB_j modulo KM_v; kappa_t in X and
\\ trivial modulo KM_w at every place, rank 15, relation kapRel; span(beta, kappa) = X; a_T in X.
\\ Negative controls: a flipped bit of beta_0 (k = 0) and a changed Pgen coefficient fail (c) and (b).
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/sunit_export.gp < /dev/null > ../selmer-global-bound/sunit_export.out 2>&1
default(parisizemax, 1700 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
SUD = Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean");
OUTF = "../selmer-global-bound/sunit_export_data.gp";

f2rank(M) = if (#M == 0, 0, matrank(Mod(M, 2)));
f2in(M, v) = f2rank(matconcat([M, v])) == f2rank(M);
f2eqspan(A1, A2) = my(r = f2rank(A1)); r == f2rank(A2) && r == f2rank(matconcat([A1, A2]));
f2annih(W, n) = { if (#W == 0, return(matid(n))); my(Kr = lift(matker(Mod(W~, 2)))); if (#Kr == 0, matrix(0, n), Kr~); }
rowblock(M, o) = matrix(o[2], #M, r, c, M[o[1] + r, c]);
embed(Kj, o, n) = matconcat([matrix(o[1], #Kj); Kj; matrix(n - o[1] - o[2], #Kj)]);
Xker(G, offs, W) = { my(R = matrix(0, #G)); for (j = 1, #offs, R = matconcat([R; f2annih(W[j], offs[j][2]) * rowblock(G, offs[j])])); lift(matker(Mod(R, 2))); }
\\ the F_2 checks (c) on data in the layout of the file; returns the number of failed statements, printing each
f2checks(G, offs, KM, W, Xs, D, SB, bet, kap, rel, aT, verbose) = {
  my(nf = 0, n = #G~, KMbar = matconcat(vector(#offs, j, embed(KM[j], offs[j], n))), ck = ((c, m) -> if (!c && verbose, printf("  fails: %s\n", m)); !c));
  nf += ck(f2rank(G) == 82 && n == 164 && offs[#offs][1] + offs[#offs][2] == n, "rank G = 82, 164 coordinates");
  nf += ck(f2rank(kap) == 15 && (kap * rel) % 2 == 0 && rel != 0, "rank kappa = 15, kappa rel = 0");
  for (k = 1, 2, my(Xk = Xker(G, offs, W[k]), Bv = matconcat([D[k], KM[1]]), Rv = rowblock(G, offs[1]));
    nf += ck(#Xk == 19 && f2eqspan(Xk, Xs[k]), Str("k = ", k - 1, ": X is the kernel of the local conditions, dim 19"));
    nf += ck(f2rank(Bv) == 7 + f2rank(KM[1]) && f2eqspan(Bv, W[k][1]), Str("k = ", k - 1, ": D and KM_v independent, spanning W_v"));
    for (j = 1, 4, nf += ck(f2in(Xs[k], bet[k][, j]) && f2in(KM[1], (Rv * bet[k][, j] - D[k] * SB[k][, j]) % 2), Str("k = ", k - 1, ": beta_", j - 1, " in X, res_v(G beta) = D SB_", j - 1, " mod KM_v")));
    nf += ck(vecmin(vector(16, tt, f2in(Xs[k], kap[, tt]) && f2in(KMbar, G * kap[, tt] % 2))), Str("k = ", k - 1, ": kappa_t in X and trivial modulo KM_w everywhere"));
    nf += ck(f2eqspan(matconcat([bet[k], kap]), Xs[k]), Str("k = ", k - 1, ": span(beta, kappa) = X"));
    nf += ck(f2in(Xs[k], aT[k]~), Str("k = ", k - 1, ": a_T in X")));
  nf;
}

main() = {
  my(t0 = getabstime(), PG = read("/tmp/sb5/pgen.bin"), SE = read("/tmp/sb5/selmer.bin"), MU = read("/tmp/sb5/muT.bin"),
     SD = vector(2, k, read(Str("../local-group/selmer_injectivity_places_twist", k - 1, ".bin"))), gO = leandef5(Str(LEAN, "M1/DataGens.lean"), "gensL"), F, wr);
  chk5(SD[1][2] == SD[2][2] && SD[1][4] == SD[2][4] && SD[1][5] == SD[2][5], "ss_1_data: offsets, KM_w and place names are the same for both twists");
  chk5(#PG[1] == 82 && #PG[2] == 82 && #SE[5] == 2 && #gO == 18, "inputs: 82 Pgen (pgen.bin), both twists (selmer.bin), 18 gO (M1)");
  system(Str("rm -f ", OUTF));
  chk5(#externstr(Str("ls ", OUTF, " 2>/dev/null")) == 0, "the old export file is removed");
  wr = (s -> write(OUTF, s));
  foreach ([
    "\\\\ sunit_export_data.gp: data of the global generators for the local side, written by",
    "\\\\ sunit_export.gp (output sunit_export.out, which rechecks this file from its text). Read with read(\"sunit_export_data.gp\").",
    "\\\\ Twist index k = 1, 2 in gp stands for the twist k = 0, 1 of the Lean files. Generator index s = 1..82 in gp stands",
    "\\\\ for s = 0..81 of SUnitData.lean (s <= 29: gL (s - 1), s >= 30: gN (s - 30)). Bit vectors are 0/1 entries.",
    "\\\\ SBX_pgen[s] (6 zk lists of length 21, constant term first), SBX_pgenDen[s]: Pgen (s - 1) = (1 / SBX_pgenDen[s])",
    "\\\\   sum_i zkE(SBX_pgen[s][i + 1]) T^i, the integers pgen, pgenDen of SUnitData.lean (zkE: M1's integral basis",
    "\\\\   of K21); Pgen(alpha) = gL (s - 1), Pgen(beta) = 1 for s <= 29, Pgen(alpha) = 1, Pgen(beta) = gN (s - 30) otherwise.",
    "\\\\ Local coordinates (code/earlier-computations/prym_two_descent.gp, td2loc.gp): 164 coordinates, place j in rows",
    "\\\\   SBX_offs[j][1] + 1 .. SBX_offs[j][1] + SBX_offs[j][2]; places 1..4 finite (SBX_places), 5..7 real; place 1 is v.",
    "\\\\ SBX_KM[j]: basis (columns) of the image of K_w^x at place j. SBX_W[k][j]: the local image W_w (columns).",
    "\\\\ SBX_G: 164 x 82, column s = the coordinates of the generator s (of Pgen (s - 1)(T) in K21[T]/(fRev k) = L42 x N84).",
    "\\\\ SBX_X[k]: 82 x 19, a basis of X = {x : res_w(G x) in W_w for all w} (the Selmer space on the generators).",
    "\\\\ SBX_D[k]: 22 x 7, column i = the coordinates at v of (U_i(alpha), U_i(beta)), U_i the polynomial of Dpt k (i - 1).",
    "\\\\ SBX_SB[k]: 7 x 4, T_k.data.SB of lean/FurioLombardo/M4/Data.lean.",
    "\\\\ SBX_beta[k]: 82 x 4, column j = beta_(j - 1): in X, res_v(G beta) = SBX_D[k] SB_j modulo SBX_KM[1] (RelAtV at v).",
    "\\\\ SBX_kappa: 82 x 16, column t = the class of (c, c), c = SBX_gO[t] (M1's gO (t - 1), t = 1..16), on the",
    "\\\\   generators; SBX_kapRel: the relation (the class of eps). SBX_aT[k]: 82 bits of mu(T); SBX_kapT[k] = [zk list, den]",
    "\\\\   of its kappa: x1 prod gensL^a = kappa y1^2, x2 prod gensN^a = kappa y2^2 (SUnitData.lean aT_k, kapT_k, kapTDen_k)."], l, wr(l));
  wr("{SBX_pgen = ["); for (s = 1, 82, wr(Str(PG[1][s], if (s < 82, ",", "")))); wr("];}");
  wr(Str("SBX_pgenDen = ", PG[2], ";"));
  wr(Str("SBX_offs = ", SD[1][2], ";"));
  wr(Str("SBX_places = ", concat(SD[1][5], ["real 1", "real 2", "real 3"]), ";"));
  wr(Str("SBX_KM = ", SD[1][4], ";"));
  wr(Str("SBX_W = ", [SD[1][3], SD[2][3]], ";"));
  wr(Str("SBX_G = ", SE[1], ";"));
  wr(Str("SBX_X = ", [SE[5][1][1], SE[5][2][1]], ";"));
  wr(Str("SBX_D = ", [SE[5][1][5], SE[5][2][5]], ";"));
  wr(Str("SBX_SB = ", [SE[5][1][4], SE[5][2][4]], ";"));
  wr(Str("SBX_beta = ", [SE[5][1][2], SE[5][2][2]], ";"));
  wr(Str("SBX_kappa = ", SE[3], ";"));
  wr(Str("SBX_kapRel = ", SE[4][, 1], ";"));
  wr(Str("SBX_gO = ", gO[1 .. 16], ";"));
  wr(Str("SBX_aT = ", [MU[1][3], MU[2][3]], ";"));
  wr(Str("SBX_kapT = ", [[MU[1][1], MU[1][2]], [MU[2][1], MU[2][2]]], ";"));
  printf("wrote %s: %s bytes, %s lines\n", "sunit_export_data.gp", externstr(Str("wc -c < ", OUTF))[1], externstr(Str("wc -l < ", OUTF))[1]);
  \\ ---- read back
  read(OUTF);
  \\ (a) equality with the checked data
  chk5(SBX_pgen == PG[1] && SBX_pgenDen == PG[2], "read back: SBX_pgen, SBX_pgenDen equal pgen.bin (sb_5c)");
  chk5(SBX_G == SE[1] && SBX_kappa == SE[3] && SBX_kapRel == SE[4][, 1] && vector(2, k, SBX_X[k] == SE[5][k][1] && SBX_beta[k] == SE[5][k][2] && SBX_SB[k] == SE[5][k][4] && SBX_D[k] == SE[5][k][5]) == [1, 1],
       "read back: G, X, D, SB, beta, kappa, kapRel equal selmer.bin (sb_5e)");
  chk5(SBX_offs == SD[1][2] && SBX_KM == SD[1][4] && SBX_W == [SD[1][3], SD[2][3]], "read back: offsets, KM_w, W_w equal selmer_injectivity_places_twist0.bin, _twist1.bin");
  chk5(SBX_aT == [MU[1][3], MU[2][3]] && SBX_kapT == [[MU[1][1], MU[1][2]], [MU[2][1], MU[2][2]]] && SBX_gO == gO[1 .. 16], "read back: a_T, kapT equal muT.bin (sb_5t); SBX_gO = M1's gO 0..15");
  my(M = leandefs5(SUD));
  chk5(leanentries5(M, "pgen", 82) == SBX_pgen && leanval5(M, "pgenDen") == SBX_pgenDen, "SBX_pgen, SBX_pgenDen equal pgen, pgenDen of the text of SUnitData.lean");
  chk5(vector(2, k, leanval5(M, Str("aT_", k - 1)) == SBX_aT[k] && leanval5(M, Str("kapT_", k - 1)) == SBX_kapT[k][1] && leanval5(M, Str("kapTDen_", k - 1)) == SBX_kapT[k][2]) == [1, 1],
       "SBX_aT, SBX_kapT equal aT_k, kapT_k, kapTDen_k of the text of SUnitData.lean");
  \\ (b) Pgen by Horner from texts only
  my(fL = leandef5(Str(LEAN, "M1/Basic.lean"), "fL"), epsL = leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL"),
     eaL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL"), ebL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL"),
     raL = leanval5(M, "alphaL"), raD = leanval5(M, "alphaDen"), rbN = leanval5(M, "betaN"), rbD = leanval5(M, "betaDen"), rgL = leanentries5(M, "gL", 29), rgN = leanentries5(M, "gN", 53),
     al, be, horner);
  nfK = nfinit(Pol(Vecrev(fL), 'b)); EPS = Col(epsL); EN = [Col(eaL) / 2, Col(ebL) / 2];
  al = [KofList(raL[1]) / raD, KofList(raL[2]) / raD]; be = vector(4, i, KofList(rbN[i]) / rbD);
  horner = ((PGl, PGd) -> my(nb = 0); for (s = 1, 82, my(cf = vector(6, i, KofList(PGl[s][i]) / PGd[s]), va = Lev(cf, al), vb = Nev(cf, be));
    if (s <= 29, if (va != [KofList(rgL[s][1]), KofList(rgL[s][2])] || vb != NofK(1), nb++),
      if (va != [Kc(1), Kc(0)] || vb != Nunfmt(vector(4, i, KofList(rgN[s - 29][i]))), nb++))); nb);
  chk5(horner(SBX_pgen, SBX_pgenDen) == 0, "from the texts: Pgen s (alpha) = gL s, Pgen s (beta) = 1 (s < 29), Pgen s (alpha) = 1, Pgen s (beta) = gN (s - 29) (s >= 29), with SBX_pgen and alpha, beta, gL, gN of SUnitData.lean: 82 x 2 exact identities");
  my(bp = SBX_pgen); bp[40][4][7] += 1;
  chk5(horner(bp, SBX_pgenDen) == 1, "negative control: one coefficient of Pgen 39 changed by 1 breaks exactly that polynomial");
  \\ (c) F_2 statements from the file alone
  chk5(f2checks(SBX_G, SBX_offs, SBX_KM, SBX_W, SBX_X, SBX_D, SBX_SB, SBX_beta, SBX_kappa, SBX_kapRel, SBX_aT, 1) == 0,
       "from the file alone: rank G = 82; per twist X = kernel of the local conditions (dim 19), D and KM_v span W_v, beta_j in X with res_v(G beta_j) = D SB_j mod KM_v, kappa_t in X and trivial mod KM_w, span(beta, kappa) = X, a_T in X; rank kappa = 15 with relation kapRel");
  my(bb = SBX_beta); bb[1][1, 1] = 1 - bb[1][1, 1];
  chk5(f2checks(SBX_G, SBX_offs, SBX_KM, SBX_W, SBX_X, SBX_D, SBX_SB, bb, SBX_kappa, SBX_kapRel, SBX_aT, 0) > 0, "negative control: beta_0 (k = 0) with bit 0 flipped fails the F_2 checks");
  printf("sizes: pgen %d integers (%d decimal digits), G %d x %d, X 82 x 19, beta 82 x 4 (weights %s, %s), kappa 82 x 16\n", 82 * 6 * 21,
    sum(s = 1, 82, sum(i = 1, 6, sum(j = 1, 21, #Str(abs(SBX_pgen[s][i][j]))))), #SBX_G~, #SBX_G, vector(4, j, vecsum(SBX_beta[1][, j])), vector(4, j, vecsum(SBX_beta[2][, j])));
  printf("sha256 of sunit_export_data.gp: %s\n", externstr(Str("sha256sum ", OUTF, " | cut -c1-64"))[1]);
  printf("DONE sunit_export: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
