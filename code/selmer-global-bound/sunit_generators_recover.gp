\\ sunit_generators_recover.gp: recovers the 29 + 53 generators of sunit_generators.gp and their
\\ cofactors after the machine crash of 2026-09-28 21:08, which wiped /tmp (the cache /tmp/sb5/gens.bin of sb_5b and
\\ the p21_28 cache /tmp/k21c/nr/nsat.bin that sb_5b reads; rebuilding the latter costs p21_25 plus p21_28, about
\\ 37 min at 8 GB). Source: the Lean export written by sunit_data_lean.gp from that gens.bin at
\\ 2026-09-28 21:05, kept as /tmp/sb5_partial_SUnitData.lean (its sha256 is printed below).
\\ Checks. (1) Shapes: 29 and 53 generators and cofactors, every zk list of length 21. (2) Exact, in the tower
\\ (tower_lib.gp): every generator nonzero and x w = 2^a 7^b with (a, b) = gLab, gNab (so x is an S-unit). (3) The
\\ fingerprints recorded by the sb_5b run in sunit_generators.out: the coordinate and cofactor bit sizes per generator, the
\\ exponents (a, b), and per element |N_{F/Q}(x)| = 2^(n2 + d B2) 7^(n7 + d B7) with 2^n2 7^n7 the recorded norm of the
\\ recovered element, 2^B2 7^B7 its recorded scaling and d = 42, 84. Then the data file sunit_generators_data.gp is written
\\ (gp syntax, SB5_gL, SB5_gN, SB5_gLw, SB5_gNw, SB5_gLab, SB5_gNab in the Lean formats) and read back. The later
\\ stages read the generators from that file (sb5_gens of tower_lib.gp); the independence modulo squares is proved
\\ again from scratch by residue_characters.gp.
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/sunit_generators_recover.gp < /dev/null > ../selmer-global-bound/sunit_generators_recover.out 2>&1
default(parisizemax, 900 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
SRC = "/tmp/sb5_partial_SUnitData.lean";
REC = "../selmer-global-bound/sunit_generators.out";
DATA = "../selmer-global-bound/sunit_generators_data.gp";

\\ the integers after "^" in the tokens of a line (tokens such as "+-2^3", "7^0:", "2^-1")
powexps(line) = {
  my(res = List());
  foreach (strsplit(line, " "), tk, my(v = Vecsmall(tk), j = 0);
    for (i = 1, #v, if (v[i] == 94, j = i; break));
    if (j, my(k = j + 1, sg = 1, n = 0, nd = 0);
      if (k <= #v && v[k] == 45, sg = -1; k++);
      while (k <= #v && v[k] >= 48 && v[k] <= 57, n = 10 * n + v[k] - 48; nd++; k++);
      if (nd, listput(res, sg * n))));
  Vec(res);
}
\\ the value of the recorded summary line beginning with prefix (the text after the prefix is a gp vector)
recline(R, prefix) = {
  my(hit = []);
  foreach (R, l, if (strprefix5(l, prefix), hit = concat(hit, [l])));
  if (#hit != 1, error("recline: ", #hit, " lines with prefix ", prefix));
  eval(Strchr(Vecsmall(hit[1])[#Vecsmall(prefix) + 1 .. #Vecsmall(hit[1])]));
}
\\ recorded per element data of one section (L or N) of the sb_5b output: [norm exponents, scaling exponents] per element
recelems(R, i0, i1, m) = {
  my(nm = vector(m), sc = vector(m), fl = vector(m, k, [0, 0]));
  for (i = i0, i1, my(l = R[i], wds = strsplit(l, " "));
    if (#wds >= 4 && wds[1] == "ok:" && wds[2] == "element",
      my(k = eval(strsplit(wds[3], ":")[1]));
      if (wds[4] == "norm", nm[k] = powexps(l); fl[k][1]++);
      if (wds[4] == "scaled", sc[k] = powexps(l)[1 .. 2]; fl[k][2]++)));
  for (k = 1, m, if (fl[k] != [1, 1], error("recelems: element ", k, " incomplete")));
  [nm, sc];
}

main() = {
  my(t0 = getabstime(), fL, epsL, eaL, ebL, sha, M, gL, gN, gLw, gNw, gLab, gNab, R, iN, rL, rN, bad);
  \\ ---- the tower
  fL = leandef5(Str(LEAN, "M1/Basic.lean"), "fL");
  chk5(Pol(Vecrev(fL), 'b) == K21, "M1's fL is K21");
  nfK = nfinit(K21);
  my(zkNum = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"), Dz = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz"));
  chk5(vector(21, j, Pol(Vecrev(zkNum[j]), 'b) / Dz) == nfK.zk, "nfK.zk equals M1's zkNum / Dz");
  epsL = leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL");
  eaL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL"); ebL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL");
  EPS = KofList(epsL); EN = [KofList(eaL) / 2, KofList(ebL) / 2];
  \\ ---- tool tests
  chk5(powexps("ok: element 4: norm +-2^3 7^0") == [3, 0] && powexps("scaled by 2^-1 7^2: x") == [-1, 2] && powexps("no powers") == [], "tool: powexps reads the exponents of a recorded line (signs, no match)");
  my(TM = Map()); mapput(TM, "e", " [e_0, e_1]"); mapput(TM, "e_0", " [1, -2]"); mapput(TM, "e_1", " [[3, 4]]");
  chk5(leanentries5(TM, "e", 2) == [[1, -2], [[3, 4]]], "tool: leanentries5 reads the entries of a split list");
  chk5(iferr(leanentries5(TM, "e", 3); 0, E, 1), "tool: leanentries5 rejects a wrong entry count (negative control)");
  \\ ---- the source
  chk5(#externstr(Str("ls ", SRC, " 2>/dev/null")) == 1, "the source file exists");
  sha = externstr(Str("sha256sum ", SRC))[1];
  printf("source %s\n", sha);
  M = leandefs5(SRC);
  gL = leanval5(M, "gL"); gN = leanval5(M, "gN"); gLw = leanval5(M, "gLw"); gNw = leanval5(M, "gNw");
  gLab = leanval5(M, "gLab", 1); gNab = leanval5(M, "gNab", 1);
  \\ ---- (1) shapes
  chk5(#gL == 29 && #gLw == 29 && #gLab == 29 && #gN == 53 && #gNw == 53 && #gNab == 53, "29 L generators, cofactors, exponents; 53 N generators, cofactors, exponents");
  chk5(vecmin(apply(g -> #g == 2 && #g[1] == 21 && #g[2] == 21, concat(gL, gLw))) && vecmin(apply(g -> #g == 4 && vecmin(apply(v -> #v == 21, g)), concat(gN, gNw))), "every entry has 2 (L) or 4 (N) zk lists, every zk list of length 21");
  chk5(vecmin(apply(e -> #e == 2 && e[1] >= 0 && e[2] >= 0, concat(gLab, gNab))), "every (a, b) is a pair of naturals");
  \\ ---- (2) exact S-unit certificates in the tower
  bad = 0;
  for (s = 1, 29, my(xl = [KofList(gL[s][1]), KofList(gL[s][2])], wl = [KofList(gLw[s][1]), KofList(gLw[s][2])]);
    if (Lis0(xl) || Lmul(xl, wl) != [Kc(2^gLab[s][1] * 7^gLab[s][2]), Kc(0)], bad++));
  chk5(bad == 0, "L: every generator x is nonzero and x w = 2^a 7^b in L42 (29 exact identities)");
  bad = 0;
  for (s = 1, 53, my(xn = Nunfmt(vector(4, i, KofList(gN[s][i]))), wn = Nunfmt(vector(4, i, KofList(gNw[s][i]))));
    if (Nis0(xn) || Nmul(xn, wn) != NofK(2^gNab[s][1] * 7^gNab[s][2]), bad++));
  chk5(bad == 0, "N: every generator x is nonzero and x w = 2^a 7^b in N84 (53 exact identities, Lean format b = c / 2)");
  chk5(gL[29] == [Vec(Kc(-1)), Vec(Kc(0))] && gN[1] == [Vec(Kc(-1)), Vec(Kc(0)), Vec(Kc(0)), Vec(Kc(0))], "gL 28 and gN 0 are -1 (the order of sb_5b)");
  \\ ---- (3) fingerprints recorded by sb_5b
  R = readstr(REC);
  chk5(#[l | l <- R, strprefix5(l, "DONE sunit_generators: 733 checks passed, 0 failed")] == 1, "sunit_generators.out is a complete passing run (DONE, 733 checks, 0 failed)");
  my(Lx = apply(g -> [Col(g[1]), Col(g[2])], gL), Lw = apply(g -> [Col(g[1]), Col(g[2])], gLw), Nx = apply(g -> vector(4, i, Col(g[i])), gN), Nw = apply(g -> vector(4, i, Col(g[i])), gNw));
  chk5(apply(bits5, Lx) == recline(R, "L: format coordinate bits per generator "), "L: the coordinate bit sizes per generator equal the recorded ones");
  chk5(apply(bits5, Lw) == recline(R, "L: cofactor bits "), "L: the cofactor bit sizes equal the recorded ones");
  chk5(gLab == recline(R, "L: (a, b) of x w = 2^a 7^b: "), "L: the exponents (a, b) equal the recorded ones");
  chk5(apply(bits5, Nx) == recline(R, "N: format coordinate bits per generator "), "N: the coordinate bit sizes per generator equal the recorded ones");
  chk5(apply(bits5, Nw) == recline(R, "N: cofactor bits "), "N: the cofactor bit sizes equal the recorded ones");
  chk5(gNab == recline(R, "N: (a, b) of x w = 2^a 7^b: "), "N: the exponents (a, b) equal the recorded ones");
  iN = 0; for (i = 1, #R, if (strprefix5(R[i], "N: complex logs"), iN = i; break));
  chk5(iN > 0, "the recorded output has an L section and an N section");
  rL = recelems(R, 1, iN, 28); rN = recelems(R, iN, #R, 52);
  bad = 0;
  for (k = 1, 28, my(nm = abs(nfeltnorm(nfK, Lnorm(Lx[k])))); if (nm != 2^(rL[1][k][1] + 42 * rL[2][k][1]) * 7^(rL[1][k][2] + 42 * rL[2][k][2]), bad++));
  chk5(bad == 0, "L: |N_{L/Q}(gL s)| = 2^(n2 + 42 B2) 7^(n7 + 42 B7) with the recorded norm and scaling of element s + 1 (28 elements)");
  bad = 0;
  for (k = 1, 52, my(nm = abs(nfeltnorm(nfK, NnormK(Nunfmt(Nx[k + 1]))))); if (nm != 2^(rN[1][k][1] + 84 * rN[2][k][1]) * 7^(rN[1][k][2] + 84 * rN[2][k][2]), bad++));
  chk5(bad == 0, "N: |N_{N/Q}(gN s)| = 2^(n2 + 84 B2) 7^(n7 + 84 B7) with the recorded norm and scaling of element s (52 elements)");
  \\ negative control of the norm fingerprint: a swap of two generators is detected
  my(nm2 = abs(nfeltnorm(nfK, Lnorm(Lx[4]))));
  chk5(nm2 != 2^(rL[1][6][1] + 42 * rL[2][6][1]) * 7^(rL[1][6][2] + 42 * rL[2][6][2]), "negative control: the norm of gL 3 differs from the recorded norm of element 6");
  \\ ---- the data file
  system(Str("rm -f ", DATA));
  write(DATA, "\\\\ sunit_generators_data.gp: the 29 + 53 generators of L42(S,2), N84(S,2) (sunit_generators.gp) and their cofactors, written");
  write(DATA, "\\\\ by sunit_generators_recover.gp (see its header and output). Formats of SUnitData.lean: SB5_gL, SB5_gLw entries [a0, a1],");
  write(DATA, "\\\\ SB5_gN, SB5_gNw entries [a0, a1, b0, b1] (a0 + a1 om + (b0 + b1 om) (2 on)), zk lists of length 21;");
  write(DATA, "\\\\ SB5_gLab, SB5_gNab the exponents (a, b) with x w = 2^a 7^b.");
  my(wlist = (nm, V) -> write(DATA, Str("{", nm, " = [")); for (s = 1, #V, write(DATA, Str(V[s], if (s < #V, ",", "];}")))));
  wlist("SB5_gL", gL); wlist("SB5_gLw", gLw); wlist("SB5_gLab", gLab);
  wlist("SB5_gN", gN); wlist("SB5_gNw", gNw); wlist("SB5_gNab", gNab);
  my(GG = sb5_gens(DATA));
  chk5(SB5_gL == gL && SB5_gN == gN && SB5_gLw == gLw && SB5_gNw == gNw && SB5_gLab == gLab && SB5_gNab == gNab, "the data file reads back equal");
  chk5(GG[1][5][1] == Lx[5] && GG[2][7][4] == Nw[7] && GG[2][9][5] == gNab[9], "sb5_gens returns the sb_5b layout (coordinates, cofactor, exponents)");
  printf("data file: %s bytes, sha256 %s\n", externstr(Str("wc -c < ", DATA))[1], externstr(Str("sha256sum ", DATA))[1]);
  printf("DONE sunit_generators_recover: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
