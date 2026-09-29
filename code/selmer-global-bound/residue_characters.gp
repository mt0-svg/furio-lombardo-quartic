\\ residue_characters.gp: residue characters that certify the
\\ independence modulo squares of the 29 generators of L42 and the 53 of N84 (the format of the Lean files):
\\ per field a list of odd primes p != 7 dividing neither Dz nor DB (of M1), with
\\   t: a root of M1's fL mod p (resHom sends theta to t), rho(zkE a) = Dz^-1 evalL t (combo a zkNum) mod p;
\\   s: s^2 = rho(eps) mod p, rho_L(a0 + a1 om) = rho(a0) + s rho(a1);
\\   (N only) t2 != 0: t2^2 = rho_L(2 ea + 2 eb om) = 2 (rho(ea) + s rho(eb)) (the image of 2 on, (2 on)^2 = 4 eN),
\\   rho_N(a0 + a1 om + (b0 + b1 om)(2 on)) = rho_L(a0 + a1 om) + rho_L(b0 + b1 om) t2.
\\ Rows RL, RN (Nat bitmasks): bit s of row j is set iff rho_j(gen s)^((p-1)/2) = -1; every generator is nonzero
\\ modulo every chosen prime. Left inverses TL, TN: the XOR of the rows R j over the set bits j of T k is 2^k
\\ (Echelon.lean's leftInvOK R r m T). Choice: primes in increasing order, the first candidate (t, +-s, +-t2) whose
\\ row raises the F2 rank, one character per prime, until the rank is 29 (L), 53 (N).
\\ Reads the generators from the data file sunit_generators_data.gp (the lists exported to SUnitData.lean by sb_5w, which
\\ rechecks the characters from the Lean text) and M1's data from DataField.lean, DataBezout.lean. Tool test: the
\\ residue maps rho_L, rho_N are multiplicative on products computed with the tower arithmetic of tower_lib.gp.
\\ Output cache /tmp/sb5/chars.bin (read by sunit_data_lean.gp). Run from code/earlier-computations:
\\   gp -q ../selmer-global-bound/residue_characters.gp < /dev/null > ../selmer-global-bound/residue_characters.out 2>&1
default(parisizemax, 900 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
DATA = "../selmer-global-bound/sunit_generators_data.gp";
OUT = "/tmp/sb5/chars.bin";

\\ F2 rows as bitmasks: xorSel as in Echelon.lean
xorSel5(R, c) = { my(r = 0); for (j = 0, #R - 1, if (bittest(c, j), r = bitxor(r, R[j + 1]))); r; }
leftInvOK5(R, m, T) = { for (k = 0, m - 1, if (xorSel5(R, T[k + 1]) != 2^k, return(0))); 1; }
rowvec(r, m) = vector(m, s, bittest(r, s - 1));

\\ the residue data at (p, t): rho of the zk basis
rhozk(zkNum, Dz, p, t) = vector(21, j, Mod(subst(Pol(Vecrev(zkNum[j]), 'b), 'b, t), p) / Dz);
rhoK(rz, a) = sum(j = 1, 21, a[j] * rz[j]);

\\ greedy choice of characters. gens: generator coordinate lists; val(rz, s, t2, g) the residue of g;
\\ kind 1 (L) or 2 (N)
choose(gens, kind, zkNum, Dz, DB, fL, epsL, eaL, ebL) = {
  my(m = #gens, rows = List(), data = List(), rk = 0, p = 2, M = matrix(0, m));
  while (rk < m, p = nextprime(p + 1);
    if (p == 7 || Dz % p == 0 || DB % p == 0, next);
    my(ts = polrootsmod(Pol(Vecrev(fL), 'X), p), done = 0);
    foreach (ts, tt, if (done, break);
      my(rz = rhozk(zkNum, Dz, p, lift(tt)), re = rhoK(rz, epsL), ss);
      if (re == 0 || !issquare(re, &ss), next);
      foreach ([ss, -ss], sv, if (done, break);
        my(t2s = [0]);
        if (kind == 2, my(te = 2 * (rhoK(rz, eaL) + sv * rhoK(rz, ebL)), t2); if (te == 0 || !issquare(te, &t2), next); t2s = [t2, -t2]);
        foreach (t2s, tv, if (done, break);
          my(vals = vector(m, s, my(g = gens[s]); if (kind == 1, rhoK(rz, g[1]) + sv * rhoK(rz, g[2]),
                 rhoK(rz, g[1]) + sv * rhoK(rz, g[2]) + (rhoK(rz, g[3]) + sv * rhoK(rz, g[4])) * tv)));
          if (vecmin(apply(v -> v != 0, vals)) == 0, next);
          my(bits = vector(m, s, kronecker(lift(vals[s]), p) == -1), M2 = matconcat([M; bits]), r2 = matrank(Mod(M2, 2)));
          \\ the Lean test is rho^((p-1)/2) = -1: the same as the Legendre symbol
          if (vecmin(vector(m, s, (vals[s]^((p - 1) / 2) == -1) == bits[s])) == 0, error("Euler criterion"));
          if (r2 > rk, M = M2; rk = r2; done = 1;
            listput(rows, sum(s = 1, m, bits[s] * 2^(s - 1)));
            listput(data, if (kind == 1, [p, lift(tt), lift(sv)], [p, lift(tt), lift(sv), lift(tv)])))))));
  [Vec(rows), Vec(data), M];
}

main() = {
  my(t0 = getabstime(), zkNum = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"), Dz = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz"),
     DB = leandef5(Str(LEAN, "M1/DataBezout.lean"), "DB"), fL = leandef5(Str(LEAN, "M1/Basic.lean"), "fL"),
     epsL = leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL"), eaL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL"),
     ebL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL"), gL, gN, CL, CN, TL, TN, doc, defs);
  read(DATA); gL = SB5_gL; gN = SB5_gN;
  chk5(#gL == 29 && #gN == 53, "29 L and 53 N generators read from sunit_generators_data.gp");
  chk5(DB % Dz == 0, "Dz divides DB (M1's Dz_dvd_DB)");
  \\ tool tests
  chk5(xorSel5([1, 2, 4], 5) == 5 && xorSel5([3, 1], 3) == 2 && leftInvOK5([1, 3], 2, [1, 3]) && !leftInvOK5([1, 3], 2, [1, 2]), "tool: xorSel5, leftInvOK5 (known answers and a failing certificate)");
  my(rz3 = rhozk(zkNum, Dz, 3, 2));
  chk5(rhoK(rz3, epsL) == Mod(2, 3), "tool: rho at (p, t) = (3, 2) sends eps to 2 (M3b's res3_epsO)");
  CL = choose(gL, 1, zkNum, Dz, DB, fL, epsL, eaL, ebL);
  CN = choose(gN, 2, zkNum, Dz, DB, fL, epsL, eaL, ebL);
  \\ tool test: rho_L, rho_N (the formulas of choose) are ring homomorphisms on the tower arithmetic, at the first
  \\ chosen character of each field (random elements; products by Lmul, Nmul of tower_lib.gp); negative control 2 t2 ((2 t2)^2 != t2^2 as p > 3)
  nfK = nfinit(Pol(Vecrev(fL), 'b)); EPS = Col(epsL); EN = [Col(eaL) / 2, Col(ebL) / 2];
  my(dL = CL[2][1], dN = CN[2][1], rzL = rhozk(zkNum, Dz, dL[1], dL[2]), rzN = rhozk(zkNum, Dz, dN[1], dN[2]), okh = 1, badh = 0,
     rhL = (rz, sv, g) -> rhoK(rz, g[1]) + sv * rhoK(rz, g[2]),
     rhN = (rz, sv, tv, g) -> rhoK(rz, g[1]) + sv * rhoK(rz, g[2]) + (rhoK(rz, g[3]) + sv * rhoK(rz, g[4])) * tv,
     rK = () -> Col(vector(21, i, random(9) - 4)));
  for (r = 1, 5, my(x1 = [rK(), rK()], y1 = [rK(), rK()], xn = [rK(), rK(), rK(), rK()], yn = [rK(), rK(), rK(), rK()], pn = Nfmt(Nmul(Nunfmt(xn), Nunfmt(yn))));
    if (rhL(rzL, dL[3], Lmul(x1, y1)) != rhL(rzL, dL[3], x1) * rhL(rzL, dL[3], y1), okh = 0);
    if (rhN(rzN, dN[3], dN[4], pn) != rhN(rzN, dN[3], dN[4], xn) * rhN(rzN, dN[3], dN[4], yn), okh = 0);
    if (rhN(rzN, dN[3], 2 * dN[4], pn) != rhN(rzN, dN[3], 2 * dN[4], xn) * rhN(rzN, dN[3], 2 * dN[4], yn), badh++));
  chk5(okh, Str("tool: rho_L at (p, t, s) = ", dL, " and rho_N at ", dN, " are multiplicative (5 random products each)"));
  chk5(badh > 0 && dN[1] > 3, Str("tool: negative control, rho_N with 2 t2 in place of t2 is not multiplicative (", badh, " of 5 products)"));
  my(TLm = lift(Mod(CL[3], 2)^(-1)), TNm = lift(Mod(CN[3], 2)^(-1)));
  TL = vector(29, k, sum(j = 1, 29, TLm[k, j] * 2^(j - 1)));
  TN = vector(53, k, sum(j = 1, 53, TNm[k, j] * 2^(j - 1)));
  chk5(#CL[1] == 29 && leftInvOK5(CL[1], 29, TL), Str("L: 29 characters, rows RL of full rank, leftInvOK RL 29 29 TL (primes ", CL[2][1][1], " to ", CL[2][29][1], ")"));
  chk5(#CN[1] == 53 && leftInvOK5(CN[1], 53, TN), Str("N: 53 characters, rows RN of full rank, leftInvOK RN 53 53 TN (primes ", CN[2][1][1], " to ", CN[2][53][1], ")"));
  chk5(!leftInvOK5(CL[1], 29, vector(29, k, bitxor(TL[k], k == 1))), "negative control: a perturbed TL fails leftInvOK");
  \\ the data satisfy the stated congruences
  my(okd = 1);
  foreach (CL[2], d, my(p = d[1], rz = rhozk(zkNum, Dz, p, d[2]));
    if (!isprime(p) || p == 2 || p == 7 || Dz % p == 0 || DB % p == 0 || subst(Pol(Vecrev(fL), 'X), 'X, Mod(d[2], p)) != 0 || Mod(d[3], p)^2 != rhoK(rz, epsL), okd = 0));
  foreach (CN[2], d, my(p = d[1], rz = rhozk(zkNum, Dz, p, d[2]));
    if (!isprime(p) || p == 2 || p == 7 || Dz % p == 0 || DB % p == 0 || subst(Pol(Vecrev(fL), 'X), 'X, Mod(d[2], p)) != 0 || Mod(d[3], p)^2 != rhoK(rz, epsL)
        || d[4] % p == 0 || Mod(d[4], p)^2 != 2 * (rhoK(rz, eaL) + d[3] * rhoK(rz, ebL)), okd = 0));
  chk5(okd, "every character datum: p odd prime, p != 7, p divides neither Dz nor DB, fL(t) = 0, s^2 = rho(eps), t2 != 0, t2^2 = 2 (rho(ea) + s rho(eb)) mod p");
  printf("chL = %s\n", CL[2]); printf("chN = %s\n", CN[2]);
  printf("RL = %s\nTL = %s\nRN = %s\nTN = %s\n", CL[1], TL, CN[1], TN);
  doc = "Residue characters (independence modulo squares, residue_characters.gp):\n\n* `chL` (29 entries `[p, t, s]`), `chN` (53 entries `[p, t, s, t2]`): `p` an odd prime, `p ≠ 7`, `p` prime to `Dz`\n  and `DB`; `t` a root of `fL` mod `p`, `ρ (zkE a) = Dz⁻¹ evalL t (combo a zkNum) mod p`; `s² = ρ ε`;\n  `t2 ≠ 0`, `t2² = 2 (ρ ea + s ρ eb)`. `ρ_L (a0 + a1 ω) = ρ a0 + s ρ a1`,\n  `ρ_N (a0 + a1 ω + (b0 + b1 ω) (2 ω_N)) = ρ_L (a0 + a1 ω) + ρ_L (b0 + b1 ω) t2`.\n* `RL`, `RN`: bit `s` of row `j` is set iff `ρ_j (gen s) ^ ((p - 1) / 2) = -1` (every generator is nonzero mod every `p`).\n* `TL`, `TN`: left inverses, `leftInvOK RL 29 29 TL`, `leftInvOK RN 53 53 TN` (Echelon.lean).\n";
  defs = [["Characters of `L42`: `[p, t, s]`.", "chL", "List (List Int)", Str(CL[2])], ["Characters of `N84`: `[p, t, s, t2]`.", "chN", "List (List Int)", Str(CN[2])],
          ["Rows of the `L42` characters on the 29 generators.", "RL", "List Nat", Str(CL[1])], ["Left inverse of `RL`.", "TL", "List Nat", Str(TL)],
          ["Rows of the `N84` characters on the 53 generators.", "RN", "List Nat", Str(CN[1])], ["Left inverse of `RN`.", "TN", "List Nat", Str(TN)]];
  system(Str("rm -f ", OUT));
  writebin(OUT, [doc, defs, [CL, CN, TL, TN]]);
  chk5(read(OUT)[2] == defs, "cache /tmp/sb5/chars.bin written and read back");
  printf("DONE residue_characters: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - t0);
}
iferr(main(), E, printf("ERROR: %s\n", E); quit(1));
quit(0);
