\\ sunits_n84.gp: S-units of the degree 84 field N (S = primes above 2 and 7) through a generalised
\\ norm relation (Etienne, arXiv 2411.13124), without bnfinit(N).
\\
\\ Group theory (code/earlier-computations/norm_relation_n84.g): N = M^H in the Galois closure M of K21 (group PGL(2,7)); N admits a
\\ generalised norm relation with respect to L = K21(sqrt(-e0)) and K13 = K21(sqrt(7 e0)) (degree 42 each), so the
\\ compositum actions of O_{L,S}^x and O_{K13,S}^x span a subgroup of finite index of O_{N,S}^x.
\\ Compositum action: for a monic factor p_j of the defining polynomial P_F of F (F = L or K13) over N, and x in F
\\ written x = g(theta_F) with g in Q[X], C_j . x = N_{N[X]/(p_j) / N}(g(X)) = Res_X(p_j, g) (p_j monic). This is
\\ multiplicative, and maps S-units of F to S-units of N (a norm of an S-unit is an S-unit), whether or not the
\\ factorisation is complete: only p_j | P_F over N is used, and it is checked exactly.
\\ The S-units of F come from bnfunits (GRH bnf) as products of small elements (compact form); each product is
\\ checked exactly to be an S-unit (valuations of the base elements at all their prime factors). So the elements of
\\ N produced here are exact S-units, unconditionally.
\\ Certificate: dim N(S,2) = r1(N) + r2(N) + #S_N = 45 + #S_N when Cl(N)[2] = 0 (class_group_n84_two.gp). If the produced
\\ S-units have a character matrix (quadratic characters at degree one primes of N) of that rank, they span N(S,2),
\\ unconditionally. The index of the norm relation subgroup plays no role.
\\ Negative control: the actions of the S-units of L alone must have a smaller rank (the characters 7 and 8' of
\\ PGL(2,7) are not covered by L).
\\
\\ Output: /tmp/k21c/nr/nsunits.bin = [basis, table] (basis: list of [field, factor, unit index] with character
\\ rank equal to the target; table: the exact elements C_j . g for every factor and base element), and the log.
\\ Run from code/earlier-computations: gp -q sunits_n84.gp < /dev/null
read("field_l42_polynomial.gp"); read("field_n84_polynomial.gp"); read("field_k13_polynomial.gp");
read("norm_relation_lib.gp");
main() = {
  my(t0 = getabstime(), nfN, SN, target, fields, PR, np, rows = List(), info = List(), M, rk = 0, rkL, sel = List(), table = List());
  PNy = subst(PN, t, y);
  if (fexists(Str(DIR, "nfN.bin")), nfN = read(Str(DIR, "nfN.bin")), nfN = nfinit([PNy, [2, 3, 7, 439, 253447]]); wbin(Str(DIR, "nfN.bin"), nfN));
  chk(nfN.pol == PNy && nfN.sign == [6, 39], "nf of N (degree 84, signature [6, 39])");
  SN = concat(idealprimedec(nfN, 2), idealprimedec(nfN, 7));
  target = nfN.sign[1] + nfN.sign[2] + #SN;
  printf("N: #S_N = %d (above 2: %s; above 7: %s); target dim N(S,2) = %d (%d ms)\n", #SN, apply(pr -> [pr.e, pr.f], idealprimedec(nfN, 2)), apply(pr -> [pr.e, pr.f], idealprimedec(nfN, 7)), target, getabstime() - t0);
  np = target + 30; PR = charprimes(nfN, np, 10^5);
  \\ character column of -1 (first candidate)
  listput(rows, vector(np, i, PR[i][1] % 4 == 3)~); listput(info, [0, 0, 0]);
  fields = [[subst(Lpol, u, y), "L", "faL_N.bin"], [P13, "K13", "fa13_N.bin"]];
  for (fi = 1, #fields, my(pol = fields[fi][1], name = fields[fi][2], su, fa, polx = subst(pol, y, x), ord);
    su = sunits_of(pol, name);
    if (fexists(Str(DIR, fields[fi][3])), fa = read(Str(DIR, fields[fi][3])), fa = nffactor(nfN, polx); wbin(Str(DIR, fields[fi][3]), fa));
    my(prod = 1); for (j = 1, #fa~, prod *= fa[j, 1]^fa[j, 2]);
    chk(prod == polx && vecmax(fa[, 2]) == 1, Str(name, ": the ", #fa~, " factors over N (degrees ", apply(poldegree, fa[, 1]~), ") multiply to its polynomial, squarefree"));
    my(gvs = apply(g -> Vecrev(g), su[3]));   \\ power coefficients of the base elements, constant first
    ord = vecsort(vector(#fa~, j, [poldegree(fa[j, 1]), j]));
    for (jj = 1, #ord, my(j = ord[jj][2], fd, act, t1 = getabstime(), chs, newrows = 0);
      if (fi == 2 && rk == target, break);
      if (pollead(fa[j, 1]) != 1, error("factor not monic"));
      fd = factordata(nfN, fa[j, 1], poldegree(polx) - 1);
      act = vector(#gvs, k, compaction(nfN, fd, gvs[k]));
      for (k = 1, #act, if (act[k] == 0, error("zero action")); if (denominator(content(act[k])) != 1, error("non-integral action")));
      listput(table, [fi, j, act]);
      chs = vector(#act, k, vector(np, i, chi(PR[i], act[k])));
      for (i = 1, #su[2], my(fam = su[2][i], row = vectorv(np));
        for (l = 1, #fam, if (fam[l][2] % 2, row += chs[fam[l][1]]~));
        listput(rows, row); listput(info, [fi, j, i]));
      M = Mod(matconcat(Vec(rows)), 2); my(rk0 = rk); rk = matrank(M);
      printf("  %s factor %d (degree %d): %d actions, %d ms; character rank %d -> %d\n", name, j, fd[1], #act, getabstime() - t1, rk0, rk));
    if (fi == 1, rkL = rk; printf("rank from the S-units of L alone (all %d factors) and -1: %d\n", #fa~, rkL));
    fields[fi] = concat(fields[fi], [su[2]]));
  printf("final character rank %d, target %d (%d ms)\n", rk, target, getabstime() - t0);
  chk(rkL < target, "negative control: the S-units of L alone do not reach the target");
  M = Mod(matconcat(Vec(rows)), 2);
  my(idx = matindexrank(M)[2]);
  wbin(Str(DIR, "nsunits.bin"), [Vec(info), Vec(table), vector(#fields, i, fields[i][4]), idx, PR]);
  printf("independent candidates: %s\n", vector(#idx, k, info[idx[k]]));
  chk(rk == target, Str("the character matrix of the produced S-units and -1 has rank ", rk, " = r1 + r2 + #S_N: they span N(S,2) (given Cl(N)[2] = 0)"));
  print("RESULT PASS");
}
main();
quit;
