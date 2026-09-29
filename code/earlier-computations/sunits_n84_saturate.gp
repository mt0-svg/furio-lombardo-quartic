\\ sunits_n84_saturate.gp: 2-saturation of the norm relation S-units of N (degree 84), giving a basis of N(S,2) without GRH.
\\
\\ Input: /tmp/k21c/nr/nsunits.bin from sunits_n84.gp: generators of a subgroup U' of O_{N,S}^x (S = primes
\\ above 2 and 7), each a compositum action C_j of an S-unit of L or K13, stored in compact form: a product of base
\\ elements a_{r,k} (the actions of the small base elements, table entry r, index k) with integer exponents (up to about
\\ 3 10^11). Their quadratic characters (83 degree one primes of N) have rank 46; dim N(S,2) = 53 (Cl(N)[2] = 0,
\\ class_group_n84_two.gp).
\\ Method (the saturation step of Biasse, Fieker, Hofmann, Page, arXiv 2002.12332):
\\  1. A free basis of a finite index subgroup U'' of U': -1, the 45 character independent generators, and 7 more
\\     generators chosen by independence of their S-logarithm vectors (log|sigma(g)| at the 45 archimedean places, v_P(g)
\\     at the 8 primes of S; the map is injective modulo torsion on S-units, torsion of N = +-1 since N has real places).
\\     Then U''/U''^2 = F2^53 with this basis.
\\  2. The kernel of the character map on U''/U''^2 has dimension 53 - 46 = 7; each kernel vector beta is a candidate
\\     square. beta = prod a^{n} is a square iff gamma = prod_{n odd} a (times -1 if needed) is one; gamma is computed
\\     explicitly (small: the base elements are small) and its square root is found by nfroots and checked exactly.
\\     rho = sqrt(gamma) prod a^{floor(n/2)} is an S-unit (rho^2 = beta).
\\  3. Replace each extra generator g_x by rho_x (then U''' = <U'', rho> is free on the new basis), recompute the
\\     character rank, iterate until the rank is 53.
\\ Certificate (no GRH): 53 elements of O_{N,S}^x (each an exact S-unit: a compositum action of an S-unit, or an exact
\\ square root of a product of those) whose character matrix has rank 53 = r1 + r2 + #S_N; since Cl(N)[2] = 0 they span
\\ N(S,2). The characters are homomorphisms, so rank 53 proves independence modulo squares; the choice of candidates in
\\ step 2 is heuristic but every square root is checked exactly.
\\ Elements are stored as [s, E, X]: (-1)^s prod over (r, k) of a_{r,k}^E[r,k] (E a Map "r,k" -> exponent) prod over
\\ [col, e] in X of col^e (col explicit on the integral basis of nfN).
\\ Output: /tmp/k21c/nr/nsat.bin = [basis (53 elements), the character matrix, PR]; square roots cached in
\\ /tmp/k21c/sat/root_<iteration>_<x>.bin (a rerun resumes).
\\ Run from code/earlier-computations: gp -q sunits_n84_saturate.gp < /dev/null
default(parisizemax, 7*10^9); default(nbthreads, 1); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
read("field_n84_polynomial.gp");
read("norm_relation_lib.gp");
SDIR = "/tmp/k21c/sat/";
key(r, k) = Str(r, ",", k);
unkey(kk) = eval(Str("[", kk, "]"));
\\ product of two elements (exponent vectors add)
eprod(A, B) = {
  my(E = A[2], M = Mat(B[2]), X = concat(A[3], B[3]));
  for (i = 1, #M~, my(v0 = 0); mapisdefined(E, M[i, 1], &v0); mapput(E, M[i, 1], v0 + M[i, 2]));
  [(A[1] + B[1]) % 2, E, X];
}
epow01(A, e) = if (e, A, [0, Map(), []]);
\\ global state (GP closures capture copies, so the caches are globals)
NFN = 0; EMBM = 0; TABLE = 0; PRG = 0; SNG = 0; LVG = Map(); CHG = Map();
tabof(in) = { for (r = 1, #TABLE, if (TABLE[r][1] == in[1] && TABLE[r][2] == in[2], return(r))); 0; }
\\ S-log vectors (45 archimedean logs, 8 valuations) and characters of the base elements of table entry r, cached
ensure(r) = {
  if (mapisdefined(LVG, r), return(0));
  my(acts = TABLE[r][3], np = #PRG, M = matrix(53, #acts), C = matrix(np, #acts), t1 = getabstime());
  for (k = 1, #acts, my(em = EMBM * acts[k]);
    for (j = 1, 45, M[j, k] = log(abs(em[j])));
    for (j = 1, 8, M[45 + j, k] = nfeltval(NFN, acts[k], SNG[j]));
    for (i = 1, np, C[i, k] = chi(PRG[i], acts[k])));
  mapput(LVG, r, M); mapput(CHG, r, C);
  printf("  base elements of table entry %d (%s): S-logs and characters, %d ms\n", r, TABLE[r][1..2], getabstime() - t1);
  write(Str(SDIR, "sat.log"), Str("ensure ", r, " ", getabstime() - t1));
  1;
}
\\ embeddings of the integral basis of N (real places, then one per complex pair): the matrix M stored by nfinit (about
\\ 1600 digits for this polynomial; nfeltembed recomputes at every call, 5 s in degree 84)
embinit() = { EMBM = NFN[5][1]; chk(#EMBM~ == NFN.r1 + NFN.r2 && #EMBM == 84, "embedding matrix of N"); }
\\ generator with info entry in = [fi, j, i] and famat fm as an element
gen(in, fm) = {
  if (in[1] == 0, return([1, Map(), []]));
  my(r = tabof(in), E = Map());
  for (l = 1, #fm, mapput(E, key(r, fm[l][1]), fm[l][2]));
  [0, E, []];
}
\\ S-log vector of an element (explicit factors: embeddings and valuations computed directly)
glog(A) = {
  my(v = vectorv(53), M = Mat(A[2]));
  for (i = 1, #M~, my(rk2 = unkey(M[i, 1])); ensure(rk2[1]); v += M[i, 2] * mapget(LVG, rk2[1])[, rk2[2]]);
  for (i = 1, #A[3], my(cc = A[3][i][1], em = EMBM * cc);
    for (j = 1, 45, v[j] += A[3][i][2] * log(abs(em[j])));
    for (j = 1, 8, v[45 + j] += A[3][i][2] * nfeltval(NFN, cc, SNG[j])));
  v;
}
\\ character row of an element
echi(A) = {
  my(np = #PRG, v = vectorv(np, i, if (A[1], PRG[i][1] % 4 == 3, 0)), M = Mat(A[2]));
  for (i = 1, #M~, if (M[i, 2] % 2, my(rk2 = unkey(M[i, 1])); ensure(rk2[1]); v += mapget(CHG, rk2[1])[, rk2[2]]));
  for (i = 1, #A[3], if (A[3][i][2] % 2, v += vectorv(np, j, chi(PRG[j], A[3][i][1]))));
  v % 2;
}
\\ Gram-Schmidt independence test: adds v to the orthonormal list QB if independent
QB = List();
addlog(v) = {
  my(w = v, nv);
  for (i = 1, #QB, w -= (QB[i]~ * w) * QB[i]);
  nv = sqrt(norml2(w));
  if (nv > 10^-20 * max(1, sqrt(norml2(v))), listput(QB, w / nv); 1, 0);
}
main() = {
  my(t0 = getabstime(), NS = read(Str(DIR, "nsunits.bin")), info = NS[1], fams = NS[3], idx = NS[4], sidx, basis,
     rows, rk = 0, chosen = List(), onecol = vectorv(84, i, i == 1));
  NFN = read(Str(DIR, "nfN.bin")); TABLE = NS[2]; PRG = NS[5];
  embinit();
  system(Str("mkdir -p ", SDIR));
  SNG = concat(idealprimedec(NFN, 2), idealprimedec(NFN, 7));
  chk(#SNG == 8, "8 primes of N above 2 and 7");
  \\ step 1: the free basis
  basis = List(); listput(basis, [1, Map(), []]);   \\ -1
  for (q = 2, #idx, my(in = info[idx[q]], A = gen(in, fams[in[1]][in[3]]));
    chk(addlog(glog(A)), Str("character independent generator ", in, " has an independent S-log"));
    listput(basis, A));
  printf("step 1: 45 character independent generators, S-log rank %d (%d ms)\n", #QB, getabstime() - t0);
  sidx = Set(idx);
  foreach ([[1, 1], [1, 3], [2, 2], [1, 4], [2, 3]], pj,
    if (#QB == 52, break);
    for (q = 1, #info, my(in = info[q]);
      if (#QB == 52, break);
      if (in[1] == pj[1] && in[2] == pj[2] && !setsearch(sidx, q),
        my(A = gen(in, fams[in[1]][in[3]]));
        if (addlog(glog(A)), listput(basis, A); listput(chosen, in)))));
  printf("  extra generators (S-log independent): %s; S-log rank %d (%d ms)\n", Vec(chosen), #QB, getabstime() - t0);
  chk(#QB == 52 && #basis == 53, "a free basis of 53 elements (-1 and 52 S-log independent generators)");
  basis = Vec(basis);
  \\ steps 2 and 3
  for (it = 1, 6,
    rows = matconcat(vector(#basis, i, echi(basis[i])));
    rk = matrank(Mod(rows, 2));
    printf("iteration %d: character rank of the basis %d of 53 (%d ms)\n", it, rk, getabstime() - t0);
    if (rk == 53, break);
    my(K = lift(matker(Mod(rows, 2))), used = List(), newb = basis);
    for (c = 1, #K, my(v = K[, c] % 2, pv = 0, beta, gam, M, half, rt, rho, fname, Xh = List());
      \\ distinct pivots (pivot = last nonzero coordinate; later vectors vanish at earlier pivots)
      for (l = 1, #used, if (v[used[l][1]], v = (v + used[l][2]) % 2));
      for (i = 1, 53, if (v[i], pv = i));
      chk(pv > 1, "kernel vector with a valid pivot");
      listput(used, [pv, v]);
      beta = [0, Map(), []]; for (i = 1, 53, if (v[i], beta = eprod(beta, basis[i])));
      \\ gamma = odd part (explicit), half = floor(n / 2)
      M = Mat(beta[2]); gam = if (beta[1], -onecol, onecol); half = Map();
      for (i = 1, #M~, my(e = M[i, 2], rk2 = unkey(M[i, 1]));
        if (e % 2, gam = mul(NFN, gam, TABLE[rk2[1]][3][rk2[2]]));
        if ((e - (e % 2)) / 2 != 0, mapput(half, M[i, 1], (e - (e % 2)) / 2)));
      for (i = 1, #beta[3], my(e = beta[3][i][2]);
        if (e % 2, gam = mul(NFN, gam, beta[3][i][1]));
        if ((e - (e % 2)) / 2 != 0, listput(Xh, [beta[3][i][1], (e - (e % 2)) / 2])));
      fname = Str(SDIR, "root_", it, "_", c, ".bin");
      rt = 0; if (fexists(fname), rt = read(fname); if (rt[1] != gam, rt = 0));
      if (rt == 0,
        my(t1 = getabstime(), rr = nfroots(NFN, x^2 - nfbasistoalg(NFN, gam)));
        chk(#rr == 2, Str("iteration ", it, ", kernel vector ", c, ": gamma (", round(log(normlp(gam)) / log(2)), " bits) is a square in N (nfroots, ", getabstime() - t1, " ms)"));
        rt = [gam, nfalgtobasis(NFN, rr[1])]; wbin(fname, rt));
      chk(mul(NFN, rt[2], rt[2]) == gam, "sqrt(gamma)^2 = gamma exactly");
      rho = [0, half, concat(Vec(Xh), [[rt[2], 1]])];
      newb[pv] = rho;
      printf("  kernel vector %d: pivot %d replaced by a square root (%d ms)\n", c, pv, getabstime() - t0));
    basis = newb);
  chk(rk == 53, "the character matrix of the saturated basis has rank 53 = r1 + r2 + #S_N: it spans N(S,2) (given Cl(N)[2] = 0)");
  wbin(Str(DIR, "nsat.bin"), [basis, rows, PRG]);
  print("RESULT PASS");
}
main();
quit;
