\\ tower_lib.gp: exact arithmetic in M3b's tower K21 < L42 = K21(om) < N84 = L42(on), om^2 = eps, on^2 = eN =
\\ (ea + eb om) / 2 (lean/FurioLombardo/Discharge/M3b/Fields.lean), in the coordinates of
\\ lean/FurioLombardo/Discharge/SelmerBasis/SUnitDefs.lean, and its identification with the absolute fields nfL, nfN of
\\ the Prym pipeline (p21_29 sel_fields, rebuilt by field_caches.gp in /tmp/sb5/sel/fields.bin). Lane selmer-global-bound, global side
\\ (scripts sb_5*.gp).
\\
\\ Elements. K21: columns on nfK.zk (checked equal to M1's zk, zkNum / Dz). L42: [a0, a1] = a0 + a1 om.
\\ N84: [a0, a1, c0, c1] = a0 + a1 om + (c0 + c1 om) on (plain on coordinates). The Lean format of gN is
\\ [a0, a1, b0, b1] = a0 + a1 om + (b0 + b1 om) (2 on), i.e. b = c / 2 (Nfmt, Nunfmt).
\\ Identifications (sb5_iota): iotaL : L42 -> nfL, theta -> aL, alpha -> 1 / thL; iotaN : N84 -> nfN, theta -> aN,
\\ beta -> 1 / thN, where alpha, beta are the roots of q, h (k = 0) chosen in sb_5a and thL, thN the roots of the
\\ unreversed factors G1, h_unrev of p21_29 (so T -> 1/x identifies K21[T]/(fRev k) with p21_29's K21[x]/(f_k)).
\\ The caller sets parisizemax, nbthreads and realprecision (a default(parisizemax) in a read file stops the read).

SB5_NFAIL = 0; SB5_NOK = 0;
\\ a failed check stops the run (error); the scripts print DONE only at the end of their main function
chk5(c, msg) = if (!c, SB5_NFAIL++; printf("CHECK FAILED: %s\n", msg); error(Str("check failed: ", msg)), SB5_NOK++; printf("ok: %s\n", msg));
strprefix5(s, p) = my(A1 = Vecsmall(s), B1 = Vecsmall(p)); #A1 >= #B1 && A1[1 .. #B1] == B1;
strtrim5(s) = { my(A1 = Vecsmall(s), i = 1, j = #A1); while (i <= j && A1[i] == 32, i++); while (j >= i && A1[j] == 32, j--); if (j < i, "", Strchr(A1[i .. j])); }
\\ replace every occurrence of pat by rep in s
strrepl5(s, pat, rep) = {
  my(A1 = Vecsmall(s), P1 = Vecsmall(pat), R1 = Vecsmall(rep), out = List(), i = 1, n = #A1, m = #P1);
  while (i <= n,
    if (i + m - 1 <= n && A1[i .. i + m - 1] == P1, for (k = 1, #R1, listput(out, R1[k])); i += m,
      listput(out, A1[i]); i++));
  Strchr(Vecsmall(Vec(out)));
}
\\ value of `def name ... := <literal>` in a Lean file: the literal is the rest of the def line after the first ":="
\\ and the following lines up to a blank line or the next declaration; `!![` (matrix) and `![` (vector) become gp
\\ brackets. after: start the search at the first line beginning with this marker (a namespace line). tuples = 1:
\\ parentheses become brackets (a List (Nat × Nat) literal is read as a vector of pairs).
leandef5(file, name, after = "", tuples = 0) = {
  my(L = readstr(file), i0 = 0, i1 = 1, s, parts);
  if (after != "", i1 = 0; for (i = 1, #L, if (strprefix5(L[i], after), i1 = i; break)); if (i1 == 0, error("leandef5: no marker ", after, " in ", file)));
  for (i = i1, #L, my(w = strsplit(strtrim5(L[i]), " ")); if (#w >= 2 && w[1] == "def" && w[2] == name, i0 = i; break));
  if (i0 == 0, error("leandef5: no def ", name, " in ", file));
  parts = strsplit(L[i0], ":=");
  if (#parts < 2, error("leandef5: no := on the def line of ", name));
  s = parts[2]; for (k = 3, #parts, s = Str(s, ":=", parts[k]));
  for (i = i0 + 1, #L, my(tl = strtrim5(L[i]));
    if (tl == "" || strprefix5(tl, "/-") || strprefix5(tl, "def ") || strprefix5(tl, "theorem ") || strprefix5(tl, "end ") || strprefix5(tl, "namespace "), break);
    s = Str(s, L[i]));
  s = strrepl5(strrepl5(s, "!![", "["), "![", "[");
  if (tuples, s = strrepl5(strrepl5(s, "(", "["), ")", "]"));
  eval(s);
}

\\ ---------------------------------------------------------------- K21
Kc(a) = if (type(a) == "t_COL", a, nfalgtobasis(nfK, a));
Km(a, c) = Kc(nfeltmul(nfK, a, c));
Kd(a, c) = Kc(nfeltdiv(nfK, a, c));
Kpow(a, e) = Kc(nfeltpow(nfK, a, e));
\\ the square roots of a in K21 (a list of 0 or 2 columns; [0] for a = 0)
Ksqrts(a) = { a = Kc(a); if (a == 0, return([a])); my(r = nfroots(nfK, 'X^2 - nfbasistoalg(nfK, a))); apply(Kc, r); }
\\ an element of K21 with zk coordinates as a Lean list (length 21) and back
\\ (silent on success: a failure counts as a failed check and stops the run)
Klist(a) = { a = Kc(a); if (denominator(a) != 1, SB5_NFAIL++; printf("CHECK FAILED: Klist: integral coordinates\n"); error("Klist: non-integral coordinates")); Vec(a); }
KofList(l) = { if (#l != 21, SB5_NFAIL++; printf("CHECK FAILED: KofList: length 21\n"); error(Str("KofList: length ", #l, " != 21"))); Col(l); }
\\ bits of the largest coordinate
bits5(v) = { my(m = 0); foreach (v, e, if (type(e) == "t_COL" || type(e) == "t_VEC", m = max(m, bits5(e)), if (e != 0, m = max(m, ceil(log(abs(e) + 1) / log(2)))))); m; }
den5(v) = { my(d = 1); foreach (v, e, d = lcm(d, if (type(e) == "t_COL" || type(e) == "t_VEC", den5(e), denominator(e)))); d; }

\\ ---------------------------------------------------------------- L42 = K21(om), om^2 = EPS
Lof(a0, a1) = [Kc(a0), Kc(a1)];
Ladd(x, y) = [x[1] + y[1], x[2] + y[2]];
Lsub(x, y) = [x[1] - y[1], x[2] - y[2]];
Lneg(x) = [-x[1], -x[2]];
Lsc(c, x) = [Km(c, x[1]), Km(c, x[2])];
Lmul(x, y) = [Km(x[1], y[1]) + Km(EPS, Km(x[2], y[2])), Km(x[1], y[2]) + Km(x[2], y[1])];
Lnorm(x) = Km(x[1], x[1]) - Km(EPS, Km(x[2], x[2]));
Linv(x) = { my(n = Lnorm(x)); if (n == 0, error("Linv: zero")); [Kd(x[1], n), Kd(-x[2], n)]; }
Lpow(x, e) = { my(r = [Kc(1), Kc(0)], y = x); if (e < 0, y = Linv(x); e = -e); while (e, if (e % 2, r = Lmul(r, y)); e \= 2; if (e, y = Lmul(y, y))); r; }
Lis0(x) = x[1] == 0 && x[2] == 0;
\\ a square root of y in L42, or 0: s0^2 + eps s1^2 = y0, 2 s0 s1 = y1, s0^2 - eps s1^2 = +-sqrt(N y)
Lsqrt(y) = {
  if (Lis0(y), return([Kc(0), Kc(0)]));
  if (y[2] == 0,
    my(r = Ksqrts(y[1])); if (#r, return([r[1], Kc(0)]));
    r = Ksqrts(Kd(y[1], EPS)); if (#r, return([Kc(0), r[1]])); return(0));
  my(ms = Ksqrts(Lnorm(y)));
  foreach (ms, m, foreach ([m, -m], mm, my(s0s = Ksqrts((y[1] + mm) / 2));
    foreach (s0s, s0, if (s0 != 0, my(s = [s0, Kd(y[2], 2 * s0)]); if (Lmul(s, s) == y, return(s))))));
  0;
}

\\ ---------------------------------------------------------------- N84 = L42(on), on^2 = EN
NA(x) = [x[1], x[2]];
NB(x) = [x[3], x[4]];
Nof(A, B) = [A[1], A[2], B[1], B[2]];
NofK(c) = [Kc(c), Kc(0), Kc(0), Kc(0)];
NofL(A) = [A[1], A[2], Kc(0), Kc(0)];
Nadd(x, y) = vector(4, i, x[i] + y[i]);
Nsub(x, y) = vector(4, i, x[i] - y[i]);
Nneg(x) = vector(4, i, -x[i]);
Nsc(c, x) = vector(4, i, Km(c, x[i]));
Nmul(x, y) = { my(A = NA(x), B = NB(x), C = NA(y), D = NB(y)); Nof(Ladd(Lmul(A, C), Lmul(EN, Lmul(B, D))), Ladd(Lmul(A, D), Lmul(B, C))); }
NnormL(x) = Lsub(Lmul(NA(x), NA(x)), Lmul(EN, Lmul(NB(x), NB(x))));
NnormK(x) = Lnorm(NnormL(x));
Ninv(x) = { my(n = NnormL(x)); if (Lis0(n), error("Ninv: zero")); n = Linv(n); Nof(Lmul(NA(x), n), Lmul(Lneg(NB(x)), n)); }
Npow(x, e) = { my(r = NofK(1), y = x); if (e < 0, y = Ninv(x); e = -e); while (e, if (e % 2, r = Nmul(r, y)); e \= 2; if (e, y = Nmul(y, y))); r; }
Nis0(x) = x[1] == 0 && x[2] == 0 && x[3] == 0 && x[4] == 0;
\\ a square root of z in N84, or 0 (the same scheme one level up)
Nsqrt(z) = {
  if (Nis0(z), return(NofK(0)));
  my(Z0 = NA(z), Z1 = NB(z));
  if (Lis0(Z1),
    my(r = Lsqrt(Z0)); if (r != 0, return(NofL(r)));
    r = Lsqrt(Lmul(Z0, Linv(EN))); if (r != 0, return(Nof([Kc(0), Kc(0)], r))); return(0));
  my(m = Lsqrt(NnormL(z)));
  if (m == 0, return(0));
  foreach ([m, Lneg(m)], mm, my(s0 = Lsqrt(Lsc(1/2, Ladd(Z0, mm))));
    if (s0 != 0 && !Lis0(s0), my(s = Nof(s0, Lmul(Z1, Linv(Lsc(2, s0))))); if (Nmul(s, s) == z, return(s))));
  0;
}
\\ Lean format of N84 elements: b = c / 2
Nfmt(x) = [x[1], x[2], x[3] / 2, x[4] / 2];
Nunfmt(f) = [f[1], f[2], 2 * f[3], 2 * f[4]];
\\ value of a polynomial P in K21[X] (coefficient columns, constant first) at an element of L42 or N84 (Horner)
Lev(P, al) = { my(r = [Kc(0), Kc(0)]); forstep (i = #P, 1, -1, r = Ladd(Lmul(r, al), [Kc(P[i]), Kc(0)])); r; }
Nev(P, be) = { my(r = NofK(0)); forstep (i = #P, 1, -1, r = Nadd(Nmul(r, be), NofK(P[i]))); r; }

\\ ---------------------------------------------------------------- small linear algebra over K21
\\ solve sum_i c_i V[i] = t over K21 (V: n vectors of n K21 columns, t: n K21 columns), Gauss-Jordan
Ksolve(V, t) = {
  my(n = #V, A = vector(n, r, vector(n + 1)));
  for (r = 1, n, for (i = 1, n, A[r][i] = Kc(V[i][r])); A[r][n + 1] = Kc(t[r]));
  for (col = 1, n,
    my(piv = 0); for (r = col, n, if (A[r][col] != 0, piv = r; break));
    if (!piv, error("Ksolve: singular"));
    if (piv != col, my(tmp = A[piv]); A[piv] = A[col]; A[col] = tmp);
    my(iv = Kd(1, A[col][col])); A[col] = vector(n + 1, j, Km(iv, A[col][j]));
    for (r = 1, n, if (r != col && A[r][col] != 0, my(f = A[r][col]); A[r] = vector(n + 1, j, A[r][j] - Km(f, A[col][j])))));
  vector(n, r, A[r][n + 1]);
}

\\ ---------------------------------------------------------------- polynomials over K21 (coefficient vectors of columns, constant first)
Kpol(P) = Pol(apply(c -> nfbasistoalg(nfK, Kc(c)), Vecrev(P)), 'X);
Kvec(pol, n) = vector(n, i, Kc(polcoef(lift(pol), i - 1, 'X)));
\\ the class of pol modulo the monic m in K21[X], as a polynomial with polmod coefficients
Kmod(pol, m) = lift(Mod(pol, m));

\\ ---------------------------------------------------------------- Lean files with one def per entry
\\ all defs of a Lean file: a Map name -> literal (the text after the first ":=" of the def line and the following
\\ lines up to a blank line or the next declaration, as leandef5); a duplicate def is an error
leandefs5(file) = {
  my(L = readstr(file), M = Map(), cur = 0, s = "");
  for (i = 1, #L + 1, my(tl = if (i <= #L, strtrim5(L[i]), ""), w);
    if (cur != 0 && (i > #L || tl == "" || strprefix5(tl, "/-") || strprefix5(tl, "def ") || strprefix5(tl, "theorem ") || strprefix5(tl, "end ") || strprefix5(tl, "namespace ") || strprefix5(tl, "set_option ")),
      mapput(M, cur, s); cur = 0);
    if (i > #L, break);
    w = strsplit(tl, " ");
    if (#w >= 2 && w[1] == "def",
      my(parts = strsplit(L[i], ":="));
      if (#parts < 2, error("leandefs5: no := on the def line of ", w[2]));
      if (mapisdefined(M, w[2]), error("leandefs5: duplicate def ", w[2]));
      cur = w[2]; s = parts[2]; for (k = 3, #parts, s = Str(s, ":=", parts[k])),
      if (cur != 0, s = Str(s, L[i]))));
  M;
}
\\ the value of def name of the Map of leandefs5 (tuples as in leandef5)
leanval5(M, name, tuples = 0) = {
  my(s);
  if (!mapisdefined(M, name, &s), error("leanval5: no def ", name));
  s = strrepl5(strrepl5(s, "!![", "["), "![", "[");
  if (tuples, s = strrepl5(strrepl5(s, "(", "["), ")", "]"));
  eval(s);
}
\\ the n entries of a list split into defs: def name := [name_0, ..., name_(n-1)] (checked textually), each name_i read
leanentries5(M, name, n, tuples = 0) = {
  my(s, want = "[");
  if (!mapisdefined(M, name, &s), error("leanentries5: no def ", name));
  for (i = 0, n - 1, want = Str(want, if (i, ",", ""), name, "_", i));
  want = Str(want, "]");
  if (strrepl5(strtrim5(s), " ", "") != want, error("leanentries5: def ", name, " is not the list of its ", n, " entries"));
  vector(n, i, leanval5(M, Str(name, "_", i - 1), tuples));
}

\\ ---------------------------------------------------------------- the generators (data file sunit_generators_data.gp)
\\ in the cache layout of sb_5b: entries [coordinates, 0, 0, cofactor w, [a, b], 0] (L: [a0, a1]; N: the Lean format
\\ [a0, a1, b0, b1]; the nf.zk coordinates, scaling exponents and LLL columns of sb_5b are not kept in the data file)
sb5_gens(file) = {
  read(file);
  my(genL = vector(29, s, [[KofList(SB5_gL[s][1]), KofList(SB5_gL[s][2])], 0, 0, [KofList(SB5_gLw[s][1]), KofList(SB5_gLw[s][2])], SB5_gLab[s], 0]),
     genN = vector(53, s, [vector(4, i, KofList(SB5_gN[s][i])), 0, 0, vector(4, i, KofList(SB5_gNw[s][i])), SB5_gNab[s], 0]));
  if (#SB5_gL != 29 || #SB5_gN != 53 || #SB5_gLw != 29 || #SB5_gNw != 53 || #SB5_gLab != 29 || #SB5_gNab != 53, error("sb5_gens: wrong lengths in ", file));
  [genL, genN];
}
