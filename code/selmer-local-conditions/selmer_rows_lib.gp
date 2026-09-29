\\ selmer_rows_lib.gp: local coordinate certificates on the standard basis of G/G^2, G = prod_j F_j^x, at a place w of K21
\\ The caller reads the p21_29 stack (as selmer_bound_subsets.gp), sets parisizemax and nbthreads, then calls sb_init().
\\ Conventions.
\\  * K21 = Q[b]/(K21(b)), nfK = nfinit(K21) (zk = M2's integral basis `elt`, M1's `zkE`; checked through the alpha_w).
\\  * Reversed model: fRev_k = c_k q h (q, h monic, twist independent), variable x.
\\  * A component C of place W is F = K21[Y1]/(P1) (n = 2) or K21[Y1,Y2]/(P1, Y2^2 - Y2 + 1) (n = 4) or K21 (n = 1),
\\    completed at w. Basis 1, Y1 (, Y2, Y1 Y2) of O_F with offsets nu: v_F(sum c_i b_i) = min(eF v_w(c_i) + nu_i).
\\  * An element e of F: its certificate is [bits a on the standard basis, m, S] with
\\      v_F(e prod_i bas_i^(a_i) - Pi^(2m) S^2) >= 2m + 2 e_F + 1 (dyadic; >= 2m + 1 at 7) and v_F(S) = 0,
\\    so e prod bas^a / (Pi^m S)^2 is in 1 + 4 Pi O_F (1 + Pi O_F at 7), a square.
Y1 = varhigher("Y1"); Y2 = varhigher("Y2"); Xs = varhigher("Xs");
FQ4 = ffgen(Mod(1, 2) * ('wq^2 + 'wq + 1), 'wq);
\\ M2's generators of the primes above 2 and 7 (lean/FurioLombardo/M2/SpecialData.lean al1, al2, al3, al7)
{SB_AL = [[0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0],
         [-2, 2, 0, 1, 0, -2, 1, -1, 0, 2, 0, 1, 2, -1, 0, 2, 1, -1, 0, 1, -1],
         [1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
         [-2, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1]];}
SB_PNAME = ["v", "w12", "w6", "w7"];
\\ D_w = dim J(K_w)/2J(K_w) (prym_two_descent.out, local image dimensions modulo the image of K_w^x)
SB_D = [7, 26, 14, 3];
NFAIL = 0; NOK = 0;
chq(c, msg) = if (!c, NFAIL++; printf("CHECK FAILED: %s\n", msg), NOK++; printf("ok: %s\n", msg));
f2rank(M) = if (#M == 0 || #M~ == 0, 0, matrank(Mod(M, 2)));
f2eqspan(A1, A2) = my(r = f2rank(A1)); r == f2rank(A2) && r == f2rank(matconcat([A1, A2]));
f2annih(W, n) = { if (#W == 0, return(matid(n))); my(Kr = lift(matker(Mod(W~, 2)))); if (#Kr == 0, matrix(0, n), Kr~); }
f2ker(R, n) = if (#R~ == 0, matid(n), lift(matker(Mod(R, 2))));
\\ ---------------------------------------------------------------- global data
sb_init() = {
  my(R = RIN[1]);
  nfK = nfinit(K21);
  SBpr = concat(idealprimedec(nfK, 2), idealprimedec(nfK, 7));
  chq(apply(P -> [P.p, P.e, P.f], SBpr) == [[2, 3, 1], [2, 12, 1], [2, 6, 1], [7, 7, 3]], "primes of K21 above 2 and 7 in the order v (e = 3), w2 (e = 12), w3 (e = 6), p7 (e = 7, f = 3)");
  SBq = lift(Mod(1, K21) * polrecip(R[2])); SBq = lift(Mod(1, K21) * SBq / pollead(SBq));
  SBh = lift(Mod(1, K21) * polrecip(R[3]^2 - R[5] * R[4]^2)); SBh = lift(Mod(1, K21) * SBh / pollead(SBh));
  SBq = subst(SBq, t, x); SBh = subst(SBh, t, x);
  SBf = vector(2, k, subst(lift(Mod(1, K21) * polrecip(if (k == 1, F0, F1))), t, x));
  SBc = vector(2, k, pollead(SBf[k]));
  for (k = 1, 2, chq(poldegree(SBf[k]) == 6 && lift(Mod(1, K21) * (SBf[k] - SBc[k] * SBq * SBh)) == 0,
    Str("fRev_", k - 1, " = polrecip(F", k - 1, ") = c_k q h with q, h monic, the same for both twists")));
}
\\ reversed model data of Lean (DataBruin.lean qData, hData over qDen, hDen = 46): recheck q, h
sb_check_lean_qh(qD, hD, dq, dh) = {
  my(qq = x^2 + sum(i = 0, 1, nfbasistoalg(nfK, qD[i + 1]~) / dq * x^i), hh = x^4 + sum(i = 0, 3, nfbasistoalg(nfK, hD[i + 1]~) / dh * x^i));
  lift(Mod(1, K21) * (qq - SBq)) == 0 && lift(Mod(1, K21) * (hh - SBh)) == 0;
}
\\ ---------------------------------------------------------------- places
sb_place(i) = {
  my(W = Map(), pr = SBpr[i], al = nfbasistoalg(nfK, SB_AL[i]~), p = pr.p, E = Mod(1, K21), dec = idealprimedec(nfK, p));
  chq(idealhnf(nfK, al) == idealhnf(nfK, pr), Str("place ", SB_PNAME[i], ": M2's alpha generates the prime (p = ", p, ", e = ", pr.e, ", f = ", pr.f, ")"));
  if (p == 2, my(oth = [P | P <- dec, idealhnf(nfK, P) != idealhnf(nfK, pr)], F = matrix(#oth + 1, 2), vals = vector(#oth + 1));
    F[1, 1] = pr; F[1, 2] = 400; vals[1] = 1; for (j = 1, #oth, F[j + 1, 1] = oth[j]; F[j + 1, 2] = 400; vals[j + 1] = 0);
    E = nfbasistoalg(nfK, idealchinese(nfK, F, vals));
    chq(nfeltval(nfK, E - 1, pr) >= 400 && vecmin(apply(P -> nfeltval(nfK, E, P), oth)) >= 400, "CRT element E = 1 mod w^400, 0 mod w'^400"));
  mapput(W, "i", i); mapput(W, "pr", pr); mapput(W, "p", p); mapput(W, "e", pr.e); mapput(W, "al", al); mapput(W, "E", E);
  mapput(W, "modpr", nfmodprinit(nfK, pr)); mapput(W, "name", SB_PNAME[i]);
  W;
}
vw(W, c) = if (c == 0, oo, nfeltval(nfK, lift(c), mapget(W, "pr")));
\\ small representative in O_K of a w-integral c, congruent modulo w^N
redK(W, c, N) = {
  if (c == 0, return(Mod(0, K21)));
  my(p = mapget(W, "p"), cv = nfalgtobasis(nfK, c), d = denominator(cv), mm);
  if (d % p == 0, cv = nfeltmul(nfK, cv, mapget(W, "E")); d = denominator(cv); if (d % p == 0, error("redK: not w-integral")));
  mm = p^ceil(N / mapget(W, "e"));
  nfbasistoalg(nfK, centerlift(Mod(cv * d, mm) * Mod(d, mm)^(-1)));
}
\\ ---------------------------------------------------------------- components
\\ n = 1: F = K_w; n = 2: P1 = Y1^2 - B Y1 - A (ram = 1: Eisenstein, ram = 0: unramified); n = 4: tower over a ramified P1
sb_comp(W, n, A = 0, B = 0, ram = 0) = {
  my(C = Map(), P1 = 0, one, eF, fF, nu, Pi, rb, p = mapget(W, "p"));
  if (n == 1, one = Mod(1, K21); eF = 1; fF = 1; nu = [0]; Pi = mapget(W, "al"); rb = [1],
      P1 = Y1^2 - Mod(lift(B), K21) * Y1 - Mod(lift(A), K21);
      if (n == 2, one = Mod(1, P1); if (ram, eF = 2; fF = 1; nu = [0, 1]; Pi = Y1 * one; rb = [1, 0], eF = 1; fF = 2; nu = [0, 0]; Pi = mapget(W, "al") * one; rb = [1, FQ4]),
        one = Mod(Mod(1, P1), Y2^2 - Y2 + 1); eF = 2; fF = 2; nu = [0, 1, 0, 1]; Pi = Y1 * one; rb = [1, 0, FQ4, 0]));
  mapput(C, "W", W); mapput(C, "n", n); mapput(C, "P1", P1); mapput(C, "one", one); mapput(C, "eF", eF); mapput(C, "fF", fF);
  mapput(C, "nu", nu); mapput(C, "Pi", Pi); mapput(C, "rb", rb); mapput(C, "ej", eF * mapget(W, "e")); mapput(C, "A", A); mapput(C, "B", B);
  if (p == 2, mapput(C, "kel", if (fF == 1, [0, 1], [0, 1, FQ4, FQ4 + 1]) * FQ4^0));
  sb_setbasis(~C);
  C;
}
co(C, z) = {
  my(n = mapget(C, "n"), L);
  z = z * mapget(C, "one");
  if (n == 1, return([z]));
  L = lift(z);
  if (n == 2, return([Mod(lift(polcoef(L, 0, Y1)), K21), Mod(lift(polcoef(L, 1, Y1)), K21)]));
  my(c0 = lift(polcoef(L, 0, Y2)), c1 = lift(polcoef(L, 1, Y2)));
  [Mod(lift(polcoef(c0, 0, Y1)), K21), Mod(lift(polcoef(c0, 1, Y1)), K21), Mod(lift(polcoef(c1, 0, Y1)), K21), Mod(lift(polcoef(c1, 1, Y1)), K21)];
}
mk(C, v) = my(n = mapget(C, "n")); mapget(C, "one") * if (n == 1, v[1], n == 2, v[1] + v[2] * Y1, v[1] + v[2] * Y1 + (v[3] + v[4] * Y1) * Y2);
val(C, z) = { my(v = co(C, z), W = mapget(C, "W"), eF = mapget(C, "eF"), nu = mapget(C, "nu"), m = oo); for (i = 1, #v, if (v[i] != 0, m = min(m, eF * vw(W, v[i]) + nu[i]))); m; }
red(C, z, N) = { my(W = mapget(C, "W"), Nw = ceil(N / mapget(C, "eF")) + 1); mk(C, apply(c -> redK(W, c, Nw), co(C, z))); }
\\ residue of an integral element (dyadic: in F_4 = FQ4 field; at 7: in the residue field of nfmodpr)
res(C, z) = {
  my(v = co(C, z), W = mapget(C, "W"), rb = mapget(C, "rb"), mp = mapget(W, "modpr"), r = 0);
  for (i = 1, #v, if (rb[i] != 0 && v[i] != 0, my(q1 = nfmodpr(nfK, lift(v[i]), mp));
    if (mapget(W, "p") == 2, if (q1 != 0, r += rb[i] * FQ4^0), r += q1)));
  if (mapget(W, "p") == 2, r * FQ4^0, r);
}
liftres(C, r) = {
  my(W = mapget(C, "W"), n = mapget(C, "n"));
  if (mapget(W, "p") != 2, return(nfmodprlift(nfK, r, mapget(W, "modpr")) * mapget(C, "one")));
  my(pl = (r * FQ4^0).pol, a0 = polcoef(pl, 0) % 2, a1 = polcoef(pl, 1) % 2);
  if (mapget(C, "fF") == 1, if (a1, error("liftres")); return(a0 * mapget(C, "one")));
  mapget(C, "one") * (a0 + a1 * if (n == 2, Y1, Y2));
}
ksqrt(C, r) = if (mapget(mapget(C, "W"), "p") == 2, if (mapget(C, "fF") == 1, r, r^2), my(s); if (!issquare(r, &s), error("ksqrt")); s);
ktr(C, r) = if (mapget(C, "fF") == 1, r, r + r^2);
\\ standard basis: dyadic [Pi, 1 + Pi^t w_l (t odd < 2 e_F, w_l = 1 (, Y)), 1 + 4 w*], at 7 [Pi, u7]
sb_setbasis(~C) = {
  my(W = mapget(C, "W"), Pi = mapget(C, "Pi"), one = mapget(C, "one"), bas = List([Pi]), names = List(["Pi"]), fF = mapget(C, "fF"), ej = mapget(C, "ej"), n = mapget(C, "n"), wl);
  if (mapget(W, "p") != 2, listput(bas, SBu7 * one); listput(names, "u7"); mapput(C, "bas", Vec(bas)); mapput(C, "bnames", Vec(names)); return);
  wl = if (fF == 1, [one], [one, one * if (n == 2, Y1, Y2)]);
  forstep (tt = 1, 2 * ej - 1, 2, for (l = 1, fF, listput(bas, one + Pi^tt * wl[l]); listput(names, Str("1+Pi^", tt, "w", l))));
  listput(bas, one + 4 * wl[fF]); listput(names, "1+4w*");
  mapput(C, "bas", Vec(bas)); mapput(C, "bnames", Vec(names));
}
\\ ---------------------------------------------------------------- coordinates
\\ e integral (v_F(e) >= 0): returns [a, m, S]
coords(C, e) = {
  my(W = mapget(C, "W"), Pi = mapget(C, "Pi"), bas = mapget(C, "bas"), ej = mapget(C, "ej"), fF = mapget(C, "fF"), one = mapget(C, "one"),
     n0 = val(C, e), a = vector(#bas), m, z, S = one, NP, rr, d, pl, y);
  if (n0 == oo || n0 < 0, error("coords: valuation ", n0));
  a[1] = n0 % 2; m = (n0 + a[1]) / 2;
  if (mapget(W, "p") != 2,
    z = red(C, e * Pi^a[1] / Pi^(2 * m), 4); d = res(C, z);
    if (!issquare(d), a[2] = 1; z = red(C, z * bas[2], 4); d = res(C, z));
    S = red(C, liftres(C, ksqrt(C, d)), 4); return([a, m, S]));
  NP = 2 * ej + 6;
  z = red(C, e * Pi^a[1] / Pi^(2 * m), NP);
  rr = liftres(C, ksqrt(C, res(C, z))); z = red(C, z / rr^2, NP); S = rr;
  for (tt = 1, 2 * ej - 1,
    d = res(C, red(C, (z - 1) / Pi^tt, NP)); if (d == 0, next);
    if (tt % 2,
      pl = d.pol; for (l = 1, fF, if (polcoef(pl, l - 1) % 2, my(ix = 1 + (tt - 1) / 2 * fF + l); a[ix] = 1; z = red(C, z * bas[ix], NP))),
      rr = one + Pi^(tt / 2) * liftres(C, ksqrt(C, d)); z = red(C, z / rr^2, NP); S = red(C, S * rr, NP)));
  d = res(C, red(C, (z - 1) / 4, NP));
  if (ktr(C, d) != 0, a[#bas] = 1; z = red(C, z * bas[#bas], NP); d = res(C, red(C, (z - 1) / 4, NP)));
  y = [c | c <- mapget(C, "kel"), c^2 + c == d]; if (#y == 0, error("coords: Artin-Schreier"));
  rr = one + 2 * liftres(C, y[1]); z = red(C, z / rr^2, NP); S = red(C, S * rr, NP);
  [a, m, S];
}
\\ the replayable check of one certificate
verC(C, e, cert) = {
  my(a = cert[1], m = cert[2], S = cert[3], bas = mapget(C, "bas"), P = e, W = mapget(C, "W"), N);
  for (i = 1, #a, if (a[i] % 2, P *= bas[i]));
  N = 2 * m + 1 + if (mapget(W, "p") == 2, 2 * mapget(C, "ej"), 0);
  val(C, S) == 0 && val(C, P - mapget(C, "Pi")^(2 * m) * S^2) >= N;
}
\\ ---------------------------------------------------------------- scaling of a polynomial G(X) at a root tau = al^s tau'
\\ returns [r, c, D, Gh]: Gh(X') = lam^2 G(al^s X') in O_K[X'] exactly, lam = al^r E^c D (D odd); G constant: s ignored
sb_scale(W, G, s, sq = 1) = {
  my(al = mapget(W, "al"), p = mapget(W, "p"), cs, r, c = 0, D, gv, pw = if (sq, 2, 1));
  cs = if (type(G) == "t_POL" && variable(G) == x, vector(poldegree(G) + 1, i, Mod(polcoef(G, i - 1, x), K21) * al^(s * (i - 1))), [Mod(G, K21)]);
  gv = vecmin(apply(z -> vw(W, z), cs));
  r = ceil(-gv / pw); cs = cs * al^(pw * r);
  while (vecmax(apply(z -> denominator(nfalgtobasis(nfK, z)) % p == 0, cs)), c++; cs = cs * mapget(W, "E")^pw; if (c > 3, error("sb_scale")));
  D = lcm(apply(z -> denominator(nfalgtobasis(nfK, z)), cs)); cs = cs * D^pw;
  [r, c, D, cs];
}
evGh(C, cs, t) = { my(r = 0); forstep (i = #cs, 1, -1, r = r * t + cs[i]); r * mapget(C, "one"); }
\\ ---------------------------------------------------------------- roots: tree search in O_F, Newton, Hensel certificate
\\ gh = coefficient vector (constant first) of the scaled factor, integral; returns list of [t', v(gh(t')), v(gh'(t'))]
sb_roots(C, gh, dtgt, kmax = 400) = {
  my(Pi = mapget(C, "Pi"), one = mapget(C, "one"), dg = vector(#gh - 1, i, i * gh[i + 1]), st = List([[0 * one, 0]]), out = List(), W = mapget(C, "W"), kel);
  kel = if (mapget(W, "p") == 2, mapget(C, "kel"), 0);
  while (#st, my(nd = st[#st], r = nd[1], k = nd[2], v1, v2, Q, mu, cq, Pb, rts);
    listpop(st);
    v1 = val(C, evGh(C, gh, r)); v2 = val(C, evGh(C, dg, r));
    if (v1 > 2 * v2 && v2 < k,
      while (v1 - v2 < dtgt, r = red(C, r - evGh(C, gh, r) / evGh(C, dg, r), 2 * dtgt + 20); v1 = val(C, evGh(C, gh, r)); v2 = val(C, evGh(C, dg, r)));
      listput(out, [r, v1, v2]); next);
    if (k > kmax, error("sb_roots: depth"));
    Q = subst(Pol(Vecrev(gh), Xs), Xs, r + Pi^k * Xs);
    cq = vector(poldegree(Q, Xs) + 1, i, polcoef(Q, i - 1, Xs));
    mu = vecmin(apply(z -> val(C, z), cq));
    Pb = vector(#cq, i, if (cq[i] == 0, 0, res(C, red(C, cq[i] / Pi^mu, 4))));
    if (mapget(W, "p") == 2,
      rts = [z | z <- kel, sum(i = 1, #Pb, Pb[i] * z^(i - 1)) == 0],
      my(fa = factor(Pol(Vecrev(Pb), 'zz))); rts = [-polcoef(fa[i, 1], 0) / polcoef(fa[i, 1], 1) | i <- [1 .. #fa~], poldegree(fa[i, 1]) == 1]);
    foreach (rts, z, listput(st, [red(C, r + Pi^k * liftres(C, z), 2 * k + 20), k + 1])));
  Vec(out);
}
\\ conjugates of a tower element (n = 2: Y1 -> B - Y1; n = 4: also Y2 -> 1 - Y2)
sb_conjs(C, z) = {
  my(n = mapget(C, "n"), v = co(C, z), B = Mod(lift(mapget(C, "B")), K21));
  if (n == 1, return([z]));
  if (n == 2, return([z, mk(C, [v[1] + B * v[2], -v[2]])]));
  my(s1 = (w -> [w[1] + B * w[2], -w[2], w[3] + B * w[4], -w[4]]), s2 = (w -> [w[1] + w[3], w[2] + w[4], -w[3], -w[4]]));
  [z, mk(C, s1(v)), mk(C, s2(v)), mk(C, s1(s2(v)))];
}
\\ scaled factor at W for g (monic, variable x): s = floor of the least root valuation, gh = mu g(al^s X') integral
sb_gscale(W, g) = {
  my(n = poldegree(g), s = floor(vecmin(vector(n, i, my(c = polcoef(g, i - 1, x)); if (c == 0, oo, vw(W, c) / (n - i + 1))))), sc = sb_scale(W, g, s, 0));
  [s, sc];
}
\\ ---------------------------------------------------------------- element certificates
\\ G: constant or polynomial in x; C carries "s" and "tp" (root tau = al^s tau', tau' ~ tp, v(tau' - tp) >= "del")
\\ returns [name, r, c, D, Ghred (list of zk coordinate columns), Mg, a, m, S (zk columns), N]
sb_cert(C, G, name) = {
  my(W = mapget(C, "W"), isc = !(type(G) == "t_POL" && variable(G) == x), sc = sb_scale(W, G, if (isc, 0, mapget(C, "s"))), cs = sc[4], eh, n0, N, Mg, csr, ehr, ce, p = mapget(W, "p"), ej = mapget(C, "ej"));
  eh = if (isc, cs[1] * mapget(C, "one"), evGh(C, cs, mapget(C, "tp")));
  n0 = val(C, eh); N = n0 + (n0 % 2) + 1 + if (p == 2, 2 * ej, 0);
  Mg = ceil(N / ej); csr = apply(z -> redK(W, z, Mg * mapget(W, "e")), cs);
  if (vecmax(apply(z -> denominator(nfalgtobasis(nfK, z)), cs)) != 1, error("sb_cert: scaled coefficients not integral"));
  ehr = if (isc, csr[1] * mapget(C, "one"), evGh(C, csr, mapget(C, "tp")));
  ce = coords(C, ehr);
  if (!verC(C, ehr, ce), error("sb_cert: verification failed for ", name));
  if (!isc && mapget(C, "del") < N, error("sb_cert: root precision ", mapget(C, "del"), " < ", N, " for ", name));
  [name, sc[1], sc[2], sc[3], apply(z -> nfalgtobasis(nfK, z), csr), Mg, ce[1], ce[2], apply(z -> nfalgtobasis(nfK, z), co(C, ce[3])), N, ehr];
}
\\ Eisenstein model of K_w(sqrt D) (ramified): [A, B, t] with P1 = Y1^2 - B Y1 - A, v(A) = 1, v(B) >= 1
sb_eisen(W, D, K = 0) = {
  my(C0 = sb_comp(W, 1), al = mapget(W, "al"), e = mapget(W, "e"), n0 = vw(W, D), z, tt = 0, d, rr, NP = 2 * e + 8, A, B);
  if (!K, K = 2 * e + 4);
  if (n0 % 2, return([redK(W, D / al^(n0 - 1), K), 0, 0]));
  z = redK(W, D / al^n0, NP); rr = liftres(C0, ksqrt(C0, res(C0, z))); z = redK(W, z / rr^2, NP);
  for (s1 = 1, 2 * e - 1, d = res(C0, redK(W, (z - 1) / al^s1, NP)); if (d == 0, next);
    if (s1 % 2, tt = s1; break); rr = 1 + al^(s1 / 2) * liftres(C0, ksqrt(C0, d)); z = redK(W, z / rr^2, NP));
  if (!tt, error("sb_eisen: unit of depth >= 2e (unramified or trivial class)"));
  my(k = (tt - 1) / 2); A = redK(W, (z - 1) / al^(2 * k), K); B = redK(W, -2 / al^k, K);
  [A, B, tt];
}
