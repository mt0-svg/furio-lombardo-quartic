\\ sieve_design_run.gp: design run of the Lean sieve of M1 (not trusted: the Lean kernel rechecks every datum).
\\ Good primes 5..23: rings R = F_p[x]/(phi) for the irreducible factors phi of f mod p, residue maps
\\ rho(zkE a) = Dz^-1 sum a_i zkNum_i(x), quadratic characters chi(w) = w^((q-1)/2); normalized points of C(F_p)
\\ (y = 1; else x = 1; else z = 1); for each point and ring the character of Q1(P) (or Q3(P) when rho(Q1(P)) = 0).
\\ Then the 3-adic test in Z/27 (theta -> 17) and the 2-adic test at P2c (e = 6).
default(parisizemax, 6*10^9); default(nbthreads, 1);
read("descent_search_lib.gp");
Fi(P) = substvec(F, [x, y, z], P);
evq(cr, P) = sum(j = 1, 6, cr[j] * P[1]^mons2[j][1] * P[2]^mons2[j][2] * P[3]^mons2[j][3]);
zkpol(a) = sum(i = 1, 21, a[i] * Polrev(zkNum[i], b));      \\ Dz * zkE a as a polynomial in b
rho(a, p, phi) = Mod(Mod(zkpol(a), p), phi) / Mod(Dz, p);
chi(w, p, phi) = { my(q = p^poldegree(phi), c = w^((q-1)/2)); if (c == 1, 0, if (c == -1, 1, -1)) };
normpts(p) = {
  my(L = List());
  for (x0 = 0, p-1, for (z0 = 0, p-1, if (Fi([x0, 1, z0]) % p == 0, listput(L, [x0, 1, z0]))));
  for (z0 = 0, p-1, if (Fi([1, 0, z0]) % p == 0, listput(L, [1, 0, z0])));
  if (Fi([0, 0, 1]) % p == 0, listput(L, [0, 0, 1]));
  Vec(L);
}
rings = List(); rows = List(); blocks = List();
{
forprime(p = 5, 23, if (p == 7, next);
  my(fa = factor(K21 * Mod(1, p))[, 1], k = #fa, phis = vector(k, j, lift(fa[j])), pts = normpts(p), im = List());
  for (j = 1, k, listput(rings, [p, phis[j]]); listput(rows, vector(18, i, chi(rho(G[i], p, phis[j]), p, phis[j]))));
  foreach(pts, P, my(v = vector(k));
    for (j = 1, k, my(q1 = evq(vector(6, t, rho(QcZ[1][t], p, phis[j])), P), q3 = evq(vector(6, t, rho(QcZ[3][t], p, phis[j])), P), c = chi(q1, p, phis[j]));
      if (c < 0, c = chi(q3, p, phis[j]));
      if (c < 0, error("both non units at ", p, " ", P, " ring ", j));
      v[j] = c);
    listput(im, v));
  listput(blocks, [p, k, Set(im)]);
  print("p = ", p, ": degrees ", apply(poldegree, phis), ", ", #pts, " points, |V_p| = ", #Set(im)));
}
M = matrix(#rows, 18, i, j, rows[i][j]);
print("rank M over F2: ", matrank(M * Mod(1, 2)), " (", #rows, " rows)");
for (i = 1, 18, if (vecmin(M[, i]) < 0, error("gen char")));
\\ left inverse of M over F2
Lf = matsolve(M~ * M * Mod(1,2), M~ * Mod(1,2));
Lm = lift(Lf);
if (lift(Lm * M * Mod(1,2)) != matid(18), error("left inverse"));
\\ combinations
combos = [[]];
foreach(Vec(blocks), bl, my(nc = List()); foreach(combos, c, foreach(bl[3], v, listput(nc, concat(c, v)))); combos = Vec(nc));
print("combinations: ", #combos);
surv = List();
foreach(combos, c, my(e = lift(Lm * c~ * Mod(1,2))); if (lift(M * e * Mod(1,2)) == c~, listput(surv, e~)));
surv = Set(Vec(surv));
print("survivors: ", #surv);
\\ known classes: delta of the rational points (descent_data_lib Q1 at the known points)
celt(e) = { my(r = zkc(1)); for (i = 1, 18, if (e[i], r = mulz(r, G[i]))); r };
\\ 3-adic in Z/27
r27 = 17; if (subst(K21, b, r27) % 27 != 0, error("r27"));
rho27(a) = Mod(subst(zkpol(a), b, r27), 27) / Mod(Dz, 27);
sq27 = Set(vector(27, s, Mod(s-1, 27)^2));
pts27 = List();
{
for (x0 = 0, 26, for (z0 = 0, 26, if (Fi([x0, 1, z0]) % 27 == 0, listput(pts27, [x0, 1, z0]))));
for (y0 = 0, 26, for (z0 = 0, 26, if (y0 % 3 == 0 && z0 % 3 == 0 && Fi([1, y0, z0]) % 27 == 0, listput(pts27, [1, y0, z0]))));
}
{
for (x0 = 0, 26, for (y0 = 0, 26, if (x0 % 3 == 0 && y0 % 3 == 0 && Fi([x0, y0, 1]) % 27 == 0, listput(pts27, [x0, y0, 1]))));
}
print("normalized triples mod 27 on F = 0: ", #pts27);
Q27 = vector(3, i, vector(6, t, rho27(QcZ[i][t])));
G27 = vector(18, i, rho27(G[i]));
kill27(e) = {
  my(g = prod(i = 1, 18, if (e[i], G27[i], 1)));
  foreach(pts27, P, my(q1 = evq(Q27[1], P) * g, q3 = evq(Q27[3], P) * g);
    if (setsearch(sq27, q1) && setsearch(sq27, q3), return(0)));
  1;
}
surv3 = [e | e <- surv, !kill27(e)];
print("after Z/27: ", #surv3, " ", surv3);
\\ known classes: e such that Q(P) G_e is a square, for P0..P3 = (0:0:1), (1:1:1), (2:0:1), (-1:0:1)
issq(a) = #nfroots(K21, X^2 - a) > 0;
qsel(P) = { my(q = Mod(evq(Qc[1], P), K21)); if (q == 0, q = Mod(evq(Qc[3], P), K21)); q };
Gel(e) = prod(i = 1, 18, if (e[i], Mod(zkr(G[i]), K21), 1));
known = vector(4, k, my(P = [[0,0,1],[1,1,1],[2,0,1],[-1,0,1]][k], c = [e | e <- surv3, issq(qsel(P) * Gel(e))]); if (#c != 1, error("known ", k)); c[1]);
print("known classes: ", known);
rest = setminus(Set(surv3), Set(known));
print("to kill at 2: ", rest);
\\ 2-adic at a prime pr | 2 with principal generator pg (residue field F_2): leaves as in two_adic_exclusion_w6.gp.
\\ Leaf kinds: [1, i, v] v = v(G_e Q_i(P0)) odd, v(Q_i(P0)) < e m; [2, i, 2j, k] v(G_e Q_i(P0)) = 2j, the unit
\\ A0 = G_e Q_i(P0) / pg^(2j) has v(A0 - s^2) = k odd < 2e for some s, and e m + v(G_e) >= 2j + 2e.
vPr(t, pr) = nfeltval(nf, lift(t), pr);
defect(A, pr, pg) = {
  my(s = Mod(1, K21), k, e = pr.e);
  for (it = 1, 60, k = vPr(A - s^2, pr);
    if (k >= 2*e || k % 2 == 1, return([k, s]));
    my(s2 = s + pg^(k/2)); if (vPr(A - s2^2, pr) > k, s = s2, return([k, s])));
  [vPr(A - s^2, pr), s];
}
leafres(P, m, pr, pg) = {
  my(e = pr.e, res = vector(#rest));
  for (si = 1, #rest,
    my(wv = Gel(rest[si]), vw = vPr(wv, pr), done = 0);
    foreach([1, 3], qi,
      if (!done,
        my(q = Mod(evq(Qc[qi], P), K21));
        if (q != 0,
          my(v = vPr(q, pr));
          if (v < e * m,
            if ((v + vw) % 2 == 1,
              res[si] = [1, qi, v + vw]; done = 1,
              my(j2 = v + vw, A0 = wv * q / pg^j2, dk = defect(A0, pr, pg));
              if (dk[1] % 2 == 1 && dk[1] < 2*e && e * m + vw >= j2 + 2*e, res[si] = [2, qi, j2, dk[1]]; done = 1))))));
    if (!done, return(0)));
  res;
}
twoadic(pr, pg, maxm) = {
  my(leaves = List(), stack = List(), bad = 0);
  for (s1 = 0, 1, for (s2 = 0, 1,
    listput(stack, [[s1, s2, 1], 1, [1, 2]]);
    if (s2 == 0, listput(stack, [[1, s1, s2], 1, [2, 3]]));
    if (s1 == 0 && s2 == 0, listput(stack, [[s1, 1, s2], 1, [1, 3]]))));
  while (#stack,
    my(it = stack[#stack], P = it[1], m = it[2], fr = it[3], r);
    listpop(stack);
    if (Fi(P) % 2^m == 0,
      r = leafres(P, m, pr, pg);
      if (r != 0, listput(leaves, [P, m, r]),
        if (m >= maxm, bad++,
          for (d1 = 0, 1, for (d2 = 0, 1, my(Q = P); Q[fr[1]] += d1 * 2^m; Q[fr[2]] += d2 * 2^m; listput(stack, [Q, m + 1, fr])))))));
  [Vec(leaves), bad];
}
Sg2 = vector(3, i, Mod(zkr(G[12 + i]), K21));
{
for (i = 1, 3, my(t = gettime(), r = twoadic(S[i], Sg2[i], 9));
  print("prime ", i, " above 2 (e = ", S[i].e, "): ", #r[1], " leaves, ", r[2], " unresolved at depth 9 (", gettime() - t, " ms)");
  if (r[2] == 0, print("  max m ", vecmax(apply(L -> L[2], r[1])), " kinds ", vector(#rest, si, [#[L | L <- r[1], L[3][si][1] == 1], #[L | L <- r[1], L[3][si][1] == 2]]))));
}
