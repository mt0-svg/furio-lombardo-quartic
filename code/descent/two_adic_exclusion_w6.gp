\\ two_adic_exclusion_w6.gp: 2-adic exclusion of the two survivors not killed at 3, at the prime P2c (e = 6) only.
\\ Leaves: classes of triples mod 2^m (first odd coordinate normalised to 1), refined until the valuation
\\ v of Q(P0) at P2c (Q = Q1 or Q3) is below 6m; leaf kinds: 1 = v(w Q) odd, 2 = v(w Q) = 2j even with a unit
\\ defect certificate (s, k): v(A0' - s^2) = k odd, k <= 11, A0' = w Q(P0) / lc^(2j), and 6m + v(w) >= 2j + 12.
default(parisizemax, 4*10^9);
default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
bnf = bnfinit(K21, 1); nf = bnf.nf;
dat = read("descent_frozen_data.bin");
G = dat[4]; Qc = dat[5];
F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
Fi(P) = substvec(F, [x, y, z], P);
mons2 = [[2,0,0], [1,1,0], [1,0,1], [0,2,0], [0,1,1], [0,0,2]];
evq(cr, P) = sum(j = 1, 6, cr[j] * P[1]^mons2[j][1] * P[2]^mons2[j][2] * P[3]^mons2[j][3]);
P2 = idealprimedec(nf, 2); pc = [pr | pr <- P2, pr.e == 6][1];
lc = G[15];
print("v_P2c of generators ", vector(18, j, nfeltval(nf, lift(G[j]), pc)));
surv = [[1,1,1,0,1,0,0,1,0,0,0,1,1,0,1,0,0,0], [1,0,1,0,1,1,0,0,1,1,0,0,1,0,1,0,0,0]];
celt(e) = prod(j = 1, 18, G[j]^e[j]);
vP(e) = nfeltval(nf, lift(e), pc);
\\ unit defect by greedy lifting of s (residue field F_2): stop at odd k or k >= 12
defect(A) = {
  my(s = Mod(1, K21), k);
  for (it = 1, 40,
    k = vP(A - s^2);
    if (k >= 12 || k % 2 == 1, return([k, s]));
    my(s2 = s + lc^(k/2));
    if (vP(A - s2^2) > k, s = s2, return([k, s])));
  [vP(A - s^2), s];
}
leafres(P, m) = {
  my(res = vector(#surv));
  for (si = 1, #surv,
    my(wv = celt(surv[si]), vw = vP(wv), done = 0);
    foreach([1, 3], qi,
      if (!done,
        my(q = Mod(evq(Qc[qi], P), K21));
        if (q != 0,
          my(v = vP(q));
          if (v < 6 * m,
            if ((v + vw) % 2 == 1,
              res[si] = [1, qi, v + vw]; done = 1,
              my(j2 = v + vw, A0 = wv * q / lc^j2, dk = defect(A0));
              if (dk[1] % 2 == 1 && dk[1] <= 11 && 6 * m + vw >= j2 + 12, res[si] = [2, qi, j2, dk[1]]; done = 1))))));
    if (!done, return(0)));
  res;
}
leaves = List(); stack = List();
{
for (s1 = 0, 1, for (s2 = 0, 1,
  listput(stack, [[s1, s2, 1], 1, [1, 2]]);
  if (s2 == 0, listput(stack, [[1, s1, s2], 1, [2, 3]]));
  if (s1 == 0 && s2 == 0, listput(stack, [[s1, 1, s2], 1, [1, 3]]))));
}
{
while (#stack,
  my(it = stack[#stack], P = it[1], m = it[2], fr = it[3], r);
  listpop(stack);
  if (Fi(P) % 2^m == 0,
    r = leafres(P, m);
    if (r != 0, listput(leaves, [P, m, r]),
      if (m >= 8, print("depth limit at ", P),
        for (d1 = 0, 1, for (d2 = 0, 1, my(Q = P); Q[fr[1]] += d1 * 2^m; Q[fr[2]] += d2 * 2^m; listput(stack, [Q, m + 1, fr])))))));
}
print(#leaves, " leaves");
foreach(leaves, L, print(L));
