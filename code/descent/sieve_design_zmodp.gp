\\ sieve_design_zmodp.gp: good prime sieve with degree one primes only (residue maps O -> Z/p, theta -> r),
\\ to see whether ZMod p characters alone reach the 8 survivors and full rank 18 (Lean M1 design).
default(parisizemax, 4*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
bnf = bnfinit(K21, 1); nf = bnf.nf;
P2 = idealprimedec(nf, 2); P3 = idealprimedec(nf, 3); P7 = idealprimedec(nf, 7); P439 = idealprimedec(nf, 439);
pr3 = [pr | pr <- P3, pr.f == 1][1];
pr439 = [pr | pr <- P439, pr.f == 1 && idealval(nf, b - 125, pr) > 0][1];
S = concat(P2, [P7[1], pr3, pr439]);
G = concat([Mod(-1, K21)], vector(11, i, Mod(nfbasistoalg(nf, bnf.fu[i]), K21)));
G = concat(G, vector(6, i, Mod(nfbasistoalg(nf, bnfisprincipal(bnf, S[i], 1)[2]), K21)));
Dbez = 2*7*45613*462191*249279053;
mons2 = [[2,0,0], [1,1,0], [1,0,1], [0,2,0], [0,1,1], [0,0,2]];
cf(Q, i, j, k) = polcoef(polcoef(polcoef(Q, i, x), j, y), k, z);
coefs2(Q) = vector(6, j, Mod(cf(Q, mons2[j][1], mons2[j][2], mons2[j][3]), K21));
c1 = coefs2(Q1); c3 = coefs2(Q3);
res(e, p, r) = { my(q = lift(e), d = denominator(content(q))); Mod(subst(q * d, b, r), p) / Mod(d, p) };
leg(v) = { if (v == 0, error("zero")); if (issquare(v), 0, 1) };
evq(cr, P) = sum(j = 1, 6, cr[j] * P[1]^mons2[j][1] * P[2]^mons2[j][2] * P[3]^mons2[j][3]);
ptsmod(p) = {
  my(L = List());
  for (x0 = 0, p-1, for (z0 = 0, p-1, if (substvec(F, [x, y, z], [x0, 1, z0]) % p == 0, listput(L, [x0, 1, z0]))));
  for (z0 = 0, p-1, if (substvec(F, [x, y, z], [1, 0, z0]) % p == 0, listput(L, [1, 0, z0])));
  if (substvec(F, [x, y, z], [0, 0, 1]) % p == 0, listput(L, [0, 0, 1]));
  Vec(L);
}
rows = List(); blocks = List(); nsurv = 2^18;
{
forprime(p = 5, 400, if (Dbez % p == 0, next);
  my(rts = [lift(r) | r <- Vec(polrootsmod(K21, p))]);
  rts = [r | r <- rts, !(p == 439 && r == 125)];
  if (#rts == 0, next);
  my(k = #rts, Mp = matrix(k, 18, i, j, leg(res(G[j], p, rts[i]))));
  my(c1r = vector(k, i, vector(6, j, res(c1[j], p, rts[i]))), c3r = vector(k, i, vector(6, j, res(c3[j], p, rts[i]))));
  my(im = List(), pts = ptsmod(p));
  foreach(pts, P, my(v = vector(k));
    for (i = 1, k, my(q = evq(c1r[i], P)); if (q == 0, q = evq(c3r[i], P)); if (q == 0, error("both vanish")); v[i] = leg(q));
    listput(im, v));
  im = Set(im);
  for (i = 1, k, listput(rows, Mp[i,]));
  listput(blocks, [p, k, im]);
  my(M = matrix(#rows, 18, i, j, rows[i][j]) * Mod(1, 2));
  print("p = ", p, " roots ", k, " |C(F_p)| = ", #pts, " |Im| = ", #im, " rank ", matrank(M)));
}
