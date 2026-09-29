\\ descent_set_sieve_probe.gp: feasibility probe (not a proof step). Selmer set of the descent class
\\ delta(P) = [Q1(P)] (or [Q3(P)]) over K21 for P in C(Q), from K21(S,2) and exact local images at good primes.
\\ Input: ../earlier-computations/bruin_form.gp. GRH bnf: probe only.
\\ Local image at a good prime p (p odd, no prime above p in S): every point of C(F_p) lifts to C(Q_p) (smooth),
\\ and for a lift P and a prime pr above p, Q1(P) (or Q3(P) when Q1 vanishes mod pr) is a pr-unit whose square
\\ class is its quadratic residue symbol; so Im_p = { (chi_pr)_pr : Pbar in C(F_p) } exactly, provided Q1 and Q3
\\ never both vanish mod pr at a point of C(F_p) (checked; such a pr would have to go into S).
\\ Run from code/descent: gp -q descent_set_sieve_probe.gp < /dev/null
default(parisizemax, 6*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
bnf = bnfinit(K21, 1); nf = bnf.nf;
chk(c, msg) = if (!c, error("FAILED: ", msg), print("ok: ", msg));
T0 = getwalltime();
PMAX = if (type(PMAX) == "t_INT", PMAX, 400);
\\ S: primes above 2 and 7, and the primes in the support of cB and of the contents of Q1, Q2, Q3
cf(Q, i, j, k) = polcoef(polcoef(polcoef(Q, i, x), j, y), k, z);
mons2 = [[2,0,0], [1,1,0], [1,0,1], [0,2,0], [0,1,1], [0,0,2]];
coefs2(Q) = vector(6, j, cf(Q, mons2[j][1], mons2[j][2], mons2[j][3]));
S = concat(idealprimedec(nf, 2), idealprimedec(nf, 7));
addS(I) = { my(fa = idealfactor(nf, I)); for (i = 1, #fa~, my(pr = fa[i,1]); if (pr.p != 2 && pr.p != 7, S = concat(S, [pr]))); };
addS(cB);
foreach([Q1, Q2, Q3], Q, my(c = coefs2(Q), I = 0); for (j = 1, 6, if (c[j] != 0, I = if (I == 0, idealhnf(nf, c[j]), idealadd(nf, I, c[j])))); addS(I));
{ my(L = List()); for (i = 1, #S, my(new = 1); for (j = 1, #L, if (S[i] == L[j], new = 0)); if (new, listput(L, S[i]))); S = Vec(L); }
print("S: ", vector(#S, i, [S[i].p, S[i].f, S[i].e]));
Sp = Set(vector(#S, i, S[i].p));
U = bnfunits(bnf, S);            \\ U[1]: S-unit generators (S-units, then fundamental units, then torsion)
G = vector(#U[1], j, nffactorback(nf, U[1][j])); dimK = #G;   \\ expanded: on a famat nfmodpr returns a t_POL, and issquare() of a t_POL is not the residue field test
print("dim K21(S,2) = ", dimK, " (", #S, " primes in S, unit rank ", #bnf.fu, ", torsion ", bnf.tu[1], ")");
\\ coordinates in K21(S,2) of alpha (must have even valuation outside S)
sqfreeS(alpha) = {
  my(fa = idealfactor(nf, alpha), I = 1);
  for (i = 1, #fa~, my(pr = fa[i,1]); if (!setsearch(Sp, pr.p), if (fa[i,2] % 2, error("odd valuation outside S at ", pr.p)); I = idealmul(nf, I, idealpow(nf, pr, fa[i,2] \ 2))));
  my(g = bnfisprincipal(bnf, I, 3)); if (g[1] != vector(#g[1], i, 0)~, error("not principal"));
  g = nfbasistoalg(nf, g[2]);
  my(e = bnfisunit(bnf, alpha / g^2, U)); if (#e == 0, error("not an S-unit after removing squares"));
  vector(dimK, i, e[i] % 2);
}
ev(Q, P) = substvec(Q, [x, y, z], P);
delta_class(P) = { my(q = ev(Q1, P)); if (q == 0, q = ev(Q3, P)); sqfreeS(Mod(q, K21)); };
Pts = [[0,0,1], [1,1,1], [2,0,1], [-1,0,1]];
dc = vector(4, i, delta_class(Pts[i]));
print("delta classes of P0..P3: ", dc);
chk(dc[1] == dc[3] && dc[2] == dc[4] && dc[1] != dc[2], "delta(P0) = delta(P2) != delta(P1) = delta(P3)");
tomask(v) = sum(i = 1, #v, v[i] * 2^(i-1));
known = Set([tomask(dc[1]), tomask(dc[2])]);
\\ characters of the generators at a prime pr (a pr-unit each: pr not in S)
ischi(e, modpr) = { my(r = nfmodpr(nf, e, modpr)); if (r == 0, error("zero residue")); if (issquare(r), 0, 1) };
\\ points of C(F_p), projective, as integer triples
ptsmod(p) = {
  my(L = List());
  for (x0 = 0, p-1, my(f = substvec(F, [x, z], [x0, 1])); foreach(polrootsmod(f, p), r, listput(L, [x0, lift(r), 1])));
  my(f = substvec(F, [y, z], [1, 0])); foreach(polrootsmod(f, p), r, listput(L, [lift(r), 1, 0]));
  if (substvec(F, [x, y, z], [1, 0, 0]) % p == 0, listput(L, [1, 0, 0]));
  Vec(L);
}
\\ residue class of a quadric at a point mod pr, as an element of the residue field
quadmod(cq, P) = sum(j = 1, 6, cq[j] * P[1]^mons2[j][1] * P[2]^mons2[j][2] * P[3]^mons2[j][3]);
surv = [0 .. 2^dimK - 1];   \\ all classes, as bit masks
nused = 0;
{forprime(p = 3, PMAX,
  if (setsearch(Sp, p) || p == 7, next);
  my(dec = idealprimedec(nf, p), g = #dec, mp = vector(g, i, nfmodprinit(nf, dec[i])));
  my(chiG = vector(dimK, j, sum(i = 1, g, ischi(G[j], mp[i]) * 2^(i-1))));
  my(c1 = vector(g, i, vector(6, j, nfmodpr(nf, coefs2(Q1)[j], mp[i]))), c3 = vector(g, i, vector(6, j, nfmodpr(nf, coefs2(Q3)[j], mp[i]))));
  my(im = List(), pts = ptsmod(p));
  foreach(pts, P,
    my(m = 0);
    for (i = 1, g,
      my(q = quadmod(c1[i], P));
      if (q == 0, q = quadmod(c3[i], P));
      if (q == 0, error("Q1 and Q3 both vanish mod a prime above ", p, " at ", P));
      if (!issquare(q), m += 2^(i-1)));
    listput(im, m));
  im = Set(im);
  my(new = List());
  foreach(surv, c, my(m = 0, cc = c, j = 1); while (cc, if (cc % 2, m = bitxor(m, chiG[j])); cc \= 2; j++); if (setsearch(im, m), listput(new, c)));
  nused++;
  my(before = #surv); surv = Vec(new);
  if (#surv < before || nused % 10 == 0, print("p = ", p, ": ", g, " primes, #C(F_p) = ", #pts, ", |Im_p| = ", #im, ", survivors ", #surv, "  (", (getwalltime() - T0) \ 1000, " s)"));
  if (#setminus(known, Set(surv)) > 0, error("a known class was removed at p = ", p));
  if (#surv <= 2, break))};
print("survivors: ", #surv, "; known classes among them: ", #setintersect(known, Set(surv)));
print("survivor masks: ", if (#surv <= 64, surv, "(too many to print)"));
print("done: ", (getwalltime() - T0) / 1000., " s");
