\\ sieve_design_degree_one.gp: Selmer set sieve with the generators -1, fundamental units, S-prime generators, using only
\\ degree one primes (residue maps b -> r mod p) at good primes, then the prime P3 (b -> 2 mod 3) at 3 (Lean M1 planning).
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
dimK = #G;
\\ residue of an element of K21 at (p, r): numerator/denominator evaluated mod p
res(e, p, r) = { my(q = lift(e), d = denominator(content(q))); Mod(subst(q * d, b, r), p) / Mod(d, p) };
chi(e, p, r) = { my(v = res(e, p, r)); if (v == 0, error("zero residue ", p, " ", r)); if (issquare(v), 0, 1) };
cf(Q, i, j, k) = polcoef(polcoef(polcoef(Q, i, x), j, y), k, z);
mons2 = [[2,0,0], [1,1,0], [1,0,1], [0,2,0], [0,1,1], [0,0,2]];
coefs2(Q) = vector(6, j, Mod(cf(Q, mons2[j][1], mons2[j][2], mons2[j][3]), K21));
c1 = coefs2(Q1); c3 = coefs2(Q3);
ev(c, P) = sum(j = 1, 6, c[j] * P[1]^mons2[j][1] * P[2]^mons2[j][2] * P[3]^mons2[j][3]);
d0m = Mod(d0, K21); d1m = Mod(d1, K21);
\\ coordinates of delta0, delta1: use the characters at many primes and solve
ptsmod(p) = {
  my(L = List());
  for (x0 = 0, p-1, my(f = substvec(F, [x, z], [x0, 1])); foreach(polrootsmod(f, p), r, listput(L, [x0, lift(r), 1])));
  my(f = substvec(F, [y, z], [1, 0])); foreach(polrootsmod(f, p), r, listput(L, [lift(r), 1, 0]));
  if (substvec(F, [x, y, z], [1, 0, 0]) % p == 0, listput(L, [1, 0, 0]));
  Vec(L);
}
\\ character matrix at degree one primes
chars = List();
{ forprime(p = 5, 3000, if (p == 7 || p == 439 || p == 3, next); foreach(polrootsmod(K21, p), r, listput(chars, [p, lift(r)]))); }
CM = matrix(#chars, dimK, i, j, chi(G[j], chars[i][1], chars[i][2])) * Mod(1, 2);
print("character rank: ", matrank(CM), " from ", #chars, " degree one primes");
\\ pick 18 independent rows greedily
sel = List(); Mcur = matrix(0, dimK);
{ for (i = 1, #chars, my(M2 = matconcat([Mcur; CM[i,]])); if (matrank(M2) > matrank(Mcur), Mcur = M2; listput(sel, chars[i])); if (#sel == dimK, break)); }
print("18 character primes: ", sel);
\\ class of delta0, delta1 in the basis G (solve with the selected characters)
Msel = matrix(dimK, dimK, i, j, chi(G[j], sel[i][1], sel[i][2])) * Mod(1, 2);
cls(e) = lift(matsolve(Msel, vector(dimK, i, chi(e, sel[i][1], sel[i][2]))~ * Mod(1, 2)))~;
v0 = cls(d0m); v1 = cls(d1m); print("delta0 coords ", v0, "  delta1 coords ", v1);
tomask(v) = sum(i = 1, #v, v[i] * 2^(i-1));
known = Set([tomask(v0), tomask(v1)]);
\\ sieve at degree one primes of good p
surv = [0 .. 2^dimK - 1];
{
forprime(p = 5, 60, if (p == 7, next);
  my(rs = [lift(r) | r <- polrootsmod(K21, p)]); if (#rs == 0, next);
  my(chiG = vector(dimK, j, sum(i = 1, #rs, chi(G[j], p, rs[i]) * 2^(i-1))));
  my(im = List());
  foreach(ptsmod(p), P, my(m = 0);
    for (i = 1, #rs, my(q = res(ev(c1, P), p, rs[i])); if (q == 0, q = res(ev(c3, P), p, rs[i])); if (q == 0, error("both vanish"));
      if (!issquare(q), m += 2^(i-1)));
    listput(im, m));
  im = Set(im);
  my(new = List());
  foreach(surv, c, my(m = 0, cc = c, j = 1); while (cc, if (cc % 2, m = bitxor(m, chiG[j])); cc \= 2; j++); if (setsearch(im, m), listput(new, c)));
  my(before = #surv); surv = Vec(new);
  print("p = ", p, " roots ", rs, " : survivors ", #surv);
  if (#setminus(known, Set(surv)) > 0, error("known class removed")));
}
print("survivors: ", surv);
