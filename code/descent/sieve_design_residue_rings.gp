\\ sieve_design_residue_rings.gp: sieve design for Lean M1 with residue rings F_p[x]/(phi), phi | f21 mod p irreducible,
\\ symbol chi(w) = w^((q-1)/2), q = p^deg(phi); generators -1, fundamental units, S-prime generators.
\\ Then the 3-adic test at P3 through Z[b] -> Z/27, b -> Hensel lift of 2, on all triples mod 27.
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
\\ residue of e in F_p[x]/(phi)
resphi(e, p, phi) = { my(q = lift(e), d = denominator(content(q))); Mod(Mod(subst(q * d, b, 'xx), p), phi) / Mod(d, p) };
symb(v, p, phi) = { my(qq = p^poldegree(phi)); if (v == 0, error("zero")); my(s = v^((qq - 1)/2)); if (s == 1, 0, if (s == -1, 1, error("not +-1"))) };
cf(Q, i, j, k) = polcoef(polcoef(polcoef(Q, i, x), j, y), k, z);
mons2 = [[2,0,0], [1,1,0], [1,0,1], [0,2,0], [0,1,1], [0,0,2]];
coefs2(Q) = vector(6, j, Mod(cf(Q, mons2[j][1], mons2[j][2], mons2[j][3]), K21));
c1 = coefs2(Q1); c3 = coefs2(Q3);
evq(cr, P) = sum(j = 1, 6, cr[j] * P[1]^mons2[j][1] * P[2]^mons2[j][2] * P[3]^mons2[j][3]);
ptsmod(p) = {
  my(L = List());
  for (x0 = 0, p-1, my(f = substvec(F, [x, z], [x0, 1])); foreach(polrootsmod(f, p), r, listput(L, [x0, lift(r), 1])));
  my(f = substvec(F, [y, z], [1, 0])); foreach(polrootsmod(f, p), r, listput(L, [lift(r), 1, 0]));
  if (substvec(F, [x, y, z], [1, 0, 0]) % p == 0, listput(L, [1, 0, 0]));
  Vec(L);
}
rows = List(); blocks = List();
{
foreach([5, 11, 13, 17, 19, 23], p,
  my(fa = factormod(K21, p), phis = vector(#fa~, i, subst(lift(fa[i,1]), b, 'xx)), k = #phis);
  my(Mp = matrix(k, dimK, i, j, symb(resphi(G[j], p, phis[i]), p, phis[i])));
  my(c1r = vector(k, i, vector(6, j, resphi(c1[j], p, phis[i]))), c3r = vector(k, i, vector(6, j, resphi(c3[j], p, phis[i]))));
  my(im = List());
  foreach(ptsmod(p), P, my(v = vector(k));
    for (i = 1, k, my(q = evq(c1r[i], P)); if (q == 0, q = evq(c3r[i], P)); if (q == 0, error("both vanish")); v[i] = symb(q, p, phis[i]));
    listput(im, v));
  im = Set(im);
  print("p = ", p, ": degrees ", vector(k, i, poldegree(phis[i])), ", |C(F_p)| = ", #ptsmod(p), ", |Im| = ", #im);
  for (i = 1, k, listput(rows, Mp[i,]));
  listput(blocks, [p, k, im]));
}
M = matrix(#rows, dimK, i, j, rows[i][j]) * Mod(1, 2);
print("rank of the sieve character matrix: ", matrank(M), " (", #rows, " rows)");
\\ left inverse from 18 independent rows
sel = List(); Mc = matrix(0, dimK);
{ for (i = 1, #rows, my(M2 = matconcat([Mc; M[i,]])); if (matrank(M2) > matrank(Mc), Mc = M2; listput(sel, i)); if (#sel == dimK, break)); }
Minv = Mc^(-1);
L = matrix(dimK, #rows, i, j, 0) * Mod(1,2); for (k = 1, dimK, for (i = 1, dimK, L[i, sel[k]] = Minv[i, k]));
print("L*M == 1: ", L * M == matid(dimK) * Mod(1,2), "; selected rows ", Vec(sel));
\\ product set of images
combos = List([[]]);
foreach(blocks, B, my(new = List()); foreach(combos, c, foreach(B[3], v, listput(new, concat(c, v)))); combos = new);
print("#combos = ", #combos);
surv = List();
foreach(combos, tt, my(tv = tt~ * Mod(1,2), e = L * tv); if (M * e == tv, listput(surv, lift(e~))));
print("survivors: ", #surv);
\\ delta classes: coordinates via symbols of d0, d1 at the sieve primes
symvec(e0) = { my(v = List()); foreach([5, 11, 13, 17, 19, 23], p, my(fa = factormod(K21, p)); for (i = 1, #fa~, my(phi = subst(lift(fa[i,1]), b, 'xx)); listput(v, symb(resphi(e0, p, phi), p, phi)))); Vec(v)~ * Mod(1,2) };
ed0 = lift(L * symvec(Mod(d0, K21)))~; ed1 = lift(L * symvec(Mod(d1, K21)))~;
print("e(delta0) = ", ed0, " in survivors: ", setsearch(Set(Vec(surv)), ed0) > 0);
print("e(delta1) = ", ed1, " in survivors: ", setsearch(Set(Vec(surv)), ed1) > 0);
celt(e) = prod(j = 1, dimK, G[j]^e[j]);
issq(e) = #nfroots(nf, (X^2 - lift(e))) > 0;
print("delta0 * c(e0) square: ", issq(Mod(d0,K21) * celt(ed0)), "; delta1 * c(e1) square: ", issq(Mod(d1,K21) * celt(ed1)));
\\ check Q1(P0) * delta0 is a square and Q1(P1) * delta1
foreach([[0,0,1],[1,1,1],[2,0,1],[-1,0,1]], P, my(q = evq(c1, P)); if (q == 0, q = evq(c3, P)); print("P = ", P, ": q*d0 square ", issq(q * Mod(d0,K21)), ", q*d1 square ", issq(q*Mod(d1,K21))));
extra = [e | e <- Vec(surv), e != ed0 && e != ed1];
print("extra survivors: ", extra);
\\ 3-adic test: b -> r mod 27
N3 = 27; r3 = [r | r <- [0 .. N3-1], r % 3 == 2 && subst(K21, b, r) % N3 == 0][1];
print("root mod 27: ", r3, " check f(r) mod 27 = ", subst(K21, b, r3) % 27);
res27(e) = { my(q = lift(e), d = denominator(content(q))); Mod(subst(q * d, b, r3), N3) / Mod(d, N3) };
sq27 = Set(vector(N3, i, Mod(i-1, N3)^2));
gr = vector(dimK, j, res27(G[j])); print("generators mod 27: ", lift(gr));
c1_27 = vector(6, j, res27(c1[j])); c3_27 = vector(6, j, res27(c3[j]));
{
foreach(extra, e, my(ce = prod(j = 1, dimK, gr[j]^e[j]), bad = 0);
  for (x0 = 0, N3-1, for (y0 = 0, N3-1, for (z0 = 0, N3-1,
    if (x0 % 3 == 0 && y0 % 3 == 0 && z0 % 3 == 0, next);
    my(P = [x0, y0, z0]); if (substvec(F, [x, y, z], P) % N3 != 0, next);
    my(ok = 0); foreach([c1_27, c3_27], cc, my(w = evq(cc, P) * ce); if (!setsearch(sq27, w), ok = 1));
    if (!ok, bad++))));
  print("extra survivor ", e, ": triples mod 27 not excluded: ", bad));
}
\\ remaining two survivors: add the other primes above 3 (residue rings F_3[x]/(phi)), and P3 mod 81
fa3 = factormod(K21, 3); phis3 = vector(#fa3~, i, subst(lift(fa3[i,1]), b, 'xx)); print("factors mod 3: ", phis3);
{
foreach(extra, e,
  my(ce = prod(j = 1, dimK, gr[j]^e[j]), bad = 0, badA = 0);
  my(cphi = vector(#phis3, i, prod(j = 1, dimK, resphi(G[j], 3, phis3[i])^e[j])));
  for (x0 = 0, N3-1, for (y0 = 0, N3-1, for (z0 = 0, N3-1,
    if (x0 % 3 == 0 && y0 % 3 == 0 && z0 % 3 == 0, next);
    my(P = [x0, y0, z0]); if (substvec(F, [x, y, z], P) % N3 != 0, next);
    my(ok = 0); foreach([c1_27, c3_27], cc, my(w = evq(cc, P) * ce); if (!setsearch(sq27, w), ok = 1));
    if (!ok, bad++;
      for (i = 2, #phis3, my(phi = phis3[i], q = evq(vector(6, j, resphi(c1[j], 3, phi)), P)); if (q == 0, q = evq(vector(6, j, resphi(c3[j], 3, phi)), P));
        if (q != 0 && symb(q * cphi[i], 3, phi) == 1, ok = 1));
      if (!ok, badA++)))));
  print("survivor ", e, ": not excluded at P3 mod 27: ", bad, ", also not by other primes above 3: ", badA));
}
