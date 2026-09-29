\\ descent_set_common_zero_probe.gp: feasibility probe (not a proof step). Which primes pr of K21 can divide both
\\ Q1(P) and Q3(P) for P in C(Q) primitive? Q1, Q2, Q3 are integral (trivial contents for Q1, Q3; Q2 has
\\ content a power of a prime above 2). F(P) = 0 gives Q1(P) Q3(P) = Q2(P)^2 exactly, so such a pr divides
\\ Q2(P) too, and P mod pr is a common zero of Q1, Q2, Q3 in P^2 over O/pr.
\\ Lemma (every characteristic): let D = det of the 6 x 6 coefficient matrix of Q1, Q2, Q3, dJ/dx, dJ/dy,
\\ dJ/dz in the quadratic monomials, J = det(dQ_i/dx_j). If Q1, Q2, Q3 have a common zero p over a field, then
\\ D = 0 there. Proof: Euler gives M p = 0 for M = (dQ_i/dx_j)(p). If rank M <= 1 all cofactors vanish; if
\\ rank M = 2 then adj(M) = p w^T with w^T M = 0. Either way dJ/dx_k(p) = sum_ij adj(M)_ji d2Q_i/dx_j dx_k
\\ = sum_i w_i (dQ_i/dx_k)(p) = (w^T M)_k = 0 (Euler for the linear forms dQ_i/dx_k), so the six quadrics vanish
\\ at p and the monomial vector of p, which is nonzero, is a kernel vector.
\\ Hence outside supp(D) we get min(v(Q1(P)), v(Q3(P))) = 0, so v(Q1(P)) = 2 v(Q2(P)) - v(Q3(P)) is even
\\ (or Q1(P) = 0 and v(Q3(P)) = 0): delta(P) is in K21(supp(D), 2). The script checks supp(D) = S.
\\ Run from code/descent: gp -q descent_set_common_zero_probe.gp < /dev/null
default(parisizemax, 4*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
nf = nfinit(K21);
T0 = getwalltime();
mons2 = [[2,0,0], [1,1,0], [1,0,1], [0,2,0], [0,1,1], [0,0,2]];
cf(Q, i, j, k) = polcoef(polcoef(polcoef(Q, i, x), j, y), k, z);
row(Q) = vector(6, j, Mod(cf(Q, mons2[j][1], mons2[j][2], mons2[j][3]), K21));
Qs = [Q1, Q2, Q3];
Jm = matrix(3, 3, i, j, deriv(Qs[i], [x, y, z][j]));
J = matdet(Jm);
M = matrix(6, 6); for (j = 1, 6, M[1,j] = row(Q1)[j]; M[2,j] = row(Q2)[j]; M[3,j] = row(Q3)[j]; M[4,j] = row(deriv(J, x))[j]; M[5,j] = row(deriv(J, y))[j]; M[6,j] = row(deriv(J, z))[j]);
D = lift(matdet(M));
print("D computed (", (getwalltime() - T0) \ 1000, " s); D == 0: ", D == 0);
if (D == 0, error("D = 0: Salmon determinant degenerate"));
\\ sanity: D is nonzero at the known points? (not needed) ; integrality of Q1, Q2, Q3
den = lcm(vector(3, i, denominator(content(lift(Mod(Qs[i], K21))))));
N = norm(Mod(D, K21));
print("norm of D: ", #digits(numerator(N)), " digits (numerator), denominator ", factor(denominator(N)));
fa = factor(numerator(N), 10^7);
print("partial factorization of the numerator of N(D), trial division to 10^7: ", fa);
for (i = 1, #fa~, my(q = fa[i,1]); if (q > 10^7, print("  cofactor ", #digits(q), " digits: ", if (ispseudoprime(q), "pseudoprime", "composite"))));
\\ the prime ideals above the small rational primes that divide D
{
for (i = 1, #fa~, my(q = fa[i,1]); if (q < 10^7,
  my(dec = idealprimedec(nf, q), L = List());
  for (k = 1, #dec, my(v = nfeltval(nf, D, dec[k])); if (v != 0, listput(L, [dec[k].f, dec[k].e, v])));
  print("  q = ", q, ": primes dividing D as [f, e, v]: ", Vec(L))));
}
\\ supp(D) against the S of descent_set_sieve_probe.gp (primes above 2 and 7, and the primes of cB)
Sx = concat(idealprimedec(nf, 2), idealprimedec(nf, 7));
foreach(idealfactor(nf, cB)[,1], pr, if (pr.p != 2 && pr.p != 7, Sx = concat(Sx, [pr])));
fD = idealfactor(nf, D);
for (i = 1, #fD~, my(pr = fD[i,1]); print("prime of D: ", [pr.p, pr.f, pr.e], " v = ", fD[i,2], " in S: ", #select(q -> q == pr, Sx) > 0));
if (#select(i -> #select(q -> q == fD[i,1], Sx) == 0, [1 .. #fD~]), error("supp(D) is not contained in S"), print("ok: supp(D) = S"));
print("done: ", (getwalltime() - T0) / 1000., " s");
