\\ small_units_search.gp: small units and S-units in Z[b] (Lean M1 planning).
default(parisizemax, 4*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
bnf = bnfinit(K21, 1); nf = bnf.nf;
P2 = idealprimedec(nf, 2); print("primes above 2: ", vector(#P2, i, [P2[i].e, P2[i].f]));
P3 = idealprimedec(nf, 3); P7 = idealprimedec(nf, 7); P439 = idealprimedec(nf, 439);
pr3 = [pr | pr <- P3, pr.f == 1 && idealval(nf, b - 2, pr) > 0][1];
pr439 = [pr | pr <- P439, pr.f == 1 && idealval(nf, b - 125, pr) > 0][1];
S = concat(P2, [P7[1], pr3, pr439]);
vS(e) = vector(#S, i, idealval(nf, e, S[i]));
foreach([b, b-1, b+1, 2, 7], e, print(e, ": vals at S ", vS(e)));
\\ units in Z[b] with coefficients in {-1,0,1}, degree <= 6
U = List();
{
forvec(v = vector(7, i, [-1, 1]), my(h = Pol(Vecrev(v), b)); if (poldegree(h) < 1, next);
  my(N = norm(Mod(h, K21))); if (abs(N) == 1, listput(U, h)));
}
print(#U, " units found with small coefficients (deg <= 6)");
\\ rank of their log embedding lattice (numerical)
lg(h) = { my(r = polroots(K21), s = nf.sign); vector(s[1] + s[2] - 1, i, my(k = if (i <= s[1], i, s[1] + 2*(i - s[1]) - 1)); log(abs(subst(h, b, r[k])))) };
M = matrix(11, #U, i, j, lg(U[j])[i]); print("rank of unit logs: ", matrank(M));
\\ independence mod squares via characters at degree one primes outside S
chars = List();
{ forprime(p = 5, 2000, if (p == 7 || p == 439, next); foreach(polrootsmod(K21, p), r, listput(chars, [p, lift(r)]))); }
chi(h, pr) = { my(v = subst(lift(Mod(h, K21)), b, Mod(pr[2], pr[1]))); if (v == 0, -1, if (issquare(v), 0, 1)) };
cand = concat([-1 + 0*b], Vec(U));
CM = matrix(#chars, #cand, i, j, my(c = chi(cand[j], chars[i])); if (c < 0, 0, c)) * Mod(1,2);
print("F2 rank of {-1} + small units: ", matrank(CM));
print("units: ", U[1..min(#U, 40)]);
