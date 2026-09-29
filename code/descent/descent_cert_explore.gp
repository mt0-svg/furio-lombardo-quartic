\\ descent_cert_explore.gp: exploration for the M1 certificates (norms from linear elements, unit cofactors, sizes).
default(parisizemax, 4*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
bnf = bnfinit(K21, 1); nf = bnf.nf;
P2 = idealprimedec(nf, 2); P3 = idealprimedec(nf, 3); P7 = idealprimedec(nf, 7); P439 = idealprimedec(nf, 439);
pr3 = [pr | pr <- P3, pr.f == 1][1];
pr439 = [pr | pr <- P439, pr.f == 1 && idealval(nf, b - 125, pr) > 0][1];
S = concat(P2, [P7[1], pr3, pr439]);
print("S [p,f,e]: ", vector(6, i, [S[i].p, S[i].f, S[i].e]));
vS(e) = vector(6, i, idealval(nf, e, S[i]));
for (c = -6, 6, my(N = norm(Mod(b - c, K21))); print("b - ", c, ": norm ", factor(N), " vS ", vS(b - c)));
print("roots of f mod 3: ", polrootsmod(K21, 3), " mod 439: ", polrootsmod(K21, 439));
print("pr3 gen ", pr3.gen, " pr439 gen ", pr439.gen);
print("f mod 7: ", factormod(K21, 7));
print("multab max digits: ", vecmax(apply(n -> if (n == 0, 0, #digits(abs(n))), concat(Vec(nf[9])))));
print("real roots ", polsturm(K21), " roots: ", real(polroots(K21)[1..3]));
