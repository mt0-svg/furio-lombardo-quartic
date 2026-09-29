\\ unit_generator_sizes.gp: sizes of units and S-prime generators of K21 in the power basis (Lean M1 planning).
default(parisizemax, 4*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
bnf = bnfinit(K21, 1); nf = bnf.nf;
P2 = idealprimedec(nf, 2); P3 = idealprimedec(nf, 3); P7 = idealprimedec(nf, 7); P439 = idealprimedec(nf, 439);
pr3 = [pr | pr <- P3, pr.f == 1][1];
pr439 = [pr | pr <- P439, pr.f == 1 && idealval(nf, b - 125, pr) > 0][1];
S = concat(P2, [P7[1], pr3, pr439]);
sz(e) = { my(p = lift(Mod(e, K21)), d = denominator(content(p)), n = p * d); [d, if (n == 0, 0, ceil(log(vecmax(abs(Vec(n)))+1)/log(10)))] };
fu = bnf.fu; print("fundamental units: ", #fu);
for (i = 1, #fu, my(e = nfbasistoalg(nf, fu[i])); print("fu ", i, ": denom ", factor(sz(e)[1]), " numerator digits ", sz(e)[2], "  charpoly digits ", ceil(log(vecmax(abs(Vec(charpoly(Mod(lift(e), K21))))))/log(10))));
for (i = 1, #S, my(g = bnfisprincipal(bnf, S[i], 1)[2], e = nfbasistoalg(nf, g)); print("S gen ", i, " (p=", S[i].p, "): denom ", factor(sz(e)[1]), " num digits ", sz(e)[2], " norm ", factor(norm(e)), " charpoly digits ", ceil(log(vecmax(abs(Vec(charpoly(Mod(lift(e), K21))))))/log(10))));
\\ reduced generators via bnfunits (S-units)
U = bnfunits(bnf, S);
for (j = 1, #U[1], my(e = nffactorback(nf, U[1][j]), s = sz(e)); print("Sunit ", j, ": denom ", factor(s[1]), " digits ", s[2], " norm ", factor(norm(e))));
