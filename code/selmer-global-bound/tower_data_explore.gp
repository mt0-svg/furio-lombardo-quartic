\\ tower_data_explore.gp: exploration for the Lean discharge of M3b (not a proof step).
default(parisizemax, 4*10^9); default(nbthreads, 1);
\\ run from code/descent: gp -q ../selmer-global-bound/tower_data_explore.gp
read("descent_search_lib.gp");
read("../earlier-computations/richelot_data.gp");
d = Mod(RIN[1][5], K21); d = d * denominator(content(lift(d)))^2;
dz = zkc(lift(d));
print("d size (digits): ", vecmax(apply(n -> #digits(abs(n) + 1), Vec(dz))));
fa = idealfactor(nf, dz);
print("factorization of (d): ", vector(#fa~, i, [fa[i,1].p, fa[i,1].e, fa[i,1].f, fa[i,2]]));
\\ J with J^2 = (d)
J = idealfactorback(nf, fa[,1], fa[,2] / 2);
jr = bnfisprincipal(bnf, J, 1); print("J principal: ", jr[1]);
j = zv(jr[2]);
eps = zv(nfeltdiv(nf, dz, nfeltpow(nf, j, 2)));
print("eps unit: ", unitq(eps), " integral: ", denominator(content(eps)) == 1);
ex = bnfisunit(bnf, nfbasistoalg(nf, eps)); print("unit exponents (fu..., tu): ", ex);
dig(v) = vecmax(apply(n -> #digits(abs(n) + 1), Vec(v)));
print("digits of G: ", vector(18, i, dig(G[i])));
er = G[1]; foreach([2, 5, 7, 10, 11], i, er = mulz(er, G[i]));
print("eps_red digits ", dig(er), " eps/eps_red square: ", #nfroots(nf, t^2 - nfbasistoalg(nf, nfeltdiv(nf, eps, er))) > 0);
print("signs of eps_red: ", nfeltsign(nf, er), " signs of d: ", nfeltsign(nf, dz));
print("signs of G units: ", vector(12, i, nfeltsign(nf, G[i])));
print("real roots of K21: ", nf.roots[1..3]);
