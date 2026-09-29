\\ descent_search_lib.gp: descent_data_lib.gp plus the class group data used to FIND the certificates of M1 (bnfinit, S, the
\\ 18 generators of K21(S,2) = -1, 11 fundamental units, generators of the six primes of S). Nothing found here is
\\ trusted by Lean: every identity is rechecked by the kernel.
read("descent_data_lib.gp");
bnf = bnfinit(K21, 1);
P2 = idealprimedec(nf, 2); P3 = idealprimedec(nf, 3); P7 = idealprimedec(nf, 7); P439 = idealprimedec(nf, 439);
pr3 = [pr | pr <- P3, pr.f == 1][1];
pr439 = [pr | pr <- P439, pr.f == 1 && idealval(nf, b - 125, pr) > 0][1];
S = concat(P2, [P7[1], pr3, pr439]);
if (vector(6, i, [S[i].p, S[i].e]) != [[2,3],[2,12],[2,6],[7,7],[3,1],[439,1]], error("S order"));
fu = vector(11, i, zv(nfalgtobasis(nf, bnf.fu[i])));
Sg = vector(6, i, zv(bnfisprincipal(bnf, S[i], 1)[2]));
G = concat([zkc(-1)], concat(fu, Sg));
\\ names: la = G[13], lb = G[14], lc = G[15], pi7 = G[16], pi3 = G[17], pi439 = G[18]
inv(u) = zv(nfeltdiv(nf, 1, u));
unitq(u) = abs(nfeltnorm(nf, u)) == 1;
