\\ descent_frozen_data.gp: frozen data for the Lean M1 certificates (sizes printed, data written to descent_frozen_data.bin).
\\ Run: gp -q descent_frozen_data.gp < /dev/null
default(parisizemax, 4*10^9);
default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
bnf = bnfinit(K21, 1); nf = bnf.nf;
dig(n) = if (n == 0, 0, #digits(abs(n)));
vdig(v) = vecmax(apply(dig, Vec(v)));
\\ integral basis zk_j = W_j(b) / D_j
zk = nf.zk; print("zk degrees ", vector(21, j, poldegree(zk[j])));
zkden = vector(21, j, denominator(content(zk[j]))); zknum = vector(21, j, zk[j] * zkden[j]);
print("zk denominators ", apply(factor, zkden)[21]);
zkcp = vector(21, j, charpoly(Mod(zk[j], K21), 'X));
print("zk charpoly integral: ", vector(21, j, denominator(content(zkcp[j])) == 1), "  max digits ", vecmax(vector(21, j, vdig(zkcp[j]))), "  numerator digits ", vecmax(vector(21, j, vdig(zknum[j]))));
\\ coordinates on zk of an element of K21
zkc(e) = nfalgtobasis(nf, lift(Mod(e, K21)));
\\ S and generators
P2 = idealprimedec(nf, 2); P3 = idealprimedec(nf, 3); P7 = idealprimedec(nf, 7); P439 = idealprimedec(nf, 439);
pr3 = [pr | pr <- P3, pr.f == 1][1];
pr439 = [pr | pr <- P439, pr.f == 1 && idealval(nf, b - 125, pr) > 0][1];
S = concat(P2, [P7[1], pr3, pr439]);
print("S [p, f, e]: ", vector(6, i, [S[i].p, S[i].f, S[i].e]));
Sgen = vector(6, i, nfbasistoalg(nf, bnfisprincipal(bnf, S[i], 1)[2]));
fu = vector(11, i, nfbasistoalg(nf, bnf.fu[i]));
G = concat([Mod(-1, K21)], concat(fu, Sgen));
print("generator norms ", vector(18, j, norm(G[j])));
print("generator zk coordinate digits ", vector(18, j, vdig(zkc(G[j]))));
\\ Q coefficients
mons2 = [[2,0,0], [1,1,0], [1,0,1], [0,2,0], [0,1,1], [0,0,2]];
cf(Q, i, j, k) = polcoef(polcoef(polcoef(Q, i, x), j, y), k, z);
row(Q) = vector(6, j, Mod(cf(Q, mons2[j][1], mons2[j][2], mons2[j][3]), K21));
Qs = [Q1, Q2, Q3]; Qc = vector(3, i, row(Qs[i]));
print("Q coefficient zk digits ", vector(3, i, vector(6, j, vdig(zkc(Qc[i][j])))));
Jm = matrix(3, 3, i, j, deriv(Qs[i], [x, y, z][j])); J = matdet(Jm);
M = matrix(6, 6); for (j = 1, 6, for (i = 1, 3, M[i, j] = Qc[i][j]); M[4,j] = row(deriv(J, x))[j]; M[5,j] = row(deriv(J, y))[j]; M[6,j] = row(deriv(J, z))[j]);
D = matdet(M);
cS = 2^13 * 7^13 * Sgen[5]^12 * Sgen[6]^12;
print("valuations of D at S ", vector(6, i, idealval(nf, lift(D), S[i])), "; of cS ", vector(6, i, idealval(nf, lift(cS), S[i])));
Nm = cS * M^(-1);
Nzk = matrix(6, 6, i, j, zkc(Nm[i, j]));
print("N = cS M^-1 integral: ", vecmin(vector(36, k, my(i = (k-1)\6 + 1, j = (k-1)%6 + 1); denominator(content(Nzk[i,j])) == 1)), "  zk digits ", vecmax(vector(36, k, my(i = (k-1)\6 + 1, j = (k-1)%6 + 1); vdig(Nzk[i,j]))));
print("cS zk digits ", vdig(zkc(cS)));
\\ Bezout s f + t f' = Dz
fp = deriv(K21, b); [us, ut, Dz] = [0, 0, 0];
{ my(r = polresultantext(K21, fp)); us = r[1]; ut = r[2]; Dz = r[3]; }
print("Bezout: D = ", factor(Dz), "; s, t digits ", [vdig(us), vdig(ut)], " denominators ", [denominator(content(us)), denominator(content(ut))]);
writebin("descent_frozen_data.bin", [zknum, zkden, zkcp, G, Qc, M, Nzk, cS, us, ut, Dz]);
print("written");
