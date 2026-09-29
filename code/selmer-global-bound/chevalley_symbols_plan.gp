\\ chevalley_symbols_plan.gp: which local symbols carry the index bounds of Chevalley's formula for L/K21 and N/L,
\\ and how small the certificates can be made (Lean planning; not a proof step).
\\ (1) L = K21(sqrt d): the ramified places, the unit symbols at them, a small unit that is not a local norm,
\\     and the least k such that u z^2 = x^2 - d y^2 has no primitive solution modulo P^k (P the prime with e = 3).
\\ (2) N = L(sqrt e): the real places of L where e < 0, the real places of K21 below them, and the rank of the
\\     sign matrix of the units of K21 at those places (if 3, the index bound for N/L needs K21 units only).
\\ (3) the 2-part of the index [O_K21 : Z[b]].
\\ Run from code/selmer-global-bound: gp -q chevalley_symbols_plan.gp < /dev/null
default(parisizemax, 4*10^9); default(nbthreads, 1); default(realprecision, 80);
[t, x, y, z, X, u, w, a, s, b];
read("../earlier-computations/bruin_form.gp");
read("../earlier-computations/richelot_data.gp");
read("../earlier-computations/field_l42_polynomial.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
d = Mod(RIN[1][5], K21);
d = d * denominator(content(lift(d)))^2;
chk(RIN[1][2] == RIN[2][2] && RIN[1][3] == RIN[2][3] && RIN[1][4] == RIN[2][4] && RIN[1][5] == RIN[2][5], "both twists share G1, A, B, d (same L and N)");
nfK = nfinit([K21, [2, 7]]);
print("index [O_K : Z[b]] = ", nfK.index, ", v_2 = ", valuation(nfK.index, 2), ", v_7 = ", valuation(nfK.index, 7));
bnfK = bnfinit(nfK, 1);
EK = concat([bnfK.tu[2]], bnfK.fu);
print("torsion units: ", bnfK.tu[1]);
rd = rnfdisc(nfK, u^2 - lift(d));
ramf = idealfactor(nfK, rd[1]);
ram = vector(#ramf~, j, ramf[j, 1]);
print("ramified primes of K21 in L: ", vector(#ram, j, [ram[j].p, ram[j].e, ram[j].f, ramf[j, 2]]));
print("signs of d at the real places of K21: ", nfeltsign(nfK, lift(d)));
\\ unit symbols
for (i = 1, #EK, print("unit ", i, ": symbols ", vector(#ram, j, nfhilbert(nfK, lift(EK[i]), lift(d), ram[j])), ", signs ", nfeltsign(nfK, lift(EK[i])), ", size ", sizebyte(EK[i])));
\\ small representative of the square class of d (S-unit decomposition over S = primes above 2, 7)
S = concat(idealprimedec(nfK, 2), idealprimedec(nfK, 7));
print("valuations of d at S: ", vector(#S, j, idealval(nfK, lift(d), S[j])), " (e: ", vector(#S, j, S[j].e), ")");
print("norm of d: ", factor(norm(d)));
\\ (2) N/L
e_of_L() = {
  my(Lp = Lpol, emb = nfisincl(K21, Lp), bL = Mod(emb[1], Lp), toL = (pk -> subst(lift(pk), b, bL)), nfL, sd, G2, e, R = RIN[1]);
  nfL = nfinit([Lp, [2, 7]]);
  sd = nfroots(nfL, t^2 - lift(toL(Mod(R[5], K21)))); sd = Mod(sd[1], Lp);
  G2 = toL(R[3]) - sd * toL(R[4]); G2 = G2 / pollead(G2);
  e = poldisc(G2); e = e * denominator(content(lift(e)))^2;
  [nfL, e, bL];
}
EL = e_of_L(); nfL = EL[1]; e = EL[2]; bL = EL[3];
sgE = nfeltsign(nfL, lift(e));
print("signs of e at the 6 real places of L: ", sgE);
\\ the real place of K21 below each real place of L: compare the value of b
rrK = nfK.roots[1..3]; rrL = nfL.roots[1..6];
below = vector(6, i, my(vb = subst(lift(bL), u, rrL[i]), best = 1); for (j = 2, 3, if (abs(vb - rrK[j]) < abs(vb - rrK[best]), best = j)); [best, abs(vb - rrK[best])]);
print("real place of K21 below each real place of L [index, |gap|]: ", below);
ramreal = [i | i <- [1..6], sgE[i] < 0];
print("real places of L ramified in N: ", ramreal, ", below them in K21: ", vector(#ramreal, i, below[ramreal[i]][1]));
Ms = matrix(#EK, 3, i, j, nfeltsign(nfK, lift(EK[i]), j) < 0);
print("sign matrix of E_K21 at the 3 real places (rows = units, 1 = negative): ", Ms, ", rank over F2 ", matrank(Mod(Ms, 2)));
\\ (1b) least k with no primitive solution mod P^k, at the prime with e = 3 (f = 1), for the unit found above
P3 = 0; for (j = 1, #ram, if (ram[j].e == 3, P3 = ram[j]));
chk(P3 != 0 && P3.f == 1, "the ramified prime with e = 3 has f = 1");
print("v_P3(d) = ", idealval(nfK, lift(d), P3));
quit;
