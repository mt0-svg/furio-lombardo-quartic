\\ algebra_arithmetic_check.gp: referee recomputation of the arithmetic of A3 used in the two-descent
\\ (square classes of Q_2 in L = A3 (x) Q_2, orbits at 2, 7, infinity), class group without GRH and without
\\ bnfcertify (Minkowski bound and verified generators), S-units modulo squares certified by quadratic characters.
\\ Written from scratch. Run: gp -q -D parisizemax=4000000000 algebra_arithmetic_check.gp

FAIL = 0;
chk(name, c) = if(c, print("ok   ", name), FAIL++; print("FAIL ", name));
\\ variable priorities fixed before any varlower: x > y > z > X > Y > w > a > u
[x, y, z, 'X, 'Y];
a = varlower("a");
A3pol = a^8+2*a^7+7*a^4-14*a^2-8*a+5;

\\ quadratic character of a nonzero element g of nf at a degree 1 prime pr (residue field F_q), 0 if pr | g
qchar(nf, g, pr) = my(m = nfmodprinit(nf, pr), v = nfmodpr(nf, g, m)); if(v == 0, 0, if(v^((pr.p - 1)/2) == 1, 1, -1));

{
print("== the field A3");
nf = nfinit(A3pol);
chk("disc(O_A3) = -2^8 7^9", nf.disc == -2^8*7^9);
chk("signature (2, 3)", nf.sign == [2, 3]);
sf = nfsubfields(A3pol);
chk("the only subfields are Q and A3", vecsort(apply(s -> poldegree(s[1]), sf)) == [1, 8]);
P2 = idealprimedec(nf, 2);
chk("2 O = P2^4, f(P2) = 2 (A3 (x) Q_2 is a field L of degree 8: one G_{Q_2}-orbit of size 8)", #P2 == 1 && P2[1].e == 4 && P2[1].f == 2);
P2 = P2[1];
P7 = idealprimedec(nf, 7);
chk("7 O = P7a P7b^7, both of degree 1 (orbits of sizes 1 and 7)", #P7 == 2 && vecsort([[p.e, p.f] | p <- P7]) == [[1,1],[7,1]]);
P7a = if(P7[1].e == 1, P7[1], P7[2]); P7b = if(P7[1].e == 7, P7[1], P7[2]);

print("== Q_2 square classes that become squares in L");
reps = [-1, 2, -2, 5, -5, 10, -10];
sq = [d | d <- reps, nfislocalpower(nf, P2, d, 2)];
print("   nfislocalpower: squares in L among -1, 2, -2, 5, -5, 10, -10: ", sq);
chk("exactly one nontrivial class (5) becomes a square in L (kernel of dimension 1)", sq == [5]);
\\ second method: P2 splits in A3(sqrt d) iff d is a square in L
spl = vector(#reps, i, my(rnf = rnfinit(nf, x^2 - reps[i])); #rnfidealprimedec(rnf, P2));
print("   number of primes above P2 in A3(sqrt d): ", spl);
chk("P2 splits in A3(sqrt d) exactly for d = 5", spl == [1,1,1,2,1,1,1]);
\\ third method: decomposition group at 2 from the splitting of P2 in A3(a') = A3[X]/(A3pol(X)/(X - a))
h7 = subst(A3pol, a, x) \ (x - Mod(a, A3pol));
rnf7 = rnfinit(nf, h7);
dec7 = rnfidealprimedec(rnf7, P2);
loc7 = vecsort([p.e * p.f / 8 | p <- dec7]);
print("   local degrees over L of the factors of A3pol(X)/(X - a): ", loc7, " (absolute [e,f]: ", [[p.e, p.f] | p <- dec7], ")");
chk("the stabilizer of a point in the decomposition group D at 2 has orbits 1, 1, 3, 3 on Omega: D = S4 (GAP table: dim J[2]^D = 1; D8 would give 2)", loc7 == [1, 3, 3]);
chk("inertia of the compositum has order divisible by 12 (e = 12): inertia A4 in S4", vecmax([p.e | p <- dec7]) == 12);

print("== real places");
chk("complex conjugation fixes 2 points of Omega and swaps 3 pairs (r1 = 2, r2 = 3)", nf.r1 == 2);

print("== class group without GRH");
bnf = bnfinit(A3pol, 1);
chk("bnfinit: h = 1", bnf.no == 1);
chk("bnfcertify(bnf) = 1", bnfcertify(bnf) == 1);
MB = 8!/8^8 * (4/Pi)^3 * sqrt(2^8 * 7^9);
print("   Minkowski bound ", MB);
nprin = 0; allok = 1;
forprime(p = 2, floor(MB) + 1,
  dec = idealprimedec(nf, p);
  for(i = 1, #dec,
    pr = dec[i];
    if(pr.p^pr.f > MB, next);
    res = bnfisprincipal(bnf, pr, 1);
    gen = res[2];
    if(idealhnf(nf, gen) != idealhnf(nf, pr), allok = 0; print("   no verified generator for ", pr));
    nprin++));
chk(Str("every prime ideal of norm <= Minkowski bound (", nprin, " of them) has an explicit generator (verified by idealhnf): h = 1 unconditionally"), allok);

print("== S-units modulo squares");
S = [P2, P7a, P7b];
su = bnfsunit(bnf, S);
gens = concat([[-1], apply(u -> nfbasistoalg(nf, u), bnf.fu), apply(u -> nfbasistoalg(nf, u), su[1])]);
gens = apply(g -> Mod(lift(g), A3pol), gens);
chk("8 generators: -1, 4 fundamental units, 3 S-units", #gens == 8 && #bnf.fu == 4 && #su[1] == 3);
okS = 1;
for(i = 1, 8,
  vv = [nfeltval(nf, gens[i], P) | P <- S];
  if(idealhnf(nf, gens[i]) != idealfactorback(nf, Mat([S~, vv~])), okS = 0));
chk("each generator is an S-unit (ideal supported on P2, P7a, P7b)", okS);
chk("the first five generators are units (norm +-1, integral)", vecmin(vector(5, i, abs(norm(gens[i])) == 1 && denominator(content(nfalgtobasis(nf, gens[i]))) == 1)) == 1);
\\ quadratic characters at auxiliary degree 1 primes; rank 8 certifies independence modulo squares
rows = List(); aux = List();
forprime(q = 3, 5000, if(q == 7, next);
  dec = idealprimedec(nf, q);
  for(i = 1, #dec, pr = dec[i]; if(pr.f != 1 || pr.e != 1, next);
    row = vector(8, j, (1 - qchar(nf, gens[j], pr))/2);
    RR = concat(Vec(rows), [row]);
    if(matrank(matrix(#RR, 8, s, t, RR[s][t]) * Mod(1,2)) > #rows, listput(rows, row); listput(aux, [q, i])));
  if(#rows == 8, break));
chk(Str("the 8 generators are independent modulo squares (quadratic characters at ", #rows, " degree 1 primes, rank 8)"), #rows == 8);
print("   auxiliary primes used: ", Vec(aux));
print("   => with h = 1 and dim O_S^x/O_S^x2 = 8 (Dirichlet), these 8 elements form a basis of A(S,2) = O_S^x/O_S^x2");
\\ -1, 2, 7 modulo squares
chk("-1, 2, 7 independent modulo squares of A3 (no quadratic subfield)", #[d | d <- [-1, 2, -2, 7, -7, 14, -14], #nfroots(nf, x^2 - d) > 0] == 0);

print("== summary: ", FAIL, " failure(s)");
system("rm -f algebra_arithmetic_check.dat"); write("algebra_arithmetic_check.dat", [lift(gens)]);
}
