\\ local_image_2_elementary.gp: the 2-adic computations of the referee redone with an elementary square test in L = A3 (x) Q_2,
\\ instead of nfislocalpower / nfhilbert. Test: alpha in L^x is a square iff v_P2(alpha) = 2m is even and the P2-unit
\\ u = alpha pi^(-2m) d^2 (d odd, clearing denominators) is congruent modulo P2^9 = 4 P2 to the square of a unit
\\ (1 + P2^9 lies in L^x2 by Hensel, since v_P2(2) = 4; beta^2 mod P2^9 only depends on beta mod P2^5).
\\ The unit squares modulo P2^9 are listed once from the 1024 classes of O/P2^5; reduction modulo an ideal uses its
\\ upper triangular HNF directly.
\\ Needs algebra_arithmetic_check.dat, local_image_2_check.dat. Run: gp -q -D parisizemax=4000000000 local_image_2_elementary.gp

FAIL = 0;
chk(name, c) = if(c, print("ok   ", name), FAIL++; print("FAIL ", name));
[x, y, z, 'X, 'Y];
w = varlower("w"); a = varlower("a"); u = varlower("u");
A3pol = a^8+2*a^7+7*a^4-14*a^2-8*a+5;
gens = apply(g -> Mod(g, A3pol), read("algebra_arithmetic_check.dat")[1]);
IM2 = apply(g -> Mod(g, A3pol), read("local_image_2_check.dat")[1]);

\\ reduce an integral column vector c modulo the lattice spanned by the columns of an upper triangular HNF H
hnfred(c, H) = my(v = c); forstep(i = #v, 1, -1, v -= (v[i] \ H[i,i]) * H[,i]); v;
\\ elementary square test in L
sq2(al) =
{
  my(v = nfeltval(nf, al, P2), uu, cc, d);
  if(v % 2, return(0));
  uu = nfalgtobasis(nf, al / PI^v);
  d = denominator(content(uu));
  if(d % 2 == 0, error("P2-unit with even denominator"));
  cc = uu * d^2;
  setsearch(SQ9, hnfred(cc, H9)) > 0;
}

\\ al lies in Im_2 Q_2^x L^x2
in2(al) = my(ok = 0); forvec(e = vector(3, j, [0,1]), foreach([1, -1, 2, -2], d, if(!ok && sq2(al * d * prod(j = 1, 3, IM2[j]^e[j])), ok = 1))); ok;

{
nf = nfinit(A3pol);
P2 = idealprimedec(nf, 2)[1];
PI = nfbasistoalg(nf, P2.gen[2]);
chk("PI is a uniformizer at P2", nfeltval(nf, PI, P2) == 1);
H5 = idealhnf(nf, idealpow(nf, P2, 5)); H9 = idealhnf(nf, idealpow(nf, P2, 9));
chk("HNFs upper triangular with index 4^5 and 4^9", matdet(H5) == 4^5 && matdet(H9) == 4^9 && H5 == mathnf(H5) && H9 == mathnf(H9));
chk("P2^9 = 4 P2", H9 == idealhnf(nf, idealmul(nf, 4, P2)));
\\ list the classes of O/P2^5 and the squares of the units among them, modulo P2^9
dg = vector(8, i, H5[i,i]);
sqlist = List(); nunits = 0;
forvec(c = vector(8, i, [0, dg[i] - 1]),
  be = c~;
  if(nfeltval(nf, be, P2) != 0, next);
  nunits++;
  listput(sqlist, hnfred(nfalgtobasis(nf, nfeltmul(nf, be, be)), H9)));
SQ9 = Set(Vec(sqlist));
chk(Str("O/P2^5 has 1024 classes, ", nunits, " of them units (1024 - 256 = 768)"), prod(i = 1, 8, dg[i]) == 1024 && nunits == 768);
\\ the unit squares modulo P2^9 form a subgroup of index 2^9 in (O/P2^9)^x (order 3 * 4^8 * ... : check the count)
print("   number of unit squares modulo P2^9: ", #SQ9, " (expected |(O/P2^9)^x| / 2^9 = 3 * 4^8 / 2^9 = ", 3*4^8/2^9, ")");
chk("the count matches (O/P2^9)^x / squares of order 2^9 = 2^([L:Q_2]+1)", #SQ9 == 3*4^8/2^9);

print("== validation against nfislocalpower on 400 random elements and their squares");
agree = 1; nsq = 0;
for(i = 1, 400,
  t = Mod(random(2^20) - 2^19 + sum(j = 1, 7, (random(2^12) - 2^11) * a^j), A3pol);
  if(t == 0, next);
  if(sq2(t) != nfislocalpower(nf, P2, lift(t), 2), agree = 0);
  if(!sq2(t^2) || !sq2(t^2 * 4^random(5)), agree = 0);
  nsq += sq2(t));
chk(Str("elementary test = nfislocalpower on all 400 (", nsq, " squares among them), and every square passes"), agree);
agree = 1; nsq = 0; ntot = 0;
for(j = 1, 10, for(i = 1, 40,
  t = Mod(random(2^10) + 1 + sum(k = 1, 7, random(2^6) * a^k), A3pol); r = Mod(random(2^6) + sum(k = 1, 7, random(2^6) * a^k), A3pol);
  al = t^2 * (1 + PI^j * r); if(al == 0, next); ntot++;
  s = sq2(al); nsq += s; if(s != nfislocalpower(nf, P2, lift(al), 2), agree = 0)));
chk(Str("elementary test = nfislocalpower on ", ntot, " near-squares t^2 (1 + pi^j r), j = 1..10 (", nsq, " squares among them)"), agree && nsq > 50 && nsq < ntot);

print("== consequences recomputed with the elementary test");
reps = [-1, 2, -2, 5, -5, 10, -10];
chk("Q_2 classes that are squares in L: only 5 (dim J(Q_2)[2] = 1)", [d | d <- reps, sq2(Mod(d, A3pol))] == [5]);
nbad = 0;
forvec(e = vector(3, j, [0,1]), foreach([1, -1, 2, -2], d, if(e == [0,0,0] && d == 1, next);
  if(sq2(d * prod(j = 1, 3, IM2[j]^e[j])), nbad++)));
chk("the three sampled generators of Im_2 are independent modulo L^x2 Q_2^x", nbad == 0);
cntN = 0; cntN2 = 0;
forvec(e = vector(8, j, [0,1]),
  al = prod(j = 1, 8, gens[j]^e[j]);
  if(!issquare(norm(al)), next);
  cntN++;
  if(in2(al), cntN2++));
print("   classes of O_S^x/squares with square norm: ", cntN, ", and in Im_2 Q_2^x L^x2 at 2: ", cntN2);
chk("norm and 2-adic condition leave 32 classes: dim Sel_fake = 5 - 3 = 2", cntN == 64 && cntN2 == 32);

print("== summary: ", FAIL, " failure(s)");
}
