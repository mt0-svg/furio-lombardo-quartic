\\ local_image_2_divisors.gp: more samples for Im_2: Galois stable divisors of degree 2 and 3 over Q_2 (irreducible factors
\\ of the fibres of x/z and z/x over Q_2) in both charts, x0 and z0 over a wider range, and fibres over x0 = m/2^j.
\\ The factorisation is certified by the resultant form of Hensel's lemma; the class of D - deg(D) P1 is tested for
\\ membership in the span of the three generators of local_image_2_check.gp with the elementary square test of
\\ local_image_2_elementary.gp (re-implemented here). A class outside the span would contradict dim Im_2 = 3.
\\ Needs geometry_check.dat, local_image_2_check.dat. Run: gp -q -D parisizemax=4000000000 local_image_2_divisors.gp
FAIL = 0;
chk(name, c) = if(c, print("ok   ", name), FAIL++; print("FAIL ", name));
[x, y, z, 'X, 'Y];
w = varlower("w"); a = varlower("a"); u = varlower("u");
A3pol = a^8+2*a^7+7*a^4-14*a^2-8*a+5;
GEOM = read("geometry_check.dat");
GAint = liftpol(GEOM[1]); GAint = GAint * denominator(content(GAint));
IM2 = apply(g -> Mod(g, A3pol), read("local_image_2_check.dat")[1]);
F = x^4+3*x^3*y-3*x^2*y*z-3*x^2*z^2+6*x*y^3-6*x*y^2*z+3*x*y*z^2-2*x*z^3+4*y^4+2*y^3*z-5*y*z^3;
v2(q) = if(q == 0, 10^6, valuation(q, 2));
hnfred(c, H) = my(v = c); forstep(i = #v, 1, -1, v -= (v[i] \ H[i,i]) * H[,i]); v;
sq2(al) =
{
  my(v = nfeltval(nf, al, P2), uu, d);
  if(v % 2, return(0));
  uu = nfalgtobasis(nf, al / PI^v); d = denominator(content(uu));
  if(d % 2 == 0, error("P2-unit with even denominator"));
  setsearch(SQ9, hnfred(uu * d^2, H9)) > 0;
}
in2(al) = my(ok = 0); forvec(e = vector(3, j, [0,1]), foreach([1, -1, 2, -2], d, if(!ok && sq2(al * d * prod(j = 1, 3, IM2[j]^e[j])), ok = 1))); ok;
\\ Q(Y): monic integral quartic whose roots Y give the points pt(Y) (homogeneous, integral); returns the list of
\\ [product of G_A over the roots of a certified factor, degree] for the factors of degree 2 and 3
facs(Q, ptY) =
{
  my(fa = factorpadic(Q, 2, 100), out = List(), qt, ht, E, m, rv, k, g, nv, vv);
  for(i = 1, #fa~,
    if(poldegree(fa[i,1]) < 2 || poldegree(fa[i,1]) > 3 || fa[i,2] != 1, next);
    qt = Pol(apply(c -> lift(Mod(truncate(c), 2^100)), Vec(fa[i,1] / pollead(fa[i,1]))), 'Y);
    ht = Q \ qt; E = Q - qt * ht;
    m = if(E == 0, 10^6, vecmin(apply(c -> v2(c), Vec(E))));
    rv = v2(polresultant(qt, ht, 'Y));
    if(m <= 2*rv, nskip++; next);
    k = m - rv;
    g = subst(subst(subst(GAint, x, ptY[1]), y, ptY[2]), z, ptY[3]);
    nv = Mod(polresultant(qt, g, 'Y), A3pol);
    if(nv == 0, nskip++; next);
    vv = nfeltval(nf, nv, P2);
    if(4*k < vv + 9, nskip++; next);
    listput(out, [nv, poldegree(qt)]));
  Vec(out);
}
{
nf = nfinit(A3pol); P2 = idealprimedec(nf, 2)[1]; PI = nfbasistoalg(nf, P2.gen[2]);
H5 = idealhnf(nf, idealpow(nf, P2, 5)); H9 = idealhnf(nf, idealpow(nf, P2, 9));
sql = List(); forvec(c = vector(8, i, [0, H5[i,i] - 1]), if(nfeltval(nf, c~, P2) != 0, next); listput(sql, hnfred(nfalgtobasis(nf, nfeltmul(nf, c~, c~)), H9)));
SQ9 = Set(Vec(sql));
chk("384 unit squares modulo P2^9", #SQ9 == 384);
g1 = Mod(subst(subst(subst(GAint, x, 1), y, 1), z, 1), A3pol);
nskip = 0; cnt = [0, 0]; out = 0;
\\ chart A, x0 integer: points (2 x0 : Y : 2); chart B, z0 even: points (2 : Y : 2 z0); chart C, x0 = m/2^j:
\\ (x : y : z) = (m : 2^j y : 2^j), y = Y/2^(j+1) ... handled through the monic polynomial 2^(4j+2) F(m, Y/2, 2^j) / c
for(x0 = -600, 600,
  Q = subst(subst(4*subst(F, z, 1), y, 'Y/2), x, x0);
  L = facs(Q, [2*x0, 'Y, 2]);
  for(i = 1, #L, cnt[L[i][2] - 1]++; if(!in2(L[i][1] / g1^L[i][2]), out++)));
forstep(z0 = -1200, 1200, 2,
  Q = subst(subst(4*subst(F, x, 1), y, 'Y/2), z, z0);
  L = facs(Q, [2, 'Y, 2*z0]);
  for(i = 1, #L, cnt[L[i][2] - 1]++; if(!in2(L[i][1] / g1^L[i][2]), out++)));
\\ x/z = m/2^j with j = 1..4, m odd: the point (m : y 2^j : 2^j); F(m, Y, 2^j) has leading coefficient 4 in Y and
\\ we use Y = Y'/2: 4 F(m, Y'/2, 2^j) is monic integral in Y'; point (2m : Y' : 2^(j+1))
for(j = 1, 4, forstep(m = -63, 63, 2,
  Q = 4*subst(subst(subst(F, x, m), z, 2^j), y, 'Y/2);
  if(pollead(Q) != 1 || denominator(content(Q)) != 1, error("chart C not monic integral"));
  L = facs(Q, [2*m, 'Y, 2^(j+1)]);
  for(i = 1, #L, cnt[L[i][2] - 1]++; if(!in2(L[i][1] / g1^L[i][2]), out++))));
print("   certified Q_2-rational divisors: degree 2: ", cnt[1], ", degree 3: ", cnt[2], ", skipped: ", nskip);
chk(Str("all ", cnt[1] + cnt[2], " divisors D - deg(D) P1 have delta in the span of the three generators (dim Im_2 stays 3)"), out == 0 && cnt[1] > 100);
print("== summary: ", FAIL, " failure(s)");
}
