\\ local_image_2_check.gp: referee computation of the local image Im_2 = delta(J(Q_2)) in L^x/L^x2 Q_2^x.
\\ Own square class map: alpha -> (Hilbert symbols (alpha, beta_j)_P2)_{j=1..10} for a basis beta of L^x/L^x2
\\ (certified by a Gram matrix of rank 10), cross-checked with nfislocalpower. Own point search: every Q_2-point in
\\ the monic charts 4F(x0, y'/2, 1) (x0 in Z_2) and 4F(1, y'/2, z0) (z0 in 2Z_2), roots certified by Hensel's
\\ lemma from integer approximations (not by polrootspadic's precision), precision criterion 4k >= v + 9
\\ (1 + P2^9 = 1 + 4 P2 lies in L^x2 since e = 4). Also degree 2 divisors (Galois stable pairs over Q_2) with the
\\ factorisation certified by the resultant form of Hensel's lemma.
\\ Needs geometry_check.dat. Run: gp -q -D parisizemax=4000000000 local_image_2_check.gp

FAIL = 0;
chk(name, c) = if(c, print("ok   ", name), FAIL++; print("FAIL ", name));
\\ variable priorities fixed before any varlower: x > y > z > X > Y > w > a > u
[x, y, z, 'X, 'Y];
w = varlower("w"); a = varlower("a"); u = varlower("u");
A3pol = a^8+2*a^7+7*a^4-14*a^2-8*a+5;
GEOM = read("geometry_check.dat");
GA = GEOM[1];
\\ make G_A primitive with coefficients in Z[a] (Z[a] lies in O_A3, so P2-integral)
GAc = liftpol(GA); dd = denominator(content(GAc)); GAint = GAc * dd;
evGA(pt) = Mod(subst(subst(subst(GAint, x, pt[1]), y, pt[2]), z, pt[3]), A3pol);
F = x^4+3*x^3*y-3*x^2*y*z-3*x^2*z^2+6*x*y^3-6*x*y^2*z+3*x*y*z^2-2*x*z^3+4*y^4+2*y^3*z-5*y*z^3;
v2(q) = if(q == 0, 10^6, valuation(q, 2));

\\ Hensel certificate for a root approximation t (integer) of an integral polynomial Q: returns certified k with
\\ a true root within 2^k of t, or -1
\\ square class map (uses the globals nf, P2, basis set in the main block)
cl(al) = vector(10, j, (1 - nfhilbert(nf, lift(al), lift(basis[j]), P2))/2) * Mod(1,2);

hensel_root(Q, t) =
{
  my(fv = v2(subst(Q, 'Y, t)), dv = v2(subst(deriv(Q, 'Y), 'Y, t)));
  if(fv > 2*dv, fv - dv, -1);
}

\\ all certified Q_2-roots of a monic integral quartic Q('Y) to working precision N
roots2(Q, N) =
{
  my(r = polrootspadic(Q, 2, N), out = List(), t, k);
  for(i = 1, #r, t = truncate(r[i]); if(type(t) != "t_INT", t = lift(Mod(t, 2^N)));
    k = hensel_root(Q, t); if(k > 0, listput(out, [t, k])));
  Vec(out);
}

{
nf = nfinit(A3pol); P2 = idealprimedec(nf, 2)[1];
chk("G_A normalised to coefficients in Z[a]", denominator(content(GAint)) == 1);

print("== basis of L^x/L^x2 and the Hilbert symbol square class map");
\\ pool: -1, 2, 5, a uniformizer pi, and 1 + pi^i zt^s (i = 1..9, s = 0..2), zt a lift of a generator of F_4^x
pi2 = nfbasistoalg(nf, P2.gen[2]);
chk("pi2 is a uniformizer of P2", nfeltval(nf, pi2, P2) == 1);
mpr = nfmodprinit(nf, P2); zt = 0;
for(j = 0, 7, my(t = Mod(a^j, A3pol), tb = nfmodpr(nf, t, mpr)); if(tb != 0 && tb^2 != tb, zt = t; break));
chk("zt reduces outside F_2", zt != 0);
pool = List();
foreach([-1, 2, 5], d, listput(pool, Mod(d, A3pol))); listput(pool, Mod(lift(pi2), A3pol));
for(i = 1, 9, for(s = 0, 2, listput(pool, Mod(lift(1 + pi2^i * zt^s), A3pol))));
pool = Vec(pool);
basis = [];
for(i = 1, #pool,
  if(#basis == 10, break);
  cand = concat(basis, [pool[i]]);
  Gm = matrix(#cand, #cand, s, t, (1 - nfhilbert(nf, lift(cand[s]), lift(cand[t]), P2))/2);
  \\ keep the candidate if the candidates stay independent: test through the full Hilbert rows against the pool
  rowsC = matrix(#cand, #pool, s, t, (1 - nfhilbert(nf, lift(cand[s]), lift(pool[t]), P2))/2);
  if(matrank(rowsC * Mod(1,2)) == #cand, basis = cand));
chk("10 elements independent in L^x/L^x2 (Hilbert rows of rank 10)", #basis == 10);
Gram = matrix(10, 10, s, t, (1 - nfhilbert(nf, lift(basis[s]), lift(basis[t]), P2))/2) * Mod(1,2);
chk("their Hilbert Gram matrix has rank 10: cl(alpha) = ((alpha, beta_j))_j is an isomorphism L^x/L^x2 -> F_2^10", matrank(Gram) == 10);
Q2img = [cl(Mod(-1, A3pol)), cl(Mod(2, A3pol)), cl(Mod(5, A3pol))];
chk("cl(5) = 0 and cl(-1), cl(2) independent: image of Q_2^x has dimension 2", Q2img[3] == 0*Q2img[3] && matrank(Mat([Q2img[1]~, Q2img[2]~])) == 2);
\\ spot check of cl against nfislocalpower on the pool
okc = 1; for(i = 1, #pool, if((cl(pool[i]) == 0*cl(pool[i])) != nfislocalpower(nf, P2, lift(pool[i]), 2), okc = 0));
chk("cl(alpha) = 0 iff nfislocalpower(alpha) on the pool elements", okc);

print("== Q_2-points");
g1 = evGA([1,1,1]);
chk("G_A(P1) != 0", g1 != 0);
cl1 = cl(g1);
classes = List(); info = List(); els = List(); nskip = 0; npts = 0; vmax = 0; nzero = 0;
N = 120;
\\ chart A: (x0 : y : 1) with x0 in Z, y = y'/2, point (2 x0 : y' : 2)
for(x0 = -300, 300,
  Q = subst(subst(4*subst(F, z, 1), y, 'Y/2), x, x0);
  rr = roots2(Q, N);
  for(i = 1, #rr, pt = [2*x0, rr[i][1], 2]; k = rr[i][2];
    gv = evGA(pt); if(gv == 0, nzero++; next); v = nfeltval(nf, gv, P2);
    if(4*k < v + 9, nskip++; next);
    npts++; vmax = max(vmax, v);
    listput(classes, cl(gv) - cl1); listput(els, gv / g1); listput(info, ["A", x0, rr[i][1] % 2^8, v])));
\\ chart B: (1 : y : z0) with z0 in 2Z, y = y'/2, point (2 : y' : 2 z0)
forstep(z0 = -600, 600, 2,
  Q = subst(subst(4*subst(F, x, 1), y, 'Y/2), z, z0);
  rr = roots2(Q, N);
  for(i = 1, #rr, pt = [2, rr[i][1], 2*z0]; k = rr[i][2];
    gv = evGA(pt); if(gv == 0, nzero++; next); v = nfeltval(nf, gv, P2);
    if(4*k < v + 9, nskip++; next);
    npts++; vmax = max(vmax, v);
    listput(classes, cl(gv) - cl1); listput(els, gv / g1); listput(info, ["B", z0, rr[i][1] % 2^8, v])));
print("   certified Q_2-points used: ", npts, ", skipped for precision: ", nskip, ", exact zeros of G_A skipped (P0): ", nzero, ", largest valuation of G_A: ", vmax);
M = matconcat(concat(apply(c -> c~, Vec(classes)), [Q2img[1]~, Q2img[2]~]));
rk = matrank(M) - 2;
print("   dimension of the span of the sampled classes modulo the image of Q_2^x: ", rk);
chk("sampled Q_2-points span exactly dimension 3 (never 4)", rk == 3);
\\ a basis of the span, as global elements
bas = []; basv = [Q2img[1]~, Q2img[2]~]; basinfo = [];
for(i = 1, #classes, if(matrank(matconcat(concat(basv, [classes[i]~]))) > #basv, basv = concat(basv, [classes[i]~]); bas = concat(bas, [i]); basinfo = concat(basinfo, [info[i]])));
print("   generators found at: ", basinfo);
IM2 = vector(#bas, j, els[bas[j]]);
\\ independence by nfislocalpower only: no nontrivial product g1^e1 g2^e2 g3^e3 d (d in {1,-1,2,-2}) is a square in L
nsq = 0;
forvec(e = vector(3, j, [0,1]), foreach([1,-1,2,-2], d, if(e == [0,0,0] && d == 1, next);
  al = d * prod(j = 1, 3, IM2[j]^e[j]); if(nfislocalpower(nf, P2, lift(al), 2), nsq++)));
chk("nfislocalpower: the three generators are independent modulo L^x2 Q_2^x (31 nontrivial products, none a square)", nsq == 0);
\\ every sampled class lies in the span of the three generators (checked through nfislocalpower on 60 samples)
nfail = 0; nt = 0;
for(i = 1, #classes, if(i % max(1, #classes \ 60) != 0, next); nt++;
  al = els[i];
  found = 0;
  forvec(e = vector(3, j, [0,1]), foreach([1,-1,2,-2], d, if(!found && nfislocalpower(nf, P2, lift(al * d * prod(j = 1, 3, IM2[j]^e[j])), 2), found = 1)));
  if(!found, nfail++));
chk(Str("nfislocalpower: ", nt, " sampled classes all lie in the span of the three generators"), nfail == 0);

print("== degree 2 divisors (Galois stable pairs of Q_2-conjugate points in chart A)");
nq = 0; nqout = 0; nqskip = 0;
for(x0 = -200, 200,
  Q = subst(subst(4*subst(F, z, 1), y, 'Y/2), x, x0);
  fa = factorpadic(Q, 2, 80);
  for(i = 1, #fa~,
    if(poldegree(fa[i,1]) != 2 || fa[i,2] != 1, next);
    qt = Pol(apply(c -> lift(Mod(truncate(c), 2^80)), Vec(fa[i,1] / pollead(fa[i,1]))), 'Y);
    ht = Q \ qt;
    E = Q - qt * ht;
    m = if(E == 0, 10^6, vecmin(apply(c -> v2(c), Vec(E))));
    rv = v2(polresultant(qt, ht, 'Y));
    if(m <= 2*rv, nqskip++; next);
    k = m - rv;
    \\ product of G_A over the two roots of qt: resultant (qt monic)
    gpoly = subst(subst(subst(GAint, x, 2*x0), z, 2), y, 'Y);
    nv = Mod(polresultant(qt, gpoly, 'Y), A3pol);
    v = nfeltval(nf, nv, P2);
    if(4*k < v + 9, nqskip++; next);
    nq++;
    al = nv / g1^2;
    found = 0;
    forvec(e = vector(3, j, [0,1]), foreach([1,-1,2,-2], d, if(!found && nfislocalpower(nf, P2, lift(al * d * prod(j = 1, 3, IM2[j]^e[j])), 2), found = 1)));
    if(!found, nqout++)));
print("   certified degree 2 divisors: ", nq, ", skipped: ", nqskip);
chk(Str("all ", nq, " degree 2 divisors land in the span of the three generators (nfislocalpower)"), nq > 20 && nqout == 0);

print("== summary: ", FAIL, " failure(s)");
system("rm -f local_image_2_check.dat"); write("local_image_2_check.dat", [lift(IM2)]);
}
