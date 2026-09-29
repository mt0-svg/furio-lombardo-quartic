\\ known_classes_images_check.gp: referee computation of delta(D1), delta(D2), delta(D3), delta([Qb - 2P0]) and delta(gen3),
\\ with auxiliary divisors different from those of the first two-descent computation:
\\   line through P0: y = -x, l.C = P0 + A;   line section: H1 = (y = 2x + 3).C;   second line section H2 = (y = -3x + 5).C;
\\   conic through R: chosen below (not the one of the first computation), kappa.C = R + R'.
\\ So P0 ~ H - A, R ~ 2H - R', and (modulo squares, and modulo Q^x from the normalising linear forms):
\\   delta(Di) = G(Pi) G(A) G(H1),  delta(Qb - 2P0) = G(Qb),  delta(gen3) = delta(3A - R' - H1) = G(A) G(R') G(H1).
\\ Each element of A3^x is then reduced to O_S^x/squares with a fully verified ideal factorisation (the norm is split
\\ through the identity N(G_A) = c Hess^2 Psi^4, whose rational factors are small enough to factor) and compared with
\\ the Selmer classes of fake_selmer_group_check.dat.
\\ Needs geometry_check.dat, algebra_arithmetic_check.dat, fake_selmer_group_check.dat. Run: gp -q -D parisizemax=4000000000 known_classes_images_check.gp

FAIL = 0;
chk(name, c) = if(c, print("ok   ", name), FAIL++; print("FAIL ", name));
\\ variable priorities fixed before any varlower: x > y > z > X > Y > w > a > u
[x, y, z, 'X, 'Y];
w = varlower("w"); a = varlower("a"); u = varlower("u");
A3pol = a^8+2*a^7+7*a^4-14*a^2-8*a+5;
GEOM = read("geometry_check.dat"); GA = GEOM[1]; r3 = GEOM[3]; yRpol = GEOM[4]; Psi = GEOM[5];
gens = apply(g -> Mod(g, A3pol), read("algebra_arithmetic_check.dat")[1]);
SELD = read("fake_selmer_group_check.dat"); SEL = SELD[1]; Er = SELD[2];
F = x^4+3*x^3*y-3*x^2*y*z-3*x^2*z^2+6*x*y^3-6*x*y^2*z+3*x*y*z^2-2*x*z^3+4*y^4+2*y^3*z-5*y*z^3;
Fx = deriv(F,x); Fy = deriv(F,y); Fz = deriv(F,z);
Hs = matdet([deriv(Fx,x),deriv(Fx,y),deriv(Fx,z); deriv(Fy,x),deriv(Fy,y),deriv(Fy,z); deriv(Fz,x),deriv(Fz,y),deriv(Fz,z)]);
F1 = subst(F, z, 1);

\\ product of a form P over the points of C on the line y = m x + b (z = 1): returns [product, x-polynomial]
online(P, m, b) = my(c = subst(F1, y, m*x + b), g = subst(subst(subst(P, z, 1), y, m*x + b), x, 'X)); [polresultant(subst(c, x, 'X), g, 'X) / pollead(c)^poldegree(g, 'X), c];
\\ product of a form P over the points of C with x a root of r (squarefree) and y = Y(x) mod r (z = 1)
onpts(P, r, Y) = my(g = subst(subst(subst(P, z, 1), y, Y), x, 'X)); polresultant(subst(r, x, 'X), subst(g, x, 'X), 'X) / pollead(r)^poldegree(g, 'X);

\\ reduction of beta in A3^x to O_S^x/squares (exponent vector on gens), given a finite set of rational primes
\\ containing the support of N(beta); every step is verified exactly
reduceS(beta, plist) =
{
  my(nb = norm(beta), rest = nb, bb = beta, odd = List(), I = idealhnf(nf, 1), ok = 1, g, e, res);
  for(i = 1, #plist, rest = rest / plist[i]^valuation(rest, plist[i]));
  if(abs(rest) != 1, error("norm not supported on the given primes: ", rest));
  for(i = 1, #plist, my(p = plist[i], dec, vv);
    if(p == 2 || p == 7, next);
    dec = idealprimedec(nf, p); vv = [nfeltval(nf, bb, pr) | pr <- dec];
    if(vecmin(vv) % 2 != vecmax(vv) % 2, error("valuations of mixed parity above ", p, ": ", vv));
    if(vv[1] % 2, listput(odd, p); bb *= p; vv = vector(#vv, j, vv[j] + 1));
    for(j = 1, #dec, I = idealmul(nf, I, idealpow(nf, dec[j], vv[j] / 2))));
  g = bnfisprincipal(bnf, I, 1)[2];
  if(idealhnf(nf, g) != I, error("generator not verified"));
  bb = bb / Mod(nfbasistoalg(nf, g), A3pol)^2;
  \\ bb is now an S-unit
  if(vecmax(vector(#plist, i, my(p = plist[i]); if(p == 2 || p == 7, 0, vecmax([abs(nfeltval(nf, bb, pr)) | pr <- idealprimedec(nf, p)])))) != 0, error("not an S-unit"));
  \\ candidate exponent vector from quadratic characters, then an exact square test
  res = lift(matsolve(CHM, vector(#AUX, i, (1 - qchar(bb, AUX[i]))/2)~ * Mod(1,2)))~;
  if(#nfroots(nf, x^2 - lift(bb * prod(j = 1, 8, gens[j]^res[j]))) == 0, error("character solution is not a square decomposition"));
  [res, Vec(odd)];
}

\\ products of a form P over the rational points and the auxiliary orbits (uses the globals cA, RpData)
hv(P) =
{
  [subst(subst(subst(P, x, 1), y, 1), z, 1), subst(subst(subst(P, x, 2), y, 0), z, 1), subst(subst(subst(P, x, -1), y, 0), z, 1),
         onpts(P, cA, -x), online(P, 2, 3)[1], online(P, -3, 5)[1], polresultant(x^2 - x + 2, subst(subst(P, z, 0), y, 1)),
         prod(i = 1, #RpData, onpts(P, RpData[i][1], RpData[i][2]))];
}

\\ quadratic character at a degree 1 prime
qchar(g, pr) = my(m = nfmodprinit(nf, pr), v = nfmodpr(nf, g, m)); if(v == 0, error("character at a prime dividing the element"), if(v^((pr.p - 1)/2) == 1, 1, -1));

\\ rational primes dividing numerator or denominator of rational numbers
primesof(v) = my(s = []); for(i = 1, #v, my(q = v[i]); if(q != 0, s = setunion(s, Set(factor(numerator(q))[,1]~)); s = setunion(s, Set(factor(denominator(q))[,1]~)))); setminus(s, Set([-1]));

\\ class of an exponent vector modulo <-1, 2, 7>: canonical representative (lexicographically least of the coset)
canon(e) = my(best = [], v); forvec(f = vector(3, j, [0,1]), v = lift(Mod(e + f[1]*Er[1] + f[2]*Er[2] + f[3]*Er[3], 2)); if(best == [] || lex(v, best) < 0, best = v)); best;

{
nf = nfinit(A3pol); bnf = bnfinit(A3pol, 1);
chk("h = 1 (bnfinit, certified in algebra_arithmetic_check.gp without GRH)", bnf.no == 1);
G = GA;
\\ 8 degree 1 auxiliary primes (above rational primes > 100 not in the candidate list below) with invertible character matrix on gens
AUX = []; CHM = 0;
forprime(q = 101, 5000, if(#AUX == 8, break); dec = idealprimedec(nf, q);
  for(i = 1, #dec, if(#AUX == 8 || dec[i].f != 1, next);
    row = vector(8, j, (1 - qchar(gens[j], dec[i]))/2);
    cand = concat(AUX, [dec[i]]); M8 = matrix(#cand, 8, s, t, if(s <= #AUX, CHM[s,t], row[t]));
    if(matrank(M8 * Mod(1,2)) == #cand, AUX = cand; CHM = M8)));
chk("8 auxiliary degree 1 primes with an invertible character matrix", #AUX == 8 && matrank(CHM * Mod(1,2)) == 8);
CHM = CHM * Mod(1,2);

print("== auxiliary divisors");
LA = online(G, -1, 0); cA = LA[2];
chk("y = -x meets C at P0 once (x | F(x,-x,1), x^2 does not)", polcoef(cA, 0) == 0 && polcoef(cA, 1) != 0);
cA = cA / x;
gA = onpts(G, cA, -x);
chk("G_A does not vanish on A (so A avoids P0, R and the flexes)", gA != 0);
gH1 = online(G, 2, 3)[1];
chk("G_A does not vanish on H1 = (y = 2x + 3).C", gH1 != 0);
gH2 = online(G, -3, 5)[1];
chk("G_A does not vanish on H2 = (y = -3x + 5).C", gH2 != 0);
\\ conic through R: kappa = q0 x^2 + ... , three linear conditions (vanishing at the points of R), choose a member not
\\ through P0 whose residual quintic is squarefree and prime to r3
cm = [x^2, x*y, y^2, x*z, y*z, z^2];
r3u = subst(r3, x, u); yRu = subst(yRpol, u, u);
MR = matrix(3, 6, i, j, polcoef(lift(subst(subst(subst(cm[j], z, 1), y, Mod(yRu, r3u)), x, Mod(u, r3u))), i-1, u));
KR = matker(MR);
chk("conics through R: a 3-dimensional family", #KR == 3);
kap = 0;
forvec(t = [[-2,2],[-2,2],[-2,2]], if(kap != 0, break);
  my(cc = KR * t~, kk, rs, r5); if(cc == 0, next);
  kk = sum(j = 1, 6, cc[j]*cm[j]);
  if(subst(subst(subst(kk, x, 0), y, 0), z, 1) == 0, next);
  if(poldegree(subst(kk, z, 1), y) < 1, next);
  rs = polresultant(F1, subst(kk, z, 1), y);
  if(poldegree(rs) != 8, next);
  if(rs % r3 != 0, next);
  r5 = rs / r3;
  if(poldegree(gcd(r5, r3)) > 0 || !issquarefree(r5) || polcoef(r5, 0) == 0, next);
  kap = kk; r5k = r5);
chk("a conic kappa through R, not through P0, with Res_y(F, kappa) = r3 * r5, r5 squarefree of degree 5 prime to r3 and x", kap != 0);
print("   kappa = ", kap);
chk("kappa is not the conic of the first two-descent computation", kap / content(kap) != (379*x^2 - 606*x*y - 409*x*z + 40*y^2 + 40*y*z - 1250*z^2) / content(379*x^2 - 606*x*y - 409*x*z + 40*y^2 + 40*y*z - 1250*z^2));
\\ R': one point above each root of r5 (squarefree resultant), y from the gcd over Q[x]/(r5)
fr5 = factor(r5k)[,1];
gR = 1; RpData = [];
for(i = 1, #fr5, my(rr = fr5[i], gg, Yr);
  my(ru = subst(rr, x, u));
  gg = gcd(subst(F1, x, Mod(u, ru)), subst(subst(kap, z, 1), x, Mod(u, ru)));
  if(poldegree(gg, y) != 1, error("fibre of R' not a single point"));
  Yr = subst(lift(-polcoef(gg, 0, y) / polcoef(gg, 1, y)), u, x);
  RpData = concat(RpData, [[rr, Yr]]);
  gR *= onpts(G, rr, Yr));
chk("G_A does not vanish on R'", gR != 0);
\\ Qb: points (xb : 1 : 0), xb^2 - xb + 2 = 0
chk("Qb lies on C", subst(subst(subst(F, z, 0), y, 1), x, Mod(x, x^2 - x + 2)) == 0);
gQb = polresultant(x^2 - x + 2, subst(subst(G, z, 0), y, 1)) ;
chk("G_A does not vanish at Qb", gQb != 0);
gP = [subst(subst(subst(G, x, 1), y, 1), z, 1), subst(subst(subst(G, x, 2), y, 0), z, 1), subst(subst(subst(G, x, -1), y, 0), z, 1)];
chk("G_A does not vanish at P1, P2, P3", vecmin(apply(t -> t != 0, gP)) == 1);

print("== elements");
betas = [gP[1]*gA*gH1, gP[2]*gA*gH1, gP[3]*gA*gH1, gQb, gA*gR*gH1, gH1/gH2];
names = ["delta(D1)", "delta(D2)", "delta(D3)", "delta(Qb - 2P0)", "delta(gen3)", "delta(H1 - H2) (principal, control)"];
\\ rational primes that can divide the norms: through N(G_A) = c Hess^2 Psi^4, the norm of G_A over a rational divisor
\\ is c^deg times Hess^2 Psi^4 over that divisor; those rational numbers are computed and factored
plist = setunion(primesof(concat(hv(Hs), hv(Psi))), primesof([content(liftpol(G))]));
plist = setunion(plist, Set([2, 3, 5, 7, 23, 73]));
print("   candidate primes: ", #plist, " (largest ", vecmax(plist), ")");
res = vector(#betas, i, reduceS(Mod(lift(betas[i]), A3pol), plist));
for(i = 1, #betas, print("   ", names[i], ": exponent vector ", res[i][1], ", rational primes removed: ", res[i][2], ", class mod <-1,2,7>: ", canon(res[i][1])));
cls = vector(#betas, i, canon(res[i][1]));
zero = canon(vector(8, j, 0));
chk("control: the principal divisor H1 - H2 maps to 0", cls[6] == zero);
chk("delta(gen3) = 0 (Proposition 3)", cls[5] == zero);
chk("delta(D2) = 0", cls[2] == zero);
chk("delta(D1) = delta(D3)", cls[1] == cls[3]);
chk("delta(D1), delta(Qb - 2P0) and their sum are nonzero", cls[1] != zero && cls[4] != zero && canon(lift(Mod(res[1][1] + res[4][1], 2))) != zero);
selc = Set(apply(canon, SEL));
chk("Sel_fake has 4 classes modulo <-1,2,7>", #selc == 4);
chk("delta(D1), delta(Qb - 2P0), their sum and 0 are exactly the 4 classes of Sel_fake", Set([zero, cls[1], cls[4], canon(lift(Mod(res[1][1] + res[4][1], 2)))]) == selc);

print("== summary: ", FAIL, " failure(s)");
}
