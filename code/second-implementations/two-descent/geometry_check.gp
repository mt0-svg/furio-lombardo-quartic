\\ geometry_check.gp: referee recomputation of the geometric input of the two-descent of C.
\\ Written from scratch; does not load two_descent_lib.gp.
\\ Route: flexes over the degree 24 flex field K24 (not over A3), the triangle map p -> fourth point of the
\\ tangent at p, the cubic through a triangle solved over K24, then descended to A3 through nfisisom.
\\ Run: gp -q -D parisizemax=4000000000 geometry_check.gp
\\ Functions are defined at top level; the computation is one brace block, so a GP error aborts it before the
\\ summary line (GP otherwise resumes at the next top-level input).

FAIL = 0;
chk(name, c) = if(c, print("ok   ", name), FAIL++; print("FAIL ", name));
\\ variable priorities fixed before any varlower: x > y > z > X > Y > w > a > u
[x, y, z, 'X, 'Y];
w = varlower("w");
a = varlower("a");
u = varlower("u");
F = x^4+3*x^3*y-3*x^2*y*z-3*x^2*z^2+6*x*y^3-6*x*y^2*z+3*x*y*z^2-2*x*z^3+4*y^4+2*y^3*z-5*y*z^3;
Fx = deriv(F,x); Fy = deriv(F,y); Fz = deriv(F,z);
Hs = matdet([deriv(Fx,x),deriv(Fx,y),deriv(Fx,z); deriv(Fy,x),deriv(Fy,y),deriv(Fy,z); deriv(Fz,x),deriv(Fz,y),deriv(Fz,z)]);
F1 = subst(F,z,1); H1 = subst(Hs,z,1); Fx1 = subst(Fx,z,1); Fy1 = subst(Fy,z,1);
A3pol = a^8+2*a^7+7*a^4-14*a^2-8*a+5;
mons = [x^3, x^2*y, x^2*z, x*y^2, x*y*z, x*z^2, y^3, y^2*z, y*z^2, z^3];
ev(P, pt) = subst(subst(subst(P, x, pt[1]), y, pt[2]), z, pt[3]);
ev2(P, pt) = subst(subst(P, x, pt[1]), y, pt[2]);

\\ fourth point of the tangent at a flex (xf, yf) in the chart z = 1
fourth(xf, yf) =
{
  my(fx = ev2(Fx1, [xf,yf]), fy = ev2(Fy1, [xf,yf]), s = varhigher("s"), L, c);
  L = subst(subst(F1, x, xf + s*fy), y, yf - s*fx);
  c = vector(5, k, polcoef(L, k-1, s));
  if(c[1]!=0 || c[2]!=0 || c[3]!=0, error("not a flex"));
  if(c[5]==0, error("tangent direction on C at infinity"));
  [xf - c[4]/c[5]*fy, yf + c[4]/c[5]*fx];
}

\\ element of K24 lying in Q(th8) -> polynomial in a modulo A3pol (Mth: columns th8^0..th8^7)
toA(c) =
{
  my(v = Colrev(Vecrev(lift(c), 24)), uu = matinverseimage(Mth, v));
  if(#uu == 0, error("element not in Q(th8)"));
  if(Mth*uu != v, error("inexact descent"));
  Mod(Polrev(Vec(uu), a), A3pol);
}

\\ first n Taylor coefficients at P0 of a monomial restricted to C (parameter x)
rowsP0(m, n) = my(e = subst(subst(m,z,1), y, yser)); vector(n, k, polcoef(e, k-1, x));

\\ value and tangential derivative of a monomial at a point of C (chart z = 1)
rowpt(m, pt) =
{
  my(m1 = subst(m,z,1), fx = ev2(Fx1, pt), fy = ev2(Fy1, pt));
  [ev2(m1, pt), ev2(deriv(m1,x)*fy - deriv(m1,y)*fx, pt)];
}

{
print("== curve");
chk("the four known points lie on C", ev(F,[0,0,1])==0 && ev(F,[1,1,1])==0 && ev(F,[2,0,1])==0 && ev(F,[-1,0,1])==0);
chk("[0:1:0] is not on C", ev(F,[0,1,0]) != 0);
chk("P0 = [0:0:1] is a smooth point, tangent 2x + 5y = 0", ev(Fx,[0,0,1])==-2 && ev(Fy,[0,0,1])==-5 && ev(Fz,[0,0,1])==0);
flex = polresultant(F1, H1, y);
chk("Res_y(F,Hess)(x,1) has degree 24 (no flex on z = 0)", poldegree(flex)==24);
chk("Res_y(F,Hess)(x,1) irreducible (24 distinct simple flexes, distinct x)", polisirreducible(flex));
chk("P0 is not a flex", ev(Hs,[0,0,1]) != 0);

print("== flexes and triangles over K24 = Q[w]/(flex)");
fl = subst(flex, x, w); x0 = Mod(w, fl);
g = gcd(subst(F1,x,x0), subst(H1,x,x0));
chk("gcd(F(x0,y), Hess(x0,y)) is linear in y", poldegree(g,y)==1);
y0 = -polcoef(g,0,y)/polcoef(g,1,y);
Ypol = lift(y0);
q = fourth(x0, y0);
chk("tangent at p meets C again at a point q != p", q[1] != x0);
chk("q is a flex (flex(xq) = 0 in K24)", subst(flex, x, q[1]) == 0);
chk("y(q) = Ypol(x(q)) (q is the flex with that x)", q[2] == subst(Ypol, w, q[1]));
gmap = lift(q[1]);
r = [subst(gmap, w, q[1]), subst(Ypol, w, subst(gmap, w, q[1]))];
chk("tangent at q meets C again at r = g(q)", fourth(q[1], q[2]) == r);
chk("tangent at r meets C again at p (triangle closes)", fourth(r[1], r[2]) == [x0, y0]);
chk("p, q, r pairwise distinct", r[1] != x0 && r[1] != q[1]);
chk("p, q, r not collinear", matdet([x0, y0, 1; q[1], q[2], 1; r[1], r[2], 1]) != 0);
T = [[x0,y0],[q[1],q[2]],[r[1],r[2]]];

print("== the triangle algebra");
s1 = x0 + q[1] + r[1];
mp = minpoly(s1);
chk("x(p)+x(q)+x(r) has degree 8", poldegree(mp)==8);
A3x = subst(A3pol, a, x);
iso = nfisisom(A3x, mp);
chk("its field is isomorphic to A3 = Q[a]/(a^8+2a^7+7a^4-14a^2-8a+5)", iso != 0);
chk("A3 has no nontrivial automorphism (unique embedding)", #iso == 1);
\\ nfisisom(A, B) lists the roots of A written as polynomials in a root of B: here a in terms of s1
th8 = subst(lift(iso[1]), x, s1);
chk("th8 is a root of A3pol in K24", subst(A3pol, a, th8) == 0);
Mth = matconcat(vector(8, k, Colrev(Vecrev(lift(th8^(k-1)), 24))));
chk("1, th8, ..., th8^7 independent over Q", matrank(Mth) == 8);

print("== the cubic G through the triangle");
yser = O(x^7); for(k=1, 8, yser = yser - subst(F1, y, yser)/(-5));
chk("y(x) solves F(x,y(x),1) = O(x^7)", valuation(subst(F1,y,yser), x) >= 7);
M = matrix(9, 10);
for(j=1, 10, v = rowsP0(mons[j], 3); for(k=1,3, M[k,j] = v[k] + 0*x0));
for(i=1, 3, for(j=1, 10, v = rowpt(mons[j], T[i]); M[3+2*i-1, j] = v[1]; M[3+2*i, j] = v[2]));
K = matker(M);
chk("the 9 conditions have a 1-dimensional solution space over K24", #K == 1);
cG = K[,1];
chk("the coefficient of y z^2 is nonzero", cG[9] != 0);
cG = cG / cG[9];
chk("no z^3 term (P0 on G)", cG[10] == 0);
chk("linear part at P0 proportional to 2x + 5y", cG[6] == 2/5);
GA = sum(j=1, 10, toA(cG[j]) * mons[j]);
print("GA = ", GA);
e1 = x0 + q[1] + r[1]; e2 = x0*q[1] + x0*r[1] + q[1]*r[1]; e3 = x0*q[1]*r[1];
cT = x^3 - toA(e1)*x^2 + toA(e2)*x - toA(e3);
chk("cT divides the flex polynomial over A3", type(cT) == "t_POL" && poldegree(cT) == 3 && (flex % cT) == 0);

print("== the divisor of G_A");
GA1 = subst(GA, z, 1);
RS = polresultant(F1, GA1, y);
chk("Res_y(F, G_A)(x,1) has degree 12 (no point of C.G on z = 0)", poldegree(RS)==12);
chk("exponent of x is exactly 3", valuation(RS, x) == 3);
RS2 = RS / x^3;
chk("cT^2 divides", RS2 % (cT^2) == 0);
RS3 = RS2 \ cT^2;
chk("cT^3 does not divide", RS3 % cT != 0);
chk("residual has degree 3", poldegree(RS3) == 3);
r3 = simplify(liftall(RS3 / pollead(RS3)));
chk("residual cubic has rational coefficients", variables(r3) == [x]);
r3 = r3 * denominator(content(r3)); r3 = r3/content(r3);
print("r3 = ", r3);
chk("r3 = 1633x^3 - 4901x^2 + 3500x + 6250 up to sign", r3 == 1633*x^3-4901*x^2+3500*x+6250 || r3 == -(1633*x^3-4901*x^2+3500*x+6250));
chk("r3 irreducible over Q", polisirreducible(r3));
chk("r3 prime to x and to the flex polynomial", polcoef(r3,0) != 0 && poldegree(gcd(r3, flex)) == 0);
r3u = subst(r3, x, u);
gk = vector(8, k, subst(polcoef(liftpol(GA1), k-1, a), x, Mod(u, r3u)));
gg = subst(F1, x, Mod(u, r3u)); for(k=1, 8, gg = gcd(gg, gk[k]));
chk("gcd(F(u,y), g_0(u,y), ..., g_7(u,y)) is linear over Q(u): R is Q-rational, common to all conjugates", poldegree(gg,y)==1);
yR = -polcoef(gg,0,y)/polcoef(gg,1,y);
print("R: x = u, y = ", lift(yR), ", r3(u) = 0");
chk("the three points of R are not collinear (yR has degree 2 in u)", poldegree(lift(yR), u) == 2);

print("== the cubic Psi with div = 6 P0 + 2 R");
MP = matrix(12, 10);
for(j=1, 10, v = rowsP0(mons[j], 6); for(k=1,6, MP[k,j] = v[k]); wv = rowpt(mons[j], [Mod(u,r3u), yR]); wv = concat(Vecrev(lift(wv[1]),3), Vecrev(lift(wv[2]),3)); for(k=1,6, MP[6+k,j] = wv[k]));
KP = matker(MP);
chk("the 12 conditions (order >= 6 at P0, contact >= 2 at R) have a 1-dimensional solution over Q", #KP == 1);
cP = KP[,1]; cP = cP / content(cP);
Psi = sum(j=1, 10, cP[j]*mons[j]);
print("Psi = ", Psi);
RP = polresultant(F1, subst(Psi,z,1), y);
chk("Res_y(F, Psi)(x,1) has degree 12", poldegree(RP) == 12);
chk("Res_y(F, Psi) = const x^6 r3^2 (div Psi = 6P0 + 2R = 2E)", RP == pollead(RP)/pollead(r3)^2 * x^6 * r3^2);

print("== norm identity N_{A3/Q}(G_A) = c Hess^2 Psi^4 mod F (sampled on C(F_p), p split in A3; evidence only)");
nchk = 0; nprimes = 0; ok = 1;
forprime(p = 11, 200000,
  if(nprimes >= 6, break);
  rts = polrootsmod(A3pol, p);
  if(#rts < 8, next);
  nprimes++; vals = [];
  for(X = 0, p-1,
    if(#vals >= 12, break);
    fy = polrootsmod(subst(F1, x, X), p);
    for(i = 1, #fy,
      pt = [Mod(X,p), fy[i], Mod(1,p)];
      hv = ev(Hs, pt); pv = ev(Psi, pt);
      if(hv == 0 || pv == 0, next);
      nv = prod(k = 1, 8, ev(subst(liftpol(GA), a, rts[k]), pt));
      vals = concat(vals, [nv/(hv^2*pv^4)]); nchk++));
  if(#vals < 5, ok = 0); for(i = 2, #vals, if(vals[i] != vals[1], ok = 0)));
chk(Str("N(G_A)/(Hess^2 Psi^4) constant on C(F_p) at ", nchk, " points, ", nprimes, " totally split primes"), ok && nprimes >= 6);

print("== summary: ", FAIL, " failure(s)");
system("rm -f geometry_check.dat"); write("geometry_check.dat", [GA, cT, r3, lift(yR), Psi]);
}
