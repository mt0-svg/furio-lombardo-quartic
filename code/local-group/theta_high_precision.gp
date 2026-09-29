\\ theta_high_precision.gp: a high precision approximation thetaHi of theta* in K_v = Q_2[x]/(E),
\\ E = x^3 + e2 x^2 + e1 x + e0 (M4Cert/Kv.lean), the root of f (M1/Basic.lean fL, constant term first) near
\\ theta0 = (163180991353, 3522151726, 560510631928) (M4Cert/Data.lean). Newton's iteration on integer
\\ polynomials modulo (E, 2^W) with the exact rational inverse of f'(theta) in Q[x]/(E) (unverified), then a
\\ residual check with exact integer arithmetic: the coordinates of f(thetaHi) modulo 2^NB and of f'(thetaHi)
\\ in the basis 1, x, x^2, and their 2-adic valuations. The Lean certificate (KvArith/Sigma.lean) redoes the
\\ check with ball arithmetic. Run: gp -q theta_high_precision.gp > theta_high_precision.out
default(parisizemax, 10^9);
NB = 1200; W = NB + 100;
e0 = 17325639337422721302482; e1 = 16418729904282180494548; e2 = 37469486047374096441064;
E = x^3 + e2*x^2 + e1*x + e0;
fL = [-4, 28, -112, 252, -336, 28, 560, -1072, 1008, -280, -770, 980, -609, 175, 2, 98, -84, 0, 0, 14, -7, 1];
dfL = vector(#fL - 1, i, i * fL[i + 1]);
redc(P, m) = { my(L = lift(Mod(P, E))); sum(i = 0, 2, (polcoef(L, i, x) % m) * x^i); }
hor(cs, T, m) = { my(r = 0); forstep (i = #cs, 1, -1, r = redc(r * T + cs[i], m)); r; }
modq(c, m) = lift(Mod(numerator(c), m) / Mod(denominator(c), m));
th0 = [163180991353, 3522151726, 560510631928];
T = th0[1] + th0[2]*x + th0[3]*x^2;
M = 2^W;
for (it = 1, 12, \
  my(r = hor(fL, T, M), d = hor(dfL, T, M), w, dl); \
  w = lift(Mod(d, E)^(-1)); \
  dl = lift(Mod(r * w, E)); \
  T = sum(i = 0, 2, modq(polcoef(T, i, x) - polcoef(dl, i, x), M) * x^i));
thetaHi = vector(3, i, polcoef(T, i - 1, x) % 2^NB);
print("thetaHi = ", thetaHi);
print("thetaHi = theta0 mod 2^33: ", vector(3, i, (thetaHi[i] - th0[i]) % 2^33 == 0));
Th = thetaHi[1] + thetaHi[2]*x + thetaHi[3]*x^2;
r = lift(Mod(subst(Pol(Vecrev(fL), y), y, Th), E));
d = lift(Mod(subst(Pol(Vecrev(dfL), y), y, Th), E));
vr = vector(3, i, valuation(polcoef(r, i - 1, x) % 2^NB, 2));
vd = vector(3, i, valuation(polcoef(d, i - 1, x), 2));
print("v_2 of the coordinates of f(thetaHi) mod 2^NB: ", vr);
print("v_2 of the coordinates of f'(thetaHi): ", vd);
vpi(vs) = vecmin(vector(3, i, if (vs[i] == oo, oo, 3 * vs[i] + i - 1)));
print("pi-adic valuation: f(thetaHi) mod 2^NB >= ", vpi(vr), ", f'(thetaHi) = ", vpi(vd));
