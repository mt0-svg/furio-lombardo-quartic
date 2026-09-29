\\ 2-descent on J = Jac(C), C = X_{E3}(7): common definitions.
\\ Read from the caller:  gp -q -D parisizemax=2000000000 two_descent_lib.gp twodesc_<k>_*.gp
\\ Variable order (priorities): x > y > z > X > u > w > a.  a is the variable of A3.
[x, y, z, X, u, w, a];

F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
Hess = matdet(matrix(3, 3, i, j, deriv(deriv(F, [x,y,z][i]), [x,y,z][j])));
mons3 = [x^3, x^2*y, x^2*z, x*y^2, x*y*z, x*z^2, y^3, y^2*z, y*z^2, z^3];
A3 = a^8 + 2*a^7 + 7*a^4 - 14*a^2 - 8*a + 5;

\\ ---------- flexes and the triangle over A3 ----------
f1 = subst(F, z, 1); h1 = subst(Hess, z, 1);
rflex = polresultant(f1, h1, y);                 \\ x-coordinates of the 24 flexes (chart z = 1)
rw = subst(rflex, x, w);
{
  my(g = gcd(subst(f1, x, Mod(w, rw)), subst(h1, x, Mod(w, rw))));
  if (poldegree(g, y) != 1, error("flex y-coordinate not unique"));
  Yw = lift(-polcoef(g, 0, y) / polcoef(g, 1, y));   \\ flex = (w, Yw(w), 1), w a root of rflex
}
bnf = bnfinit(A3, 1);
{
  my(fa = nffactor(bnf, subst(rflex, x, X)));
  cT = 0;
  for (i = 1, #fa~, if (poldegree(fa[i,1], X) == 3, cT = fa[i,1] / pollead(fa[i,1])));
  if (cT == 0, error("no cubic factor"));
}
YT = subst(Yw, w, X) % cT;                         \\ the flex T1 = (X, YT(X), 1) over A3[X]/(cT)

\\ local expansion of C at P0 = (0:0:1) in the parameter y: x = xP0(y)
xP0ser(N) = { my(xs = O(y^N)); for (k = 1, N + 1, xs = xs + subst(f1, x, xs) / 2); xs; }

\\ ---------- the cubic G_A ----------
\\ order >= 3 at P0, contact >= 2 at the three flexes of the triangle
{
  my(rows = List(), xs = xP0ser(6), fx, fy, fxT, fyT, V0, V1, M, ker, gv, den);
  for (k = 0, 2, listput(rows, vector(10, i, polcoef(subst(subst(mons3[i], z, 1), x, xs), k, y))));
  fx = deriv(f1, x); fy = deriv(f1, y);
  fxT = subst(subst(fx, x, X), y, YT) % cT; fyT = subst(subst(fy, x, X), y, YT) % cT;
  V0 = vector(10, i, subst(subst(subst(mons3[i], z, 1), x, X), y, YT) % cT);
  V1 = vector(10, i, my(m = subst(mons3[i], z, 1));
       (fxT * subst(subst(deriv(m, y), x, X), y, YT) - fyT * subst(subst(deriv(m, x), x, X), y, YT)) % cT);
  for (k = 0, 2, listput(rows, vector(10, i, polcoef(V0[i], k, X))));
  for (k = 0, 2, listput(rows, vector(10, i, polcoef(V1[i], k, X))));
  M = matrix(9, 10, i, j, Mod(lift(rows[i][j]), A3));
  ker = matker(M);
  GAkerdim = #ker;
  gv = ker[, 1];
  \\ normalise: coefficient of y z^2 equal to 1, then clear rational denominators
  gv = gv / gv[9];
  den = lcm(vector(10, i, denominator(content(lift(gv[i])))));
  GA = den * sum(i = 1, 10, gv[i] * mons3[i]);
}

\\ ---------- evaluation on Galois orbits of points ----------
\\ orb = [m(u), [X(u), Y(u), Z(u)]], m in Q[u] monic squarefree; the points are (X(al):Y(al):Z(al)), m(al) = 0.
\\ evalorb(Phi, orb) = prod over the roots al of Phi(X(al), Y(al), Z(al)), an element of A3 (or Q).
evalorb(Phi, orb) = {
  my(m = orb[1], V = orb[2], h);
  h = substvec(Phi, [x, y, z], V);
  if (poldegree(m, u) == 1, return(subst(h, u, -polcoef(m, 0, u))));
  h = h % m;
  polresultant(m, h, u);
}
ptorb(P) = [u, [P[1], P[2], P[3]]];                 \\ a rational point as an orbit of degree 1
orbdeg(orb) = poldegree(orb[1], u);
\\ D = list of [n, orb]; delta(D) = prod evalorb(GA, orb)^n, a representative of the class in A^x / A^x2 Q^x
delta(D) = {
  my(s = 0, r = Mod(1, A3), v);
  for (i = 1, #D, s += D[i][1] * orbdeg(D[i][2]);
    v = evalorb(GA, D[i][2]);
    if (v == 0, error("orbit in the support of div(GA)"));
    r *= v^D[i][1]);
  if (s != 0, error("divisor of nonzero degree"));
  r;
}
\\ check that an orbit lies on C
onC(orb) = { my(h = substvec(F, [x, y, z], orb[2])); (h % orb[1]) == 0; }

\\ ---------- primes of A3 above 2 and 7, local square classes ----------
P2 = idealprimedec(bnf, 2); if (#P2 != 1 || P2[1].e != 4 || P2[1].f != 2, error("2 in A3"));
P2 = P2[1];
P7 = idealprimedec(bnf, 7);
P7b = if (P7[1].e == 7, P7[1], P7[2]); P7a = if (P7[1].e == 1, P7[1], P7[2]);
if (P7a.e != 1 || P7a.f != 1 || P7b.e != 7 || P7b.f != 1, error("7 in A3"));
uniformizer(pr) = { my(p = pr.p, g = pr.gen[2]);
  if (nfeltval(bnf, p, pr) == 1, return(p));
  if (nfeltval(bnf, g, pr) == 1, return(g));
  g = g + p; if (nfeltval(bnf, g, pr) == 1, return(g));
  error("no uniformizer"); }
pi2 = uniformizer(P2); pi7a = uniformizer(P7a); pi7b = uniformizer(P7b);
bid2 = idealstar(bnf, idealpow(bnf, P2, 9), 1);    \\ U/U^2 = (O/P^9)^x / squares since 1 + P^9 = 1 + 4P is in U^2
ev2 = [i | i <- [1..#bid2.cyc], bid2.cyc[i] % 2 == 0];
if (#ev2 != 9, error("2-rank of (O/P^9)^x is not 9"));
\\ class of b in L^x / L^x2 (L = completion at P2), as a vector in F_2^10
cl2(b) = { my(v = nfeltval(bnf, b, P2), uu = nfeltmul(bnf, b, nfeltpow(bnf, pi2, -v)), lg);
  lg = ideallog(bnf, uu, bid2);
  concat([v % 2], vector(#ev2, i, lg[ev2[i]] % 2)); }
modpr7a = nfmodprinit(bnf, P7a); modpr7b = nfmodprinit(bnf, P7b);
legF7(r) = { if (r == 0, error("not a unit")); if (r^3 == 1, 0, 1); }   \\ Euler criterion in F_7
\\ class of b in (A3 (x) Q_7)^x / squares = (Q_7^x/Q_7^x2) x (L7^x/L7^x2), vector in F_2^4
cl7(b) = { my(va = nfeltval(bnf, b, P7a), vb = nfeltval(bnf, b, P7b), ua, ub);
  ua = nfeltmul(bnf, b, nfeltpow(bnf, pi7a, -va)); ub = nfeltmul(bnf, b, nfeltpow(bnf, pi7b, -vb));
  [va % 2, legF7(nfmodpr(bnf, ua, modpr7a)), vb % 2, legF7(nfmodpr(bnf, ub, modpr7b))]; }
\\ signs at the two real places, vector in F_2^2
clinf(b) = { my(s = nfeltsign(bnf, b)); vector(#s, i, if (s[i] < 0, 1, 0)); }

\\ ---------- linear algebra over F_2 ----------
f2rank(M) = matrank(M * Mod(1, 2));
\\ annihilator: rows y with y * v = 0 for all columns v of B (B has entries 0/1)
annih(B) = { my(K = matker(B~ * Mod(1, 2))); lift(K~); }

\\ ---------- S-units, S = primes above 2 and 7 (h(A3) = 1) ----------
Sprimes = [P2, P7a, P7b];
Uobj = bnfunits(bnf, Sprimes);
Sgens = vector(#Uobj[1], i, nfbasistoalg(bnf, nffactorback(bnf, Uobj[1][i])));   \\ 3 S-units, 4 units, torsion -1
\\ class in A(S,2) = O_S^x / squares (a vector in F_2^8 on Sgens) of an element b of A3^x whose class in
\\ A3^x / A3^x2 Q^x is unramified outside {2, 7}; also returns the rational factor used.
globcls(b) = {
  my(fa, ps = List(), q = 1, I = 1, beta, e);
  b = nfbasistoalg(bnf, b); b = b / content(lift(b));
  fa = idealfactor(bnf, b);
  for (i = 1, #fa~, my(pr = fa[i, 1]);
    if (pr.p == 2 || pr.p == 7, next);
    if (fa[i, 2] % 2, if (!setsearch(Set(ps), pr.p), listput(ps, pr.p))));
  for (i = 1, #ps, my(p = ps[i], dec = idealprimedec(bnf, p));
    for (j = 1, #dec, if (nfeltval(bnf, b, dec[j]) % 2 == 0, error("class ramified at ", p)));
    q *= p);
  b = b * q;
  fa = idealfactor(bnf, b);
  for (i = 1, #fa~, my(pr = fa[i, 1]);
    if (pr.p == 2 || pr.p == 7, next);
    if (fa[i, 2] % 2, error("odd valuation left"));
    I = idealmul(bnf, I, idealpow(bnf, pr, fa[i, 2] / 2)));
  beta = bnfisprincipal(bnf, I, 3);   \\ flag 3: return the generator, increasing precision as needed
  if (beta[1] != vector(#beta[1], i, 0)~, error("not principal"));
  beta = nfbasistoalg(bnf, beta[2]);
  e = bnfisunit(bnf, b / beta^2, Uobj);
  if (#e == 0, error("not an S-unit"));
  [lift(e~ * Mod(1, 2)), q];
}

\\ ---------- the residual divisor R of G_A (Q-rational; checked in two_descent_algebra.gp) ----------
{
  my(R = polresultant(F, GA, y), q = subst(R, z, 1), cx = subst(cT, X, x), r3, g, yR);
  while (polcoef(q, 0, x) == 0, q = q / x); while (q % cx == 0, q = q \ cx);
  r3 = simplify(lift(q / pollead(q)));
  rR = subst(r3, x, u);
  g = gcd(substvec(f1, [x], [Mod(u, rR)]), polresultant(A3, lift(substvec(subst(GA, z, 1), [x], [Mod(u, rR)])), a));
  if (poldegree(g, y) != 1, error("R"));
  yR = lift(-polcoef(g, 0, y) / polcoef(g, 1, y));
  orbR = [rR, [u, yR, 1]];
}
