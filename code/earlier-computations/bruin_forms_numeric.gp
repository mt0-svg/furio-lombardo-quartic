\\ Bruin forms Q1*Q3 = Q2^2 of C for all 63 nonzero 2-torsion points, numerically, from the bitangents:
\\ Steiner complexes (6 pairs of bitangents with b_i - b_j = eta; two pairs are in the same complex iff their
\\ 8 contact points lie on a conic), net N_eta = span of the 6 conics b_i b_j, Veronese conic Z in P(N_eta)
\\ through the 6 points b_i b_j (the contact conics of eta), Q1 = member of Z through P0 (tangent to C there),
\\ Q3 = member through P1, Q2 = pole of the line Q1 Q3 with respect to Z, scaled so that Q1 Q3 - Q2^2 = c F.
\\ Normalisation (Galois equivariant): Q1 and Q2 with coefficient of z^2... (first nonzero of a fixed monomial
\\ list) equal to 1, Q3 then determined.  Output: prym21 data after orbit decomposition (bitan_3).
\\ Run: gp -q bruin_forms_numeric.gp < /dev/null
default(parisizemax, 4*10^9); default(nbthreads, 1);
default(realprecision, 800);
[x, y, z, m, k, X];
F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
g = subst(subst(F, z, 1), y, m*x + k);
[g0, g1, g2, g3, g4] = vector(5, i, polcoef(g, i - 1, x));
E1 = 8*g4^2*g1 - g3*(4*g2*g4 - g3^2);
E0 = 64*g4^3*g0 - (4*g2*g4 - g3^2)^2;
Rm = polresultant(E1, E0, k);
fa = factor(Rm); B28 = 0; for (i = 1, #fa~, if (poldegree(fa[i,1]) == 28, B28 = fa[i,1]));
ms = polroots(B28);
\\ k from the common root of E1(m_i, k), E0(m_i, k): gcd numerically via the resultant-free approach:
\\ roots of E1(m_i, .) (cubic), pick the one where E0 vanishes
bit = vector(28);
{
  for (i = 1, 28,
    my(mi = ms[i], e1 = subst(E1, m, mi), e0 = subst(E0, m, mi), rk = polroots(e1), best = 0, bv = 1e100);
    for (j = 1, #rk, my(v = abs(subst(e0, k, rk[j]))); if (v < bv, bv = v; best = rk[j]));
    if (bv > 1e-300, print("warning: residual ", bv, " at bitangent ", i));
    bit[i] = [mi, best]);
}
\\ contact points of bitangent i: roots of g4 x^2 + (g3/2) x + q g4... use g = g4 (x^2 + p x + q)^2
cpts = vector(28, i, my(mi = bit[i][1], ki = bit[i][2], G = subst(subst(g, m, mi), k, ki), G4 = polcoef(G, 4), p = polcoef(G, 3)/(2*G4), q = (polcoef(G, 2)/G4 - p^2)/2, r = polroots(x^2 + p*x + q)); vector(2, j, [r[j], mi*r[j] + ki, 1]));
\\ check: F vanishes at contact points
print("max |F| at contact points: ", vecmax(vector(28, i, vecmax(vector(2, j, abs(substvec(F, [x,y,z], cpts[i][j])))))));
mons2 = [x^2, x*y, x*z, y^2, y*z, z^2];
ev2(P) = vector(6, j, substvec(mons2[j], [x, y, z], P));
\\ 8 contact points on a conic: smallest singular value of the 8 x 6 matrix
\\ hermitian smallest eigenvalue via determinant of M^* M scaled
syzdet(i, j, k2, l) = {
  my(P = concat([cpts[i], cpts[j], cpts[k2], cpts[l]]), M = matrix(8, 6, a, b, ev2(P[a])[b]), H = conj(M~) * M);
  abs(matdet(H)) / vecmax(abs(H))^6;
}
coef4(Q) = { my(v = List()); for (i = 0, 4, for (j = 0, 4 - i, listput(v, polcoef(polcoef(polcoef(Q, i, x), j, y), 4 - i - j, z)))); Vec(v); }
pairs = List(); for (i = 1, 28, for (j = i + 1, 28, listput(pairs, [i, j])));
\\ Steiner complexes
used = vector(#pairs); cx = List();
{
  for (a = 1, #pairs, if (used[a], next);
    my(pa = pairs[a], mem = List([a]));
    for (b = a + 1, #pairs, if (used[b], next);
      my(pb = pairs[b]);
      if (#setintersect(Set(pa), Set(pb)) > 0, next);
      if (syzdet(pa[1], pa[2], pb[1], pb[2]) < 1e-500, listput(mem, b)));
    if (#mem != 6, error("Steiner complex of size ", #mem, " for pair ", pa));
    for (c = 1, #mem, used[mem[c]] = 1);
    listput(cx, Vec(mem)));
}
print("Steiner complexes: ", #cx);
line(i) = y - bit[i][1]*x - bit[i][2]*z;
coef2(Q) = vector(6, j, polcoef(polcoef(polcoef(Q, poldegree(mons2[j], x), x), poldegree(mons2[j], y), y), poldegree(mons2[j], z), z));
P0 = [0, 0, 1]; P1 = [1, 1, 1];
gradF(P) = vector(3, i, substvec(deriv(F, [x, y, z][i]), [x, y, z], P));
\\ first nonzero coefficient normalisation w.r.t. a fixed monomial order
normz(Q) = { my(c = coef2(Q)); for (j = 1, 6, if (abs(c[j]) > 1e-100, return(Q / c[j]))); error("zero"); }
bruin = vector(#cx);
{
  for (e = 1, #cx,
    my(prs = vector(6, s, pairs[cx[e][s]]), cons = vector(6, s, line(prs[s][1]) * line(prs[s][2])), V, Mb, N, cz, Zq, Qp0, Qp1, Q1, Q3, Q2, lam, cF);
    V = matrix(6, 6, a, b, coef2(cons[b])[a]);
    \\ basis of the net: first three independent columns
    my(sel = [1, 2, 3]);   \\ any three of the six points of the smooth conic Z are independent
    Mb = matrix(6, 3, a, b, V[a, sel[b]]);
    N = vector(3, s, cons[sel[s]]);
    \\ coordinates of the 6 conics in the basis N (least squares, exact in theory)
    cz = vector(6, s, matsolve(Mb~ * Mb, Mb~ * V[, s]));
    \\ residual check
    if (vecmax(vector(6, s, vecmax(abs(Mb * cz[s] - V[, s])))) > 1e-600, print("net residual large at eta ", e));
    \\ conic Z through the 6 points in P^2 (coordinates u, v, w)
    my(Mz = matrix(6, 6, s, j, my(c = cz[s]); [c[1]^2, c[1]*c[2], c[1]*c[3], c[2]^2, c[2]*c[3], c[3]^2][j]));

    \\ numerical kernel: smallest singular vector via inverse iteration on Mz^* Mz

    \\ fall back to exact-style: solve with last coordinate 1 using 5 points
    \\ Z passes through the basis points e1, e2, e3: Z = a uv + b uw + c vw; points 4, 5 give (a : b : c)
    my(r4 = [Mz[4,2], Mz[4,3], Mz[4,5]], r5 = [Mz[5,2], Mz[5,3], Mz[5,5]], abc, zc);
    abc = [r4[2]*r5[3] - r4[3]*r5[2], r4[3]*r5[1] - r4[1]*r5[3], r4[1]*r5[2] - r4[2]*r5[1]];
    zc = [0, abc[1], abc[2], 0, abc[3], 0]~;
    if (vecmax(abs(vector(3, s, cz[s][s] - 1))) > 1e-600, print("basis coordinates wrong at eta ", e));
    if (abs(Mz[6, ] * zc) > 1e-500, print("Z residual ", abs(Mz[6, ] * zc), " at eta ", e));
    \\ Zq as symmetric matrix
    Zq = [zc[1], zc[2]/2, zc[3]/2; zc[2]/2, zc[4], zc[5]/2; zc[3]/2, zc[5]/2, zc[6]];
    \\ member through P: points of P(N) with Q(P) = 0 form a line; tangent to Z there; find tangency point
    my(member = (P) -> my(ev = vector(3, s, substvec(N[s], [x, y, z], P)), l = ev~, adj = matadjoint(Zq), pt);
      \\ tangency point of the line l.X = 0 with Z: pole of the line = adj(Zq) * l
      pt = adj * l; pt);
    my(c0 = member(P0), c1 = member(P1));
    Qp0 = sum(s = 1, 3, c0[s] * N[s]); Qp1 = sum(s = 1, 3, c1[s] * N[s]);
    \\ check tangency of Qp0 to C at P0: gradient proportional
    \\ Q2: pole of the line through c0, c1 w.r.t. Z: line = c0 x c1 (cross product), pole = Zq^-1 * line
    my(ln = [c0[2]*c1[3] - c0[3]*c1[2], c0[3]*c1[1] - c0[1]*c1[3], c0[1]*c1[2] - c0[2]*c1[1]]~, c2 = matsolve(Zq, ln));
    Q2 = sum(s = 1, 3, c2[s] * N[s]);
    Q1 = normz(Qp0); Q2 = normz(Q2); Q3 = normz(Qp1);
    \\ Q1 * (mu Q3) - Q2^2 = c F: find mu from a point of C (use P2 = (2:0:1))
    my(P2 = [2, 0, 1], q1 = substvec(Q1, [x,y,z], P2), q2 = substvec(Q2, [x,y,z], P2), q3 = substvec(Q3, [x,y,z], P2));
    lam = q2^2 / (q1 * q3);
    Q3 = lam * Q3;
    my(D = Q1*Q3 - Q2^2, cc = polcoef(polcoef(polcoef(D, 4, x), 0, y), 0, z));
    cF = cc;   \\ coefficient of x^4 in F is 1
    my(res = vecmax(abs(Vec(coef4(D - cF*F)))));
    bruin[e] = [Q1, Q2, Q3, cF, res]);
}
print("max residual |Q1 Q3 - Q2^2 - c F|: ", vecmax(vector(#bruin, e, bruin[e][5])));
\\ orbit decomposition by an invariant theta(eta): weighted sum of coefficients of Q1 and Q2
wt = [3, -5, 7, 2, -1, 4];
thv(e) = sum(j = 1, 6, wt[j] * (coef2(bruin[e][1])[j] + 2*coef2(bruin[e][2])[j]));
th = vector(#bruin, e, thv(e));
P63 = prod(e = 1, #bruin, X - th[e]);
print("max imaginary part of P63 coefficients: ", vecmax(abs(imag(Vec(P63)))));
P63r = apply(c -> bestappr(real(c), 10^300), P63);
print("rational P63 check: ", vecmax(abs(Vec(P63 - P63r))) < 1e-200);
fa63 = factor(P63r);
print("orbit factors: ", vector(#fa63~, i, [poldegree(fa63[i,1]), fa63[i,2]]));
system("rm -f bruin_forms_numeric.bin"); writebin("bruin_forms_numeric.bin", [bruin, th, fa63]);   \\ writebin appends
quit;
