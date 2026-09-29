\\ bruin_form_reduce.gp: Bruin form of C over K21 (eta in the Galois orbit of size 21) from the raw Bruin form bruin_form_orbit21.gp,
\\ reduced (primitive conics, twist e reduced modulo squares), twists delta(P0), delta(P1), Prym curves
\\ F_delta : Y^2 = -delta det(M1 + 2t M2 + t^2 M3), and the known-answer test (trace identity at degree 1 primes).
\\ Same steps as prym_3_reduce.gp (14-orbit). Run from code/earlier-computations: gp -q bruin_form_reduce.gp < /dev/null
default(parisizemax, 4*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("prym_lib.gp");
read("bruin_form_orbit21.gp");
chk(c, msg) = if (!c, error("FAILED: ", msg), print("ok: ", msg));
F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
KK = Kb;
bnf = bnfinit(KK, 1); nf = bnf.nf;
print("K21: class group ", bnf.cyc, " (GRH), signature ", nf.sign, ", unit rank ", #bnf.fu, ", torsion ", bnf.tu[1]);
B1 = Mod(R1, KK); B2 = Mod(R2, KK); B3 = Mod(R3, KK);
chk(B1*B3 - B2^2 == Mod(cR, KK) * F, "input Bruin form");
mons2 = [x^2, x*y, x*z, y^2, y*z, z^2];
cf(Q, m) = polcoef(polcoef(polcoef(Q, poldegree(m, x), x), poldegree(m, y), y), poldegree(m, z), z);
coefs2(Q) = vector(6, j, cf(Q, mons2[j]));
cf4(Q, m) = cf(Q, m);
\\ primitive multiple of a conic: divide by a generator of the content ideal (class group data, GRH)
primitive(Q) = {
  my(c = coefs2(Q), I, g);
  I = 0; for (j = 1, 6, if (c[j] != 0, I = if (I == 0, idealhnf(nf, c[j]), idealadd(nf, I, c[j]))));
  g = bnfisprincipal(bnf, I, 3); if (g[1] != vector(#g[1], i, 0)~, print("content not principal: dividing by a generator of an equivalent ideal"); );
  g = nfbasistoalg(nf, g[2]);
  Q / g;
}
\\ small representative of e modulo squares: e = e0 * f^2
sqred(e) = {
  my(fa = idealfactor(nf, e), I = 1, f0, e1, g, uu, ex, u0, f1, cl);
  for (i = 1, #fa~, if (fa[i, 2] \ 2 != 0, I = idealmul(nf, I, idealpow(nf, fa[i, 1], fa[i, 2] \ 2))));
  cl = bnfisprincipal(bnf, I, 3);
  if (cl[1] != vector(#cl[1], i, 0)~, error("sqred: square part not principal (class group nontrivial)"));
  f0 = nfbasistoalg(nf, cl[2]);
  e1 = e / f0^2;
  cl = bnfisprincipal(bnf, idealhnf(nf, e1), 3);
  if (cl[1] != vector(#cl[1], i, 0)~, error("sqred: squarefree part not principal"));
  g = nfbasistoalg(nf, cl[2]);
  uu = e1 / g;
  ex = bnfisunit(bnf, uu);
  if (#ex == 0, error("not a unit"));
  u0 = prod(i = 1, #bnf.fu, bnf.fu[i]^(ex[i] % 2)) * bnf.tu[2]^(ex[#ex] % 2);
  my(e0 = g * u0);
  if (#nfroots(nf, t^2 - lift(e / e0)) == 0, error("sqred: e/e0 not a square"));
  [e0, e / e0];
}
q1 = primitive(B1); q3 = primitive(B3); q2 = primitive(B2);
{
  my(G = q2^2, H = q1 * q3, mons4 = List(), M, rhs, sol);
  forvec(v = [[0, 4], [0, 4]], if (v[1] + v[2] <= 4, listput(mons4, x^v[1] * y^v[2] * z^(4 - v[1] - v[2]))));
  M = matrix(#mons4, 2, i, j, if (j == 1, cf4(H, mons4[i]), cf4(F, mons4[i])));
  rhs = vector(#mons4, i, cf4(G, mons4[i]))~;
  sol = matinverseimage(M, rhs);
  if (#sol == 0 || M * sol != rhs, error("q2^2 is not e q1 q3 + c F"));
  E = sol[1];
}
ef = sqred(E); e0 = ef[1];
fr = nfroots(nf, t^2 - lift(ef[2])); chk(#fr == 2, "E/e0 is a square in K21");
f = Mod(fr[1], KK);
Q1 = q1; Q2 = q2 / f; Q3 = e0 * q3;
cB = cf(Q1*Q3 - Q2^2, x^4) / cf(F, x^4);
chk(Q1*Q3 - Q2^2 == cB * F, "reduced Bruin form Q1*Q3 - Q2^2 = c*F over K21");
print("characters of the reduced Q1, Q2, Q3: ", [#Str(lift(Q1)), #Str(lift(Q2)), #Str(lift(Q3))]);
Pts = [[0,0,1], [1,1,1], [2,0,1], [-1,0,1]];
dval(P) = { my(q = substvec(Q1, [x,y,z], P)); if (q == 0, q = substvec(Q3, [x,y,z], P)); if (q == 0, error("Q1 and Q3 vanish at ", P)); q; };
dl = vector(4, i, sqred(dval(Pts[i]))[1]);
issq(e) = #nfroots(nf, t^2 - lift(e)) > 0;
chk(issq(dl[3] / dl[1]), "delta(P2) = delta(P0) modulo squares (predicted by P2 = P0 mod 2J(Q))");
chk(issq(dl[4] / dl[2]), "delta(P3) = delta(P1) modulo squares (predicted by P3 = P1 mod 2J(Q))");
print("delta(P1)/delta(P0) is a square: ", issq(dl[2] / dl[1]));
d0 = dl[1]; d1 = dl[2];
print("delta0 = ", lift(d0)); print("delta1 = ", lift(d1));
print("ideal of delta0: ", apply(v -> [v[1].p, v[1].e, v[1].f, v[2]], Vec(idealfactor(nf, d0)~)));
print("ideal of delta1: ", apply(v -> [v[1].p, v[1].e, v[1].f, v[2]], Vec(idealfactor(nf, d1)~)));
F0 = prymf(Q1, Q2, Q3, d0); F1 = prymf(Q1, Q2, Q3, d1);
print("deg F0 = ", poldegree(F0, t), ", deg F1 = ", poldegree(F1, t));
fn = "bruin_form.gp"; system(Str("rm -f ", fn));    \\ write appends
write(fn, "\\\\ reduced Bruin form of C over K21 (bruin_form_reduce.gp): Q1*Q3 - Q2^2 = cB*F; twists d0 = delta(P0), d1 = delta(P1); Prym curves F0, F1");
write(fn, "K21 = ", KK, ";");
write(fn, "Q1 = ", lift(Q1), ";");
write(fn, "Q2 = ", lift(Q2), ";");
write(fn, "Q3 = ", lift(Q3), ";");
write(fn, "cB = ", lift(cB), ";");
write(fn, "d0 = ", lift(d0), ";");
write(fn, "d1 = ", lift(d1), ";");
write(fn, "F0 = ", lift(F0), ";");
write(fn, "F1 = ", lift(F1), ";");
print("written ", fn);
\\ ---------- known-answer test: trace identity at degree 1 primes of K21 ----------
denall = simplify(lcm(apply(simplify, [denominator(content(lift(Q1))), denominator(content(lift(Q2))), denominator(content(lift(Q3))), denominator(content(lift(d0))), denominator(content(lift(d1)))])));
if (type(denall) != "t_INT", error("denominator lcm is not an integer"));
redc(c, r, p) = { my(l = lift(c * Mod(1, KK))); Mod(subst(l, b, r), p); }
redform(Q, r, p) = { my(v); if (type(Q) != "t_POL" || variable(Q) == b, return(lift(redc(Q, r, p)))); v = variable(Q); sum(i = 0, poldegree(Q, v), redform(polcoef(Q, i, v), r, p) * v^i); }
{
  my(nt = 0);
  forprime(p = 3, 300,
    if (p == 7 || denall % p == 0 || poldisc(KK) % p == 0, next);
    my(rts = polrootsmod(KK, p));
    for (k = 1, #rts, my(r = lift(rts[k]), q1r, q2r, q3r, d0r, d1r, F0r, F1r, s0, s1, n0, n1);
      q1r = redform(Q1, r, p); q2r = redform(Q2, r, p); q3r = redform(Q3, r, p);
      d0r = lift(redc(d0, r, p)); d1r = lift(redc(d1, r, p));
      if (d0r == 0 || d1r == 0, next);
      F0r = redform(F0, r, p); F1r = redform(F1, r, p);
      n0 = g2count_p(F0r, p); n1 = g2count_p(F1r, p);
      if (n0 < 0 || n1 < 0 || poldisc(F0r * Mod(1, p)) == 0 || poldisc(F1r * Mod(1, p)) == 0, print("skip p = ", p, " (bad reduction of the model)"); next);
      iferr(s0 = prymsum_p(q1r, q2r, q3r, d0r, p); s1 = prymsum_p(q1r, q2r, q3r, d1r, p), E, print("skip p = ", p, ": ", E); next);
      print1("[", p, ": ", s0[2], " ", n0 - p - 1, " | ", s1[2], " ", n1 - p - 1, "] ");
      if (s0[2] != n0 - p - 1 || s1[2] != n1 - p - 1, error("trace identity fails at p = ", p, ", root ", r, ": ", [s0, n0, s1, n1]));
      nt++));
  print();
  chk(nt >= 10, Str("trace identity #D_delta(F_p) - #C(F_p) = #F_delta(F_p) - p - 1 for delta0 and delta1 at ", nt, " degree 1 primes of K21"));
}
quit;
