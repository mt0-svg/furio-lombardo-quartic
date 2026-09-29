\\ integral_model_hypotheses.gp: the three hypotheses of the integral model, exactly
\\ (2-adic precision 2^P, valuations far below it), for the base setups of R7/ConcreteKv.lean:
\\ f = fK k = F_k(X + k), f0 = f(0), p = pi^a, ft(X) = f(p X) / f0, Vt = tbeta(ft) the cubic Taylor
\\ polynomial of sqrt(ft) at 0 (= tbeta(f)(p X) = b^-1 V0(p X)), and f - V0^2 = c0 X^4 w0, so that
\\ ft - Vt^2 = X^4 (R0 + R1 X + R2 X^2) with Ri = p^(4+i) tRi(f) / f0.
\\   H1: the coefficients tb1 p, tb2 p^2, tb3 p^3 of Vt are integral;
\\   H2: R0, R1, R2 are in 4 O (v >= 6);
\\   H3: v(R2) = 6 exactly (R2 / 4 = c0 p^6 / (4 f0) is a unit).
\\ The scaling a is tried from 0 to 3 for each twist; the model uses a = 2 (k = 0), a = 0 (k = 1).
\\ Run from code/local-group:  gp -q integral_model_hypotheses.gp < /dev/null > integral_model_hypotheses.out
default(parisizemax, 10^9);
read("../local-group/chart_lib.gp");
yv = varlower("yv");
P = 400;
q = factorpadic(K21, 2, P);
g3 = [q[i,1] | i <- [1..#q[,1]], poldegree(q[i,1]) == 3][1];
g3v = subst(g3, variable(g3), yv);
Y = Mod(yv, g3v);
toKv(c) = subst(lift(Mod(c, K21)), b, Y);
vpi(z) = if (z == 0, oo, valuation(norm(Mod(1, g3v) * z), 2));
if (vpi(toKv(PI)) != 1 || vpi(2) != 3, error("place check"));
piv = toKv(PI);
printf("PARI/GP %s, 2-adic precision 2^%d, v = v_pi, v(2) = 3\n", version(), P);
{
for (k = 0, 1,
  my(F = frev[k + 1], fx = subst(F, t, xp + k), f);
  f = vector(7, j, toKv(polcoef(fx, j - 1, xp)));
  printf("k = %d: v(f_j), j = 0..6: %s\n", k, vector(7, j, vpi(f[j])));
  my(tb1 = f[2] / (2 * f[1]), tb2, tb3, R0, R1, R2);
  tb2 = (f[3] / f[1] - tb1^2) / 2;
  tb3 = (f[4] / f[1] - 2 * tb1 * tb2) / 2;
  R0 = f[5] - f[1] * (tb2^2 + 2 * tb1 * tb3);
  R1 = f[6] - f[1] * (2 * tb2 * tb3);
  R2 = f[7] - f[1] * tb3^2;
  for (a = 0, 3,
    my(p = piv^a, h1, h2, v2);
    h1 = [vpi(tb1 * p), vpi(tb2 * p^2), vpi(tb3 * p^3)];
    h2 = [vpi(R0 * p^4 / f[1]), vpi(R1 * p^5 / f[1]), vpi(R2 * p^6 / f[1])];
    printf("  a = %d: v(tb1 p, tb2 p^2, tb3 p^3) = %s  H1 %s; v(R0, R1, R2) = %s  H2 %s  H3 %s\n", a, h1,
      if (vecmin(h1) >= 0, "ok", "FAILS"), h2, if (vecmin(h2) >= 6, "ok", "FAILS"), if (h2[3] == 6, "ok", "FAILS"))));
}
