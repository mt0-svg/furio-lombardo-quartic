\\ prym_involution.gp: the reduced involution rbar of the 21-orbit Prym curves F_delta over K21.
\\ F_delta = q(t) h(t) over K21 (q quadratic: the two Weierstrass points fixed by rbar); rbar = harmonic
\\ involution with fixed points the roots of q: sigma(t) = -(B t + 2C)/(2A t + B) for q = A t^2 + B t + C.
\\ Checks that sigma permutes the roots of h, computes lambda with f(sigma(t)) (2At + B)^6 = lambda f(t);
\\ the lift r(t, y) = (sigma(t), sqrt(lambda) y / (2At + B)^3) has order 4 (r^2 = hyperelliptic involution)
\\ and is defined over K21(sqrt(lambda)).  Run from code/earlier-computations: gp -q prym_involution.gp < /dev/null
default(parisizemax, 4*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("bruin_form.gp");
chk(c, msg) = if (!c, error("FAILED: ", msg), print("ok: ", msg));
nf = nfinit(K21);
autdata(F) = {
  my(f = lift(Mod(F, K21)), fa = nffactor(nf, f), q, h, A, B, C, s, den, fs, lam);
  q = 0; h = 0;
  for (i = 1, #fa~, if (poldegree(fa[i,1]) == 2, q = fa[i,1], h = fa[i,1]));
  q = Mod(q, K21); h = Mod(h, K21);
  A = polcoef(q, 2, t); B = polcoef(q, 1, t); C = polcoef(q, 0, t);
  den = 2*A*t + B;
  \\ h(sigma(t)) * den^4 is proportional to h(t)
  my(hs = substpol(0, t, t)); hs = sum(i = 0, 4, polcoef(h, i, t) * (-(B*t + 2*C))^i * den^(4 - i));
  my(rat = polcoef(hs, 4, t) / polcoef(h, 4, t));
  chk(hs == rat * h, "rbar permutes the roots of the quartic factor");
  fs = sum(i = 0, 6, polcoef(Mod(f, K21), i, t) * (-(B*t + 2*C))^i * den^(6 - i));
  lam = polcoef(fs, 6, t) / polcoef(Mod(f, K21), 6, t);
  chk(fs == lam * Mod(f, K21), "f(sigma(t)) (2At + B)^6 = lambda f(t)");
  [q, h, [A, B, C], lam];
}
D0 = autdata(F0); D1 = autdata(F1);
issq(e) = #nfroots(nf, t^2 - lift(e)) > 0;
print("lambda0 square in K21: ", issq(D0[4]), ";  lambda1 square in K21: ", issq(D1[4]));
print("-lambda0 square: ", issq(-D0[4]), ";  lambda0 * lambda1 square: ", issq(D0[4] * D1[4]));
\\ sign convention check: with sigma(sigma(t)) = t, the lift squared is y -> lambda * (...) y; record lambda mod squares
bnf = bnfinit(K21, 1);
print("lambda0 factorisation: ", apply(v -> [v[1].p, v[1].e, v[1].f, v[2]], Vec(idealfactor(nf, D0[4])~)));
print("disc of q0: ", lift(poldisc(D0[1])));
print("disc(q0)/lambda0 square: ", issq(poldisc(D0[1]) / D0[4]), ";  -disc(q0)/lambda0 square: ", issq(-poldisc(D0[1]) / D0[4]));
fn = "prym_involution_data.gp"; system(Str("rm -f ", fn));
write(fn, "\\\\ prym_involution.gp output: F_delta = q*h over K21, rbar(t) = -(B t + 2C)/(2A t + B), f(rbar t)(2At+B)^6 = lam f(t)");
write(fn, "q0 = ", lift(D0[1]), "; h0 = ", lift(D0[2]), "; lam0 = ", lift(D0[4]), ";");
write(fn, "q1 = ", lift(D1[1]), "; h1 = ", lift(D1[2]), "; lam1 = ", lift(D1[4]), ";");
quit;
