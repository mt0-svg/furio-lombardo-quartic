\\ completion_kv.gp: the completion K_v of K21 at the place v above 2 with e = 3, as K' = Q_2(pi), E(pi) = 0 Eisenstein,
\\ with a certified embedding K21 -> K' (library for the certified pipeline p21_45_cert.gp; ball arithmetic of
\\ code/lib/pball.gp).
\\ Construction (only the final certificate matters, not how E and theta were found):
\\ E = the characteristic polynomial over Q_2 of the uniformizer PI = pr.gen[2] in the cubic factor of K21 over Q_2
\\ (factorpadic), truncated to rational coefficients and checked Eisenstein; theta0 = coordinates of b on 1, PI, PI^2
\\ in that factor; then Newton for K21(theta) = 0 in Q[pi]/(E). Certificate (Hensel): v(K21(theta)) > 2 v(K21'(theta))
\\ gives a unique root theta* of K21 in K' with v(theta* - theta) >= v(K21(theta)) - v(K21'(theta)). The map
\\ b -> theta* is a field embedding K21 -> K'; its place is pr because v(gen2(theta*)) > 0 and v(2) > 0 (pr = (2, gen2)
\\ is contained in the prime of the induced valuation, both are maximal). K' has degree 3 = [K21_pr : Q_2], so K' is the
\\ completion. Also checked: v(a(theta*)) = nfeltval(a, pr) for random a (known-answer test).
\\ Interface: kv_init(mw) (sets up pball with cap mw), kv(a) = ball of the image of a in K21 (t_POLMOD in b, polynomial
\\ in b or rational), kvx(P) for a polynomial in x or t with K21 coefficients (balls, lowest degree first).
\\ Requires the variable b and K21 (bruin_form.gp) and nfK, pr (as in leading_class_explore.gp).
read("../lib/pball.gp");
kv_init(mw) = {
  my(F = factorpadic(K21, 2, 80), g, PIp, cp, E, M, c, th, it = 0, vK, vD);
  g = [F[i, 1] | i <- [1 .. #F~], poldegree(F[i, 1]) == 3];
  if (#g != 1, error("kv_init: one cubic factor expected")); g = g[1];
  PIp = lift(nfbasistoalg(nfK, pr.gen[2]));
  if (nfeltval(nfK, PIp, pr) != 1, error("kv_init: gen2 is not a uniformizer"));
  cp = charpoly(Mod(subst(PIp, b, 'b), g), 'x);
  E = Pol(apply(cc -> truncate(cc), Vec(cp)), 'x);
  pb_init(2, E, mw);
  \\ coordinates of b on 1, PI, PI^2 in Q_2[b]/(g)
  M = matrix(3, 3, i, j, polcoef(lift(Mod(subst(PIp, b, 'b), g)^(j - 1)), i - 1, 'b));
  c = matsolve(M, [0, 1, 0]~);
  th = Mod(sum(j = 1, 3, truncate(c[j]) * PBV^(j - 1)), PB_EP);
  my(KP = subst(K21, b, 'X), KD = deriv(KP, 'X), ev = ((P, a) -> subst(lift(P), 'X, a)));
  KV_ev = ev; KV_KP = KP; KV_KD = KD;
  while (pb_vc(subst(KP, 'X, th)) < 2 * mw + 40,
    th = pb_red(th - subst(KP, 'X, th) / subst(KD, 'X, th), 2 * mw + 60); it++; if (it > 60, error("kv_init: Newton")));
  vK = pb_vc(subst(KP, 'X, th)); vD = pb_vc(subst(KD, 'X, th));
  if (vK <= 2 * vD, error("kv_init: Hensel condition"));
  KV_TH = [th, min(vK - vD, mw)];
  KV_CERT = [vK, vD];
  \\ place check
  my(g2 = kv(nfbasistoalg(nfK, pr.gen[2])));
  if (!(pb_nz(g2) && pb_vc(g2[1]) > 0), error("kv_init: the place of the embedding is not pr"));
  [E, KV_TH[2], vK, vD];
}
kv(a) = {
  my(L = if (type(a) == "t_POLMOD", lift(a), a), r = pb_zero);
  if (type(L) != "t_POL", return(pb_c(L)));
  if (variable(L) != b, error("kv: element of K21 expected"));
  forstep (i = poldegree(L), 0, -1, r = pb_add(pb_mul(r, KV_TH), pb_c(polcoef(L, i))));
  r;
}
kvx(P) = { my(v = if (type(P) == "t_POL" && variable(P) != b, Vecrev(P), [P])); vector(#v, i, kv(v[i])); }
\\ known-answer test: valuations of random elements
kv_kat(n) = {
  my(bad = 0);
  for (i = 1, n,
    my(a = nfbasistoalg(nfK, vectorv(21, j, random(2^30) - 2^29) / 2^random(5)) * nfbasistoalg(nfK, pr.gen[2])^random(9), va = nfeltval(nfK, a, pr), ka = kv(a));
    if (!(pb_nz(ka) && pb_vc(ka[1]) == va), bad++));
  bad;
}
