\\ redacted for the release: paths of the development workspace, which is not shipped
\\ td2loc.gp: local images of the 2-descent map of a genus 2 Jacobian at a place of a number field, with an exact
\\ stopping rule, and the Richelot Kummer images derived from them (PARI/GP 2.17). Read richelot.gp first (this file
\\ uses its square class coordinates rich_sqinit / rich_sqcoord, rich_above, rich_f2add and its local model rich_lv_*).
\\
\\ SETTING. K a number field (nfK, maximal at the primes used), C : y^2 = f(x), f in K[x] squarefree of degree 6
\\ (degree 5 is accepted where stated), J = Jac(C), g = 2. A = K[x]/(f) = prod_i K[x]/(g_i) over the irreducible
\\ factors g_i of f; each K[x]/(g_i) is handled as an absolute number field nfG_i (maximal at the given primes).
\\ For a place v of K above p and A_v = A tensor K_v = prod over the primes W of the nfG_i above v of the fields
\\ (nfG_i)_W, the 2-descent (x - T) map is
\\     mu_v : J(K_v)/2J(K_v) -> A_v^x / (K_v^x A_v^x2),   [P1 + P2 - Dinf] -> u(T),  u = (x - x(P1))(x - x(P2)),
\\ well defined because its components against the 2-torsion points are Weil pairings: ((x - th_i)/(x - th_j))(D)
\\ with div((x - th_i)/(x - th_j)) = 2 (W_i - W_j); for a divisor through a Weierstrass point W_i the component at
\\ th_i uses -f'(th_i) u'(th_i) (x - th_i = y^2 / (lc h_i(x)) with f = lc (x - th_i) h_i, so the class of x1 - th_i tends to
\\ that of f'(th_i) as the point (x1, y1) tends to W_i, and u(th_i) = prod_k (th_i - x_k) = -(x1 - th_i) u'(th_i)).
\\
\\ STOPPING RULE (the reason for this file). J(K_v) is a compact p-adic Lie group of dimension g [K_v : Q_p], so
\\ J(K_v) = Z_2^(g [K_v:Q_2]) x (finite) for p = 2 and dim J(K_v)/2J(K_v) = dim J(K_v)[2] + g [K_v : Q_2] [p = 2].
\\ The kernel of mu_v on J(K_v)/2J(K_v) has dimension eps_v in {0, 1}: it is the image of the connecting map of
\\ 0 -> J[2] -> R/mu_2 -> mu_2 -> 0 (R = Res_{A/K} mu_2, the arrow to mu_2 the norm), intersected with the image of
\\ J(K_v); eps_v = 1 iff every factor of f over K_v has even degree, no nontrivial class of K_v^x/K_v^x2 becomes a
\\ square in every factor field (equivalently f is not lc h h^sigma with h a cubic over a quadratic extension), and
\\ Pic^1_C(K_v) is nonempty, which always holds for genus 2 over a p-adic field (Lichtenbaum: the period divides
\\ g - 1). This is the rule of Magma's selmer.m (N. Bruin, "local Cassels kernel").
\\ Hence
\\     dim mu_v(J(K_v)) = D_v := dim J(K_v)[2] + g [K_v : Q_2] [p = 2] - eps_v,
\\ with dim J(K_v)[2] = log2(1 + C(n1, 2) + n2) (n1, n2 the numbers of factors of degree 1 and 2 of f over K_v;
\\ the nonzero 2-torsion points are the classes of pairs of Weierstrass points). A set of K_v-rational divisor
\\ classes whose mu_v values span a space of dimension D_v spans J(K_v)/2J(K_v) modulo ker mu_v; since every map
\\ that factors through J(K_v)/2J(K_v) and kills ker mu_v (for instance the Richelot Kummer maps, which are norms of
\\ components of mu_v) has its image spanned by the images of those classes, this certifies complete local images.
\\
\\ CERTIFIED DIVISORS. Samples are produced in a local model (any heuristic), then checked exactly over K: a monic
\\ u in K[x] of degree 2 (or 1) with distinct roots and a line v in K[x] give a K_v-rational effective divisor of
\\ degree 2 (or 1) on C when f = v^2 (1 + rho) mod u with v(rho(x_i)) > 2 v_v(2) at the roots x_i of u (then 1 + rho
\\ is a square in K_v[x]/(u), so f is a square there: u | f - (v s)^2 for some s). The test uses only exact
\\ arithmetic in K[x]/(u) and valuations at v: v(rho0 + rho1 x_i) >= min(v(rho0), v(rho1) + vmin), vmin the least
\\ root valuation of u from its Newton polygon.
\\
\\ INTERFACE (x is the polynomial variable; K elements are t_POLMOD modulo nfK.pol, or rationals when K = Q)
\\   A  = td2_alg(nfK, f, {facs = 0}, {plist = [2]})   etale algebra: facs = the irreducible factors of f over K
\\                                                      (nffactor when 0); absolute fields maximal at plist
\\   td2_Kimg(A, i, a)                                   image in nfG_i of a in K
\\   td2_uvals(A, u)                                     the components of mu (u(th_i), Weierstrass rule included)
\\   P  = td2_place(A, pr)                               local data at the prime pr of K: primes W, square class
\\                                                      structures, factor degrees, dim J(K_v)[2], eps_v, D_v,
\\                                                      image of K_v^x (a basis of it as columns)
\\   td2_coord(A, P, u)                                  F2 coordinates of mu(u) in A_v^x / A_v^x2
\\   td2_certify(nfK, pr, f, u, v)                       1 if (u, v) certifies a K_v-rational divisor, else 0
\\   S  = td2_span_new(P)                                an empty span modulo the image of K_v^x
\\   td2_span_add(S, c)                                  [S', 1] if the coordinate vector c is new, else [S, 0]
\\   td2_localimage(...)                                 driver: samples, certificates, the stopping rule (below)
\\   P  = td2_smallplace(nfK, f, pr, models)             the same local data without absolute factor fields, when
\\                                                      every factor of f over K_v has degree <= 2 and its field is
\\                                                      K_v(sqrt delta) for a given quadratic extension N = K(sqrt
\\                                                      delta) (models from td2_model_from_field or td2_model); exact
\\                                                      coordinates at certified approximate roots (Newton polygon)
\\   td2_dtree(LV, cv, Qd, sd, kmax)                      exhaustive disc tree for the points of C over K_v or over a
\\                                                      quadratic field of the local model (both charts)
\\   P  = td2_kapplace(F, RR, pr, Dt)                     place of kind "kappa": the samplers and certificates of this
\\                                                      file, screened with the Richelot Kummer map of richelot.gp
\\                                                      (exact: rich_loccoord of rich_kappa; fast: Res(u, G2) in the
\\                                                      local model) towards a known target dimension Dt
\\ SCREENING. td2_localimage first screens candidates with fast coordinates computed in the local model (td2_fastcoord:
\\ one root per factor of degree <= 2, square classes by a digit reduction; td2_kfastcoord for kind "kappa"), then
\\ re-checks the kept divisors with the exact coordinates; completeness always refers to the exact check.
\\ The caller sets default(parisizemax) and default(nbthreads). Tests: td2loc_test.gp (outputs td2loc_test.out and, for
\\ the e = 12 test, td2loc_test_e12.out).

td2_zA = varlower("td2_zA", 'x);

td2_chk(c, msg) = if (!c, error("td2loc: ", msg));

\\ normalised element of K (t_POLMOD modulo nfK.pol, or a rational number when K = Q)
td2_Kelt(nfK, a) =
{
  my(T = nfK.pol);
  if (type(a) == "t_COL", a = nfbasistoalg(nfK, a));
  if (type(a) == "t_POLMOD", a = lift(a));
  if (poldegree(T) == 1, return(if (type(a) == "t_POL", subst(a, variable(T), -polcoef(T, 0) / polcoef(T, 1)), a)));
  Mod(a, T);
}

td2_Kx(nfK, P) = Pol(apply(c -> td2_Kelt(nfK, c), if (type(P) == "t_POL" && variable(P) == 'x, Vec(P), [P])), 'x);

\\ integral scaling of a monic g in K[x]: the least positive integer c with c^n g(X / c) integral
td2_scale(nfK, g) =
{
  my(n = poldegree(g, 'x), c = 1, dn);
  for (i = 0, n - 1,
    dn = denominator(nfalgtobasis(nfK, td2_Kelt(nfK, polcoef(g, i, 'x))));
    \\ c^(n - i) must be divisible by dn: raise c prime by prime
    my(fa = factor(dn));
    for (j = 1, #fa~, my(q = fa[j, 1], need = ceil(fa[j, 2] / (n - i)));
      if (valuation(c, q) < need, c *= q^(need - valuation(c, q)))));
  c;
}

\\ one factor field: g monic irreducible over K; returns [g, nfG, aimg, thimg] with aimg the image of the generator
\\ of K and thimg the image of the root of g in nfG (t_POLMOD in td2_zA)
td2_field(nfK, g, plist) =
{
  my(T = nfK.pol, vK = variable(T), n = poldegree(g, 'x), c, gi, eq, P, al, k, rb, Q, m, aimg, bimg, th, nfG);
  if (poldegree(T) == 1,
    c = td2_scale(nfK, g); gi = c^n * subst(lift(g), 'x, 'x / c);
    P = gi; if (type(P) == "t_POL", P = Pol(apply(z -> if (type(z) == "t_POL", polcoef(z, 0), z), Vec(P)), 'x));
    rb = polredbest(P, 1); Q = subst(rb[1], 'x, td2_zA); m = subst(lift(rb[2]), 'x, Mod(td2_zA, Q));
    aimg = 0; th = m / c
  ,
    \\ rnfequation accepts the non-integral g (flag 1: a root of the absolute equation is beta + k alpha, beta a root
    \\ of g): no integral rescaling, which would inflate the coefficients
    eq = rnfequation(nfK, Pol(apply(z -> if (type(z) == "t_POLMOD", lift(z), z), Vec(g)), 'x), 1); P = eq[1]; al = eq[2]; k = eq[3];
    rb = polredbest(P, 1); Q = subst(rb[1], 'x, td2_zA); m = subst(lift(rb[2]), 'x, Mod(td2_zA, Q));
    aimg = subst(lift(al), 'x, m);
    th = m - k * aimg);
  nfG = nfinit([Q, plist]);
  \\ check: g(th) = 0 in nfG
  my(r = 0, cs = Vec(g)); for (j = 1, #cs, r = r * th + if (poldegree(T) == 1, lift(cs[j]) * Mod(1, Q), subst(lift(cs[j]), vK, aimg)));
  td2_chk(r == 0, "td2_field: the image of the root is not a root");
  [g, nfG, aimg, th];
}

td2_alg(nfK, f, facs = 0, plist = [2]) =
{
  my(A = Map(), fl, lc, fa, flds = List(), prod = 1);
  f = td2_Kx(nfK, f); lc = pollead(f);
  td2_chk(poldegree(f, 'x) == 6 || poldegree(f, 'x) == 5, "deg f must be 5 or 6");
  if (facs == 0,
    fa = if (poldegree(nfK.pol) == 1, factor(lift(f)), nffactor(nfK, lift(f)));
    facs = vector(#fa~, i, td2_chk(fa[i, 2] == 1, "f not squarefree"); fa[i, 1]));
  foreach (facs, g,
    g = td2_Kx(nfK, g); g /= pollead(g); prod *= g;
    listput(flds, td2_field(nfK, g, plist)));
  td2_chk(prod * lc == f, "the factors do not multiply to f");
  mapput(A, "nfK", nfK); mapput(A, "f", f); mapput(A, "lc", lc); mapput(A, "fd", deriv(f, 'x));
  mapput(A, "flds", Vec(flds)); mapput(A, "plist", plist); mapput(A, "pre", td2_pre(nfK, Vec(flds)));
  A;
}

\\ precomputed images in each factor field: the images of the integral basis of K and th, th^2 (t_POLMOD)
td2_pre(nfK, flds) =
{
  vector(#flds, i, my(F = flds[i]);
    [if (poldegree(nfK.pol) == 1, [Mod(1, F[2].pol)], vector(#nfK.zk, j, subst(lift(nfK.zk[j]), variable(nfK.pol), F[3]))), F[4], F[4]^2]);
}

\\ image of a in K in the factor field i (linear combination of the precomputed images of the integral basis)
td2_Kimg(A, i, a) =
{
  my(nfK = mapget(A, "nfK"), Z = mapget(A, "pre")[i][1], c);
  a = td2_Kelt(nfK, a);
  if (poldegree(nfK.pol) == 1, return(a * Z[1]));
  c = nfalgtobasis(nfK, a);
  sum(j = 1, #c, if (c[j], c[j] * Z[j], 0));
}

\\ u(th) in the factor field i for u in K[x] (Horner on the images of the coefficients)
td2_evalu(A, i, u) =
{
  my(pre = mapget(A, "pre")[i], cs = Vecrev(td2_Kx(mapget(A, "nfK"), u)), r = 0, pw = [1, pre[2], pre[3]]);
  for (j = 1, #cs, if (cs[j] != 0, r += td2_Kimg(A, i, cs[j]) * if (j <= 3, pw[j], pre[2]^(j - 1))));
  r;
}

\\ components of mu for the divisor with x-polynomial u (monic in K[x], degree 1 or 2, distinct roots): u(th_i),
\\ or -f'(th_i) u'(th_i) (sign: see the header) when u(th_i) = 0 (the divisor contains the Weierstrass point of th_i, u = its x-polynomial
\\ times a coprime factor)
td2_uvals(A, u) =
{
  my(nf = #mapget(A, "flds"), val);
  vector(nf, i,
    val = td2_evalu(A, i, u);
    if (val == 0,
      val = -td2_evalu(A, i, mapget(A, "fd")) * td2_evalu(A, i, deriv(td2_Kx(mapget(A, "nfK"), u), 'x));
      td2_chk(val != 0, "mu: u is not squarefree at a Weierstrass point"));
    val);
}

\\ ---------------------------------------------------------------- local data
\\ a basis of K_v^x / K_v^x2 by global elements (uniformiser, -1, units 1 + pi^j, 5, then random small elements)
td2_Kvbasis(nfK, pr) =
{
  my(S = rich_sqinit(nfK, pr), want = 1 + #S[4], B = [], V = [], pi = td2_Kelt(nfK, S[2]), cand = List(), r, a, n = poldegree(nfK.pol), tries = 0);
  listput(cand, pi); listput(cand, -1); listput(cand, 5);
  for (j = 1, 2 * pr.e * pr.f + 2, listput(cand, 1 + pi^j));
  foreach (cand, c, if (#B < want, r = rich_f2add(V, rich_sqcoord(nfK, S, c)); if (r[2], V = r[1]; B = concat(B, [c]))));
  while (#B < want,
    tries++; td2_chk(tries < 10^5, "no basis of K_v^x / squares found");
    a = if (n == 1, random(2 * 10^4 + 1) - 10^4, nfbasistoalg(nfK, vectorv(n, i, random(9) - 4)));
    if (a == 0, next);
    r = rich_f2add(V, rich_sqcoord(nfK, S, a)); if (r[2], V = r[1]; B = concat(B, [td2_Kelt(nfK, a)])));
  [B, S];
}

td2_place(A, pr) =
{
  my(P = Map(), nfK = mapget(A, "nfK"), flds = mapget(A, "flds"), Ws = List(), degs = List(), sq = List(), n1 = 0, n2 = 0,
     t2, cnt, alleven = 1, Kb, KM, kerK, eps, D, p = pr.p, g = 2, Nv = 0, Kv);
  for (i = 1, #flds,
    my(nfG = flds[i][2], W = rich_above(nfK, nfG, a -> td2_Kimg(A, i, a), pr));
    td2_chk(sum(j = 1, #W, W[j].e * W[j].f) == poldegree(flds[i][1], 'x) * pr.e * pr.f, "primes above v in a factor field");
    foreach (W, w,
      my(dg = w.e * w.f / (pr.e * pr.f), s = rich_sqinit(nfG, w));
      s = concat(s, [idealpow(nfG, w, if (w.p == 2, 1 + 2 * w.e, 1))]);
      listput(Ws, [i, w]); listput(degs, dg); listput(sq, s); Nv += 1 + #s[4];
      if (dg == 1, n1++); if (dg == 2, n2++); if (dg % 2, alleven = 0)));
  if (poldegree(mapget(A, "f"), 'x) == 5, n1++; alleven = 0);
  cnt = 1 + n1 * (n1 - 1) / 2 + n2; t2 = valuation(cnt, 2); td2_chk(cnt == 2^t2, "#J(K_v)[2] is not a power of 2");
  mapput(P, "pr", pr); mapput(P, "Ws", Vec(Ws)); mapput(P, "degs", Vec(degs)); mapput(P, "sq", Vec(sq)); mapput(P, "N", Nv);
  Kv = td2_Kvbasis(nfK, pr); Kb = Kv[1];
  KM = Mat(vector(#Kb, j, td2_coordvals(A, P, vector(#flds, i, td2_Kimg(A, i, Kb[j])))));
  kerK = #Kb - matrank(Mod(KM, 2));
  eps = alleven && kerK == 0;
  D = t2 + if (p == 2, g * pr.e * pr.f, 0) - eps;
  \\ the quadratic factor fields over K_v, as K_v(sqrt delta) with delta in K: the kernel of K_v^x/K_v^x2 -> M^x/M^x2
  \\ on the coordinate block of a prime of degree 2 is {1, delta}
  my(qf = List(), off = 0);
  for (j = 1, #Ws, my(nb = 1 + #sq[j][4], blk, kk);
    if (degs[j] == 2,
      blk = matrix(nb, #Kb, r, c2, KM[off + r, c2]); kk = matker(Mod(blk, 2));
      td2_chk(#kk == 1, "kernel of K_v^x / squares in a quadratic factor field");
      listput(qf, prod(i = 1, #Kb, Kb[i]^lift(kk[i, 1]))));
    off += nb);
  mapput(P, "qfields", Vec(qf));
  mapput(P, "Kbasis", Kb); mapput(P, "KM", KM); mapput(P, "Ksq", Kv[2]); mapput(P, "kerK", kerK);
  mapput(P, "tors2", t2); mapput(P, "alleven", alleven); mapput(P, "eps", eps); mapput(P, "D", D);
  mapput(P, "name", Str("p = ", p, " (e = ", pr.e, ", f = ", pr.f, "), factor degrees ", Vec(degs)));
  P;
}

\\ square class coordinates at a prime W of nf (S = rich_sqinit(nf, W)): (v_W(a) mod 2, ideallog of a tau^v mod 2) with tau
\\ the anti-uniformiser of W used by nfeltval; a -> (v mod 2, class of a tau^v) is a homomorphism M^x / M^x2 -> F2^(1+dim)
\\ and injective (a = square times tau^(-v)), and it avoids dividing by powers of a uniformiser (slow in degree 84)
td2_sqcoord(nf, S, a) =
{
  my(v, yy, lg, c, dn);
  \\ a times the square of its denominator is integral, so the part yy coprime to W is integral and can be reduced
  \\ modulo W^k (S[5]) before ideallog
  c = nfalgtobasis(nf, a); dn = denominator(c); if (dn != 1, c *= dn^2);
  v = nfeltval(nf, c, S[1], &yy);
  yy = nfeltreduce(nf, yy, S[5]);
  lg = ideallog(nf, yy, S[3]);
  concat([v % 2], vector(#S[4], i, lg[S[4][i]] % 2))~;
}

\\ coordinates of the vector of factor values vals (one element of each nfG_i) in A_v^x / A_v^x2
td2_coordvals(A, P, vals) =
{
  my(Ws = mapget(P, "Ws"), sq = mapget(P, "sq"), flds = mapget(A, "flds"));
  concat(vector(#Ws, j, td2_sqcoord(flds[Ws[j][1]][2], sq[j], vals[Ws[j][1]])));
}

\\ exact coordinates (factor fields, or small models for a place of td2_smallplace; 0 when the latter cannot decide)
td2_coord(A, P, u) = my(kd = if (mapisdefined(P, "kind"), mapget(P, "kind"), "")); if (kd == "small", td2_smcoord(P, u), if (kd == "kappa", td2_kapcoord(P, u), td2_coordvals(A, P, td2_uvals(A, u))));

\\ ---------------------------------------------------------------- spans modulo the image of K_v^x
\\ S = [basis (columns) of span(image of K_v^x, found vectors), number of found dimensions]
td2_span_new(P) =
{
  my(KM = mapget(P, "KM"), B = []);
  for (j = 1, #KM, my(r = rich_f2add(B, KM[, j])); if (r[2], B = r[1]));
  [B, 0];
}

td2_span_add(S, c) =
{
  my(r = rich_f2add(S[1], c));
  if (r[2], [[r[1], S[2] + 1], 1], [S, 0]);
}

\\ ---------------------------------------------------------------- certificates
\\ valuation of a in K at pr (oo for 0)
td2_val(nfK, a, pr) = if (a == 0, oo, nfeltval(nfK, a, pr));

\\ least valuation of the roots of the monic u (degree 1 or 2) at pr, from the Newton polygon
td2_vmin(nfK, pr, u) =
{
  my(n = poldegree(u, 'x), c1, c0);
  if (n == 1, return(td2_val(nfK, polcoef(u, 0, 'x), pr)));
  c1 = td2_val(nfK, polcoef(u, 1, 'x), pr); c0 = td2_val(nfK, polcoef(u, 0, 'x), pr);
  min(c1, if (c0 == oo, oo, c0 / 2));
}

\\ (u, v) certifies a K_v-rational effective divisor on y^2 = f with x-polynomial u: u monic of degree 1 or 2 with
\\ distinct roots, v in K[x] of degree <= 1 with v(x_i) != 0, and rho = (f - v^2) / v^2 mod u small at pr
td2_certify(nfK, pr, f, u, v) =
{
  my(n = poldegree(u, 'x), r, w, s1, s2, nw, winv, rho, bnd = 2 * idealval(nfK, 2, pr), vm);
  u = td2_Kx(nfK, u); v = td2_Kx(nfK, v); f = td2_Kx(nfK, f);
  if (pollead(u) != 1 || n < 1 || n > 2, return(0));
  if (n == 2 && poldisc(u) == 0, return(0));
  r = (f - v^2) % u; w = (v^2) % u;
  if (n == 1,
    w = polcoef(w, 0, 'x); if (w == 0, return(0));
    rho = polcoef(r, 0, 'x) / w;
    return(td2_val(nfK, rho, pr) > bnd));
  s1 = -polcoef(u, 1, 'x); s2 = polcoef(u, 0, 'x);
  my(w0 = polcoef(w, 0, 'x), w1 = polcoef(w, 1, 'x));
  nw = w0^2 + w0 * w1 * s1 + w1^2 * s2;
  if (nw == 0, return(0));
  winv = (w0 + w1 * s1 - w1 * 'x) / nw;
  rho = (r * winv) % u;
  vm = td2_vmin(nfK, pr, u);
  my(r1 = polcoef(rho, 1, 'x));
  min(td2_val(nfK, polcoef(rho, 0, 'x), pr), if (r1 == 0, oo, td2_val(nfK, r1, pr) + vm)) > bnd;
}

\\ ---------------------------------------------------------------- local model and samplers
\\ The samplers run on the local model K_v = Q_p[Y]/(E) of richelot.gp (rich_lv_*; degree one primes only) and
\\ produce candidate divisors [u, v] over K, which td2_certify then checks exactly. Nothing proposed by a sampler is
\\ used without that check.
td2_lvinit(nfK, pr, prec = 120, tgt = 60) =
{
  my(F = Map(), P = Map());
  mapput(F, "nfK", nfK); mapput(F, "d", 1); mapput(P, "pr", pr);
  rich_lv_init(F, P, prec, tgt);
}

\\ the curve in the local model: [f_v, f*_v] with f*(s) = s^6 f(1/s) (points near infinity)
td2_lvcurve(LV, f) =
{
  my(fv = rich_lv_mapx(LV, f));
  [fv, Pol(vector(7, i, polcoef(fv, i - 1, 'x)), 'x)];
}

\\ global lift of a local element of K_v (reduced modulo pr^N)
td2_lift(LV, z, Ib) = rich_lv_lift(LV, rich_lv_unwrap(z), Ib);

\\ local point on the side model sd (1: (x, y); 2: (s, Y) with x = 1/s, y = Y / s^3) -> (x, y) in the same field
td2_toaff(LV, Qd, sd, r, y) =
{
  if (sd == 1, return([r, y]));
  my(ri = if (Qd == 0, rich_lv_inv(LV, r), rich_lv_invQ(LV, Qd, r)));
  [ri, y * ri^3];
}

\\ candidate [u, v] (global, over K) from two points of C over K_v (P1 = [x1, y1], P2 = [x2, y2], x1 != x2)
td2_cand_pair(LV, P1, P2, Ib) =
{
  my(v1, v0, dx = P1[1] - P2[1], dv, s1, s2);
  dv = rich_lv_val(LV, dx); if (!dv[2] || dv[1] == oo, return(0));
  \\ u nearly a square: the lift modulo Ib loses the discriminant and the certificate would fail
  if (mapisdefined(LV, "Nlift") && 4 * dv[1] > mapget(LV, "Nlift"), return(0));
  v1 = (P1[2] - P2[2]) * rich_lv_inv(LV, dx); v0 = P1[2] - v1 * P1[1];
  s1 = P1[1] + P2[1]; s2 = P1[1] * P2[1];
  [x^2 - td2_lift(LV, s1, Ib) * x + td2_lift(LV, s2, Ib), td2_lift(LV, v0, Ib) + td2_lift(LV, v1, Ib) * x];
}

\\ candidate [u, v] from a point [x1, y1] over the quadratic field Qd = K_v(sqrt dl), x1 not in K_v: the divisor
\\ P + P^sigma, u = X^2 - 2 al X + al^2 - dl be^2 (x1 = al + be sqrt dl), v the line through P and P^sigma
td2_cand_quad(LV, Qd, P1, Ib) =
{
  my(xab = rich_lv_ab(Qd, P1[1]), yab = rich_lv_ab(Qd, P1[2]), vb, v1, v0, s1, s2);
  vb = rich_lv_val(LV, xab[2]); if (!vb[2] || vb[1] == oo, return(0));
  if (mapisdefined(LV, "Nlift") && 4 * vb[1] + 2 * rich_lv_val(LV, Qd[1])[1] > mapget(LV, "Nlift"), return(0));
  v1 = yab[2] * rich_lv_inv(LV, xab[2]); v0 = yab[1] - v1 * xab[1];
  s1 = 2 * xab[1]; s2 = xab[1]^2 - Qd[1] * xab[2]^2;
  [x^2 - td2_lift(LV, s1, Ib) * x + td2_lift(LV, s2, Ib), td2_lift(LV, v0, Ib) + td2_lift(LV, v1, Ib) * x];
}

\\ random element of O_v (Qd = 0) or of O_W = O_v[th] (th = th0 + th1 sqrt(dl), rich_lv_quad) with valuation >= m (units of v)
td2_rndloc(LV, Qd, m) =
{
  my(E = mapget(LV, "E"), one = mapget(LV, "one"), a, b);
  a = Mod(rich_lv_rnd(LV, max(m, 0)), E) + one - 1;
  if (m < 0, a *= rich_lv_pipow(LV, m));
  if (Qd == 0, return(a));
  b = Mod(rich_lv_rnd(LV, max(m, 0)), E) + one - 1;
  if (m < 0, b *= rich_lv_pipow(LV, m));
  Mod(a + b * (Qd[4] + Qd[5] * Qd[7]), Qd[7]^2 - Qd[1]);

}

\\ local points of C over K_v (Qd = 0) or over the field Qd with y = y0: the roots of f(x) - y0^2 (sd = 1) or of
\\ f*(s) - y0^2 (sd = 2), as affine points [x, y]
td2_ypoints(LV, cv, Qd, sd, y0) =
{
  my(rts, out = List(), P);
  rts = iferr(rich_lv_roots(LV, Qd, cv[sd] - y0^2), E, []);
  foreach (rts, r,
    if (sd == 2 && rich_lv_vf(LV, Qd, r)[1] == oo, next);
    P = iferr(td2_toaff(LV, Qd, sd, r, y0), E, 0);
    if (P != 0, listput(out, P)));
  Vec(out);
}

\\ a y-value for the samplers: an approximate square root of f(x1) at a random x1 (random depth; then f(x) = y0^2 has a
\\ root near x1 by Hensel's lemma when the approximation is good), or a random element of valuation k (small k: generic
\\ points; large k: points near the Weierstrass points, where y is the local parameter and every small y gives a point)
td2_yvalue(LV, cv, Qd, mode) =
{
  my(e = mapget(LV, "e"), eW = if (Qd == 0, 1, Qd[3]), sd = 1 + random(2), x1, z, ap, k);
  if (mode == 0,
    x1 = td2_rndloc(LV, Qd, if (random(2), 0, random(2 * e + 1)) - if (random(3) == 0, random(e + 1), 0));
    z = subst(cv[sd], 'x, x1);
    ap = iferr(rich_lv_approxsqrt(LV, Qd, z), E, 0);
    if (ap != 0 && ap != [], return([sd, ap[1]])));
  k = if (mode == 2, random(6 * e + 1), random(2 * e + 1) - e);
  [sd, td2_rndloc(LV, Qd, k)];
}

\\ ---------------------------------------------------------------- fast local coordinates (screening only)
\\ The exact coordinates (td2_coord) cost ideallog in the factor fields (degree 84 over K21: about 0.1 s per prime).
\\ For the screening of candidates, td2_localimage uses the same coordinates computed in the local model instead: for
\\ each factor of f over K_v of degree 1 or 2, a root t in K_v or in M = K_v(sqrt dl) (the field of that factor), and
\\ the square class of u(t) by a digit reduction. The kept divisors are then checked with the exact coordinates, so
\\ nothing below needs to be rigorous: an error could only delay completion (the exact check fails and the run
\\ goes on with exact coordinates).
\\
\\ square class coordinates in K_v (Qd = 0) or in the quadratic field M = Qd = K_v(sqrt dl) (rich_lv_quad, field case),
\\ a homomorphism M^x / M^x2 -> F2^(2 + [M : Q_2]). Elements of M are pairs [a, b] = a + b th on the integral basis
\\ (1, th) of O_W = O_v[th], th^2 + q1 th + q0 = 0 (th a uniformiser when M/K_v is ramified, a lift of a root of
\\ Y^2 + Y + 1 when unramified); uni = th (ramified) or pi. Digit reduction: z = uni^v u; u times a residue square is
\\ 1 mod W; at the level j = v_W(u - 1) with digit c (residue of (u - 1) / uni^j): j odd < 2 v_W(2): the F2
\\ coordinates of c are recorded and u is multiplied by the basis units 1 + uni^j, 1 + th uni^j (unramified case) of
\\ its digits; j even < 2 v_W(2): u times (1 + s uni^(j/2))^2 with s^2 = c; j = 2 v_W(2): the digit is in the image of
\\ s -> s^2 + s (the residue of 2 / uni^(v_W(2)) is 1) iff it lies in F2 (then u times (1 + th uni^(v_W(2)))^2), and
\\ otherwise one bit and u times 1 + th uni^(2 v_W(2)) (1 + uni^(2 v_W(2)) when the residue field is F2); j > 2 v_W(2):
\\ u is a square. Each basis unit is used at most once (the level increases), so the bits are the coordinates of z in
\\ the basis {uni, 1 + b uni^j (j odd < 2 v_W(2)), the unit of level 2 v_W(2)}. The unit u is truncated to O(2^10)
\\ first: its class depends on u mod W^(2 v_W(2) + 1) only, and the loop divides by at most uni^(2 v_W(2)) (two
\\ 2-adic digits), so the loop runs at low precision.
\\ SP = td2_lvq_prep(LV, Qd): [Qd, eW, fW, v2, q0, q1, th0, 1/th1, unipow, unineg, sigma th]
td2_lvq_prep(LV, Qd) =
{
  my(e = mapget(LV, "e"), eW, fW, v2, th0, th1, q1 = 0, q0 = 0, i1 = 0, iq0, up, un, sth = 0, kd = 10);
  if (Qd == 0,
    eW = 1; fW = 1; v2 = e;
    up = vector(2 * v2 + 1, j, [td2_lvtr(LV, rich_lv_pipow(LV, j - 1), kd + 4), 0]);
    un = vector(2 * v2 + 1, j, [td2_lvtr(LV, rich_lv_pipow(LV, 1 - j), kd + 4), 0]);
    return([0, eW, fW, v2, 0, 0, 0, 0, up, un, 0]));
  eW = Qd[3]; fW = Qd[2]; v2 = eW * e; th0 = Qd[4]; th1 = Qd[5];
  q1 = -2 * th0; q0 = th0^2 - th1^2 * Qd[1]; i1 = rich_lv_inv(LV, th1);
  if (eW == 2,
    td2_chk(rich_lv_val(LV, q0)[1] == 1, "td2_lvq_prep: th is not a uniformiser");
    iq0 = rich_lv_inv(LV, q0); sth = [-q1, -1];
    \\ th^j and th^(-j) = (sigma th)^j / q0^j
    up = vector(2 * v2 + 1); up[1] = [1, 0]; for (j = 2, #up, up[j] = td2_lvq_mul0(q0, q1, up[j - 1], [0, 1]));
    un = vector(2 * v2 + 1); un[1] = [1, 0]; for (j = 2, #un, un[j] = td2_lvq_mul0(q0, q1, un[j - 1], [-q1 * iq0, -iq0]))
  ,
    up = vector(2 * v2 + 1, j, [rich_lv_pipow(LV, j - 1), 0]);
    un = vector(2 * v2 + 1, j, [rich_lv_pipow(LV, 1 - j), 0]));
  up = apply(g -> [td2_lvtr(LV, g[1], kd + 4), td2_lvtr(LV, g[2], kd + 4)], up);
  un = apply(g -> [td2_lvtr(LV, g[1], kd + 4), td2_lvtr(LV, g[2], kd + 4)], un);
  [Qd, eW, fW, v2, td2_lvtr(LV, q0, kd + 4), td2_lvtr(LV, q1, kd + 4), th0, i1, up, un, sth];
}

\\ element of K_v truncated to absolute precision O(2^k) on the basis 1, Y, ..., Y^(e-1)
td2_lvtr(LV, z, k) =
{
  my(E = mapget(LV, "E"), l);
  z = rich_lv_unwrap(z);
  l = lift(if (type(z) == "t_POLMOD", z, Mod(z, E)));
  if (type(l) != "t_POL", return(Mod(l + O(2^k), E)));
  Mod(apply(c -> c + O(2^k), l), E);
}

td2_lvq_mul0(q0, q1, g, h) = my(bd = g[2] * h[2]); [g[1] * h[1] - bd * q0, g[1] * h[2] + g[2] * h[1] - bd * q1];
td2_lvq_mul(SP, g, h) = td2_lvq_mul0(SP[5], SP[6], g, h);

\\ valuation v_W of the pair g: [v, exact] (exact = 0: a lower bound, g = 0 to precision)
td2_lvq_val(LV, SP, g) =
{
  my(va = rich_lv_val(LV, g[1]), vb = if (g[2] == 0 && type(g[2]) != "t_POLMOD", [oo, 1], rich_lv_val(LV, g[2])), ve = oo, vi = oo);
  if (SP[2] == 2, if (va[1] < oo, va[1] *= 2); if (vb[1] < oo, vb[1] = 2 * vb[1] + 1));
  foreach ([va, vb], t, if (t[2], ve = min(ve, t[1]), vi = min(vi, t[1])));
  if (ve < vi, [ve, 1], [vi, 0]);
}

\\ the pair of an element z of M (as returned by the local model: t_POLMOD in Qd[7], or an element of K_v)
td2_lvq_pair(SP, z) =
{
  my(ab, bb);
  if (SP[1] == 0, return([rich_lv_unwrap(z), 0]));
  ab = rich_lv_ab(SP[1], z); bb = ab[2] * SP[8];
  [ab[1] - bb * SP[7], bb];
}

\\ coordinates of z (element of K_v or of M) as a row vector, or 0 when the precision does not decide
td2_lvq_sqcoord(LV, SP, z) =
{
  my(e = mapget(LV, "e"), eW = SP[2], fW = SP[3], v2 = SP[4], g, vz, u, c, w, t, j, bits, idx, s, one = [1, 0], th = [0, 1], d, n);
  g = td2_lvq_pair(SP, z);
  vz = td2_lvq_val(LV, SP, g); if (!vz[2] || vz[1] == oo, return(0));
  \\ u = z uni^(-v), at full precision
  n = vz[1];
  if (eW == 1,
    u = [g[1] * rich_lv_pipow(LV, -n), g[2] * rich_lv_pipow(LV, -n)]
  ,
    my(q0 = SP[1][4]^2 - SP[1][5]^2 * SP[1][1], pw = one, bs = if (n >= 0, SP[11], th), m = abs(n));
    \\ z th^(-n) = z (sigma th)^n / q0^n for n >= 0, z th^(-n) for n < 0
    while (m, if (m % 2, pw = td2_lvq_mul0(q0, -2 * SP[7], pw, bs)); bs = td2_lvq_mul0(q0, -2 * SP[7], bs, bs); m \= 2);
    u = td2_lvq_mul0(q0, -2 * SP[7], g, pw);
    if (n > 0, my(iq = rich_lv_inv(LV, q0)^n); u = [u[1] * iq, u[2] * iq]));
  u = [td2_lvtr(LV, u[1], 10), td2_lvtr(LV, u[2], 10)];
  if (fW == 2, c = [rich_lv_res(LV, u[1]), rich_lv_res(LV, u[2])]; w = [c[1], c[2]]; u = td2_lvq_mul(SP, u, td2_lvq_mul(SP, w, w)));
  bits = vector(fW * v2 + 1);
  for (it = 1, 4 * v2 + 8,
    d = [u[1] - 1, u[2]];
    t = td2_lvq_val(LV, SP, d); j = t[1];
    if (j >= 2 * v2 + 1, return(concat([n % 2], bits)));
    if (!t[2], return(0));
    d = td2_lvq_mul(SP, d, SP[10][j + 1]);
    c = [rich_lv_res(LV, d[1]), if (fW == 2, rich_lv_res(LV, d[2]), 0)];
    if (j % 2,
      idx = fW * (j - 1) / 2;
      if (c[1], bits[idx + 1] = 1; u = td2_lvq_mul(SP, u, one + SP[9][j + 1]));
      if (c[2], bits[idx + 2] = 1; u = td2_lvq_mul(SP, u, one + td2_lvq_mul(SP, th, SP[9][j + 1])));
      next);
    if (j < 2 * v2,
      \\ s^2 = c in F_4 = F_2[th], th^2 = th + 1: (c0 + c1 th)^2 = (c0 + c1) + c1 th
      s = if (fW == 1, one, [(c[1] + c[2]) % 2, c[2]]);
      w = one + td2_lvq_mul(SP, s, SP[9][j / 2 + 1]); u = td2_lvq_mul(SP, u, td2_lvq_mul(SP, w, w)); next);
    if (fW == 1, bits[fW * v2 + 1] = 1; u = td2_lvq_mul(SP, u, one + SP[9][2 * v2 + 1]); next);
    if (c[2], bits[fW * v2 + 1] = 1; u = td2_lvq_mul(SP, u, one + td2_lvq_mul(SP, th, SP[9][2 * v2 + 1])); next);
    w = one + td2_lvq_mul(SP, th, SP[9][v2 + 1]); u = td2_lvq_mul(SP, u, td2_lvq_mul(SP, w, w)));
  0;
}

\\ square class coordinates of the element z of K_v (Qd = 0) or of the field Qd, as a column (0 when undecided)
td2_lv_sqc(LV, Qd, z) = td2_lv_sqc2(LV, td2_lvq_prep(LV, Qd), z);
td2_lv_sqc2(LV, SP, z) = my(c = td2_lvq_sqcoord(LV, SP, z)); if (type(c) == "t_INT", 0, c~);

\\ fast coordinate data at the place P: one root t per factor of f over K_v (degrees 1 and 2 only; 0 otherwise):
\\ Map with "LV", "reps" ([Qd, t] per factor), "KM" (the image of the basis of K_v^x / squares, columns)
td2_fastinit(A, P, LV) =
{
  my(out, FC = Map(), KM, Kb);
  if (mapisdefined(P, "kind") && mapget(P, "kind") == "kappa",
    if (!mapisdefined(P, "kfast"), return(0));
    mapput(FC, "kind", "kappa"); mapput(FC, "LV", mapget(P, "LV")); mapput(FC, "kfast", mapget(P, "kfast"));
    mapput(FC, "KM", matrix(mapget(P, "N"), 0)); mapput(FC, "reps", mapget(P, "kreps"));
    return(FC));
  if (vecmax(mapget(P, "degs")) > 2, return(0));
  \\ a small model place carries its local roots
  if (mapisdefined(P, "fastreps"), out = mapget(P, "fastreps"); LV = mapget(P, "LV"), out = td2_fastroots(A, P, LV));
  if (type(out) == "t_INT", return(0));
  Kb = mapget(P, "Kbasis");
  my(sps = vector(#out, i, td2_lvq_prep(LV, out[i][1])));
  KM = Mat(vector(#Kb, j, my(bv = rich_lv_map(LV, Kb[j]), col = []);
    for (i = 1, #out, my(c = td2_lv_sqc2(LV, sps[i], bv)); if (type(c) == "t_INT", return(0)); col = concat(col, c)); col));
  mapput(FC, "LV", LV); mapput(FC, "reps", Vec(out)); mapput(FC, "KM", KM); mapput(FC, "sps", sps);
  FC;
}

\\ one local root per factor of f over K_v (from the degrees and the fields of the factor fields at P), or 0
td2_fastroots(A, P, LV) =
{
  my(degs = mapget(P, "degs"), qf = mapget(P, "qfields"), fv, out = List(), cls = List(), n1, n2);
  fv = rich_lv_mapx(LV, mapget(A, "f"));
  n1 = #[d | d <- degs, d == 1]; n2 = #[d | d <- degs, d == 2];
  if (n1,
    my(rts = iferr(rich_lv_roots(LV, 0, fv, -1, 4000), E, []));
    if (#rts != n1, return(0));
    foreach (rts, r, listput(out, [0, r])));
  \\ the quadratic factors, grouped by the class of their field: the roots in K_v(sqrt dl) outside K_v, one per
  \\ conjugate pair
  foreach (qf, dl,
    my(dv = rich_lv_map(LV, dl), cd = rich_lv_sqcoord(LV, dv), Qd, rts, kept = List(), nw);
    if (cd == 0, return(0));
    if (setsearch(Set(cls), cd), next);
    listput(cls, cd);
    nw = #[q | q <- qf, rich_lv_sqcoord(LV, rich_lv_map(LV, q)) == cd];
    Qd = rich_lv_quad(LV, dv);
    rts = iferr(rich_lv_roots(LV, Qd, fv, -1, 4000), E, []);
    foreach (rts, r, my(ab = rich_lv_ab(Qd, r), vb = rich_lv_val(LV, ab[2]), dup = 0);
      if (!vb[2] || vb[1] == oo, next);
      foreach (kept, k2, my(ab2 = rich_lv_ab(Qd, k2)); if (rich_lv_val(LV, ab2[1] - ab[1])[1] > 20 * mapget(LV, "e") &&
          (rich_lv_val(LV, ab2[2] - ab[2])[1] > 20 * mapget(LV, "e") || rich_lv_val(LV, ab2[2] + ab[2])[1] > 20 * mapget(LV, "e")), dup = 1));
      if (!dup, listput(kept, r)));
    if (#kept != nw, return(0));
    foreach (kept, r, listput(out, [Qd, r])));
  if (#out != n1 + n2, return(0));
  Vec(out);
}

\\ fast coordinates of the divisor with x-polynomial u (in K[x]), or 0 when undecided
td2_fastcoord(FC, u) =
{
  if (mapisdefined(FC, "kind"), return(td2_kfastcoord(FC, u)));
  my(LV = mapget(FC, "LV"), uv = rich_lv_mapx(LV, u), col = [], c, reps = mapget(FC, "reps"), sps = mapget(FC, "sps"));
  for (i = 1, #reps, my(R = reps[i]);
    c = td2_lv_sqc2(LV, sps[i], subst(uv, 'x, R[2]));
    if (type(c) == "t_INT", return(0));
    col = concat(col, c));
  col;
}

\\ Res(x^2 + a1 x + a0, g2 x^2 + g1 x + g0) (checked against polresultant in td2loc_test.gp)
td2_kres(a0, a1, g0, g1, g2) = g2^2 * a0^2 - g2 * g1 * a1 * a0 + g2 * g0 * a1^2 - 2 * g2 * g0 * a0 + g1^2 * a0 - g1 * g0 * a1 + g0^2;

\\ fast coordinates of kappa(u) = Res(u, G2) (u monic of degree 2) in L_v^x / squares, or 0 when undecided
td2_kfastcoord(FC, u) =
{
  my(LV = mapget(FC, "LV"), kf = mapget(FC, "kfast"), uv, a0, a1, g0, g1, g2, r, c);
  if (poldegree(u, 'x) != 2, return(0));
  uv = rich_lv_mapx(LV, u / pollead(u)); a0 = polcoef(uv, 0, 'x); a1 = polcoef(uv, 1, 'x);
  g0 = kf[2][1]; g1 = kf[2][2]; g2 = kf[2][3];
  r = td2_kres(a0, a1, g0, g1, g2);
  c = td2_lv_sqc2(LV, kf[3], r);
  if (type(c) == "t_INT", 0, c);
}

\\ an empty span over the fast coordinates (modulo the image of K_v^x)
td2_fastspan_new(FC) =
{
  my(KM = mapget(FC, "KM"), B = []);
  for (j = 1, #KM, my(r = rich_f2add(B, KM[, j])); if (r[2], B = r[1]));
  [B, 0];
}

\\ a random nontrivial class of K_v^x / squares (p = 2, f = 1), uniform over the conductor: the unramified class
\\ 1 + pi^(2e) u, a class 1 + pi^j u of odd level j < 2e (discriminant exponent 2e - j + 1), or pi u (u random units).
\\ A random unit has level 1 with probability 1/2, so the naive choice almost never gives the unramified extension or
\\ the ramified ones of small discriminant, whose points reach the classes of J(K_v) that reduce to points over F_4
\\ (conjugate pairs of F_4-points of the special fibre) and to components of the Neron special fibre.
td2_rnddelta(LV) =
{
  my(e = mapget(LV, "e"), r = random(e + 2), u = 1 + mapget(LV, "Y") * td2_rndloc(LV, 0, 0));
  if (r == 0, return(mapget(LV, "Y") * u));
  if (r == 1, return(1 + rich_lv_pipow(LV, 2 * e) * u));
  1 + rich_lv_pipow(LV, 2 * (r - 2) + 1) * u;
}

\\ ---------------------------------------------------------------- small global models (no absolute factor fields)
\\ When every factor of f over K_v has degree 1 or 2 and each quadratic factor has its field K_v(sqrt delta) for delta
\\ in a given list of quadratic extensions N = K(sqrt delta) (models [delta, nfN, aimg, s]: aimg the image in N of the
\\ generator of K, s in N with s^2 = delta), the components of mu are computed exactly without the absolute factor
\\ fields (which have degree 4 [K : Q] for a quartic factor of f over K): at a global approximation t (in K, or in N)
\\ of one root theta of each factor over K_v, certified by the Newton polygon of g(z) = f(t + z) = sum c_k z^k over
\\ N_w (no integrality needed): if r := v(c_0) - v(c_1) > rho := max_{k >= 2} (v(c_1) - v(c_k)) / (k - 1), then (1, v(c_1))
\\ is a vertex, f has exactly one root theta with v(theta - t) > rho, and v(theta - t) = r; every other root theta'
\\ has v(theta' - t) <= rho.
\\  - same root: t' approximating theta' (v(theta' - t') = r' > rho) with v(t' - t) > rho gives v(theta' - t) > rho,
\\    so theta' = theta;
\\  - distinct roots: v(t' - t) < min(r, r') gives v(theta' - t) = v(t' - t) < r = v(theta - t): theta' != theta;
\\  - theta not in K_v (t in N): sigma theta is the root with v(sigma theta - sigma t) = r (sigma the conjugation of N_w
\\    over K_v, which preserves v_w since w is the only prime of N above pr), so v(t - sigma t) < r gives
\\    v(sigma theta - t) = v(t - sigma t) < r: theta != sigma theta.
\\ With the models' classes delta pairwise distinct and nontrivial in K_v^x / squares (checked), roots in different
\\ models are different, so once deg f distinct roots are accounted for (roots in K_v, and pairs theta, sigma theta),
\\ the factorisation type of f over K_v is certified: the linear factors, and one quadratic factor with field N_w for
\\ each pair. Components: for u in K[x] monic of degree <= 2, u(theta) - u(t) = (theta - t)(theta + t + u1) (degree
\\ 2; theta - t in degree 1) has valuation >= r + min(v(2t + u1), r) (resp. r), so u(theta) / u(t) = 1 + eps with
\\ v(eps) >= 2 v_w(2) + 1, a square in N_w, as soon as v(u(t)) + 2 v_w(2) + 1 <= that bound (td2_smcoord checks it and
\\ returns 0 otherwise). Only p = 2 with f(pr) = 1 and [K : Q] > 1.

td2_sqinit(nf, w) = concat(rich_sqinit(nf, w), [idealpow(nf, w, if (w.p == 2, 1 + 2 * w.e, 1))]);

\\ a model [delta, nfN, aimg, s] from a quadratic factor field of td2_field ([g, nfG, aimg, th], g = x^2 + g1 x + g0):
\\ delta = g1^2 - 4 g0 and s = 2 th + g1
td2_model_from_field(nfK, fl) =
{
  my(g = td2_Kx(nfK, fl[1]), g1 = polcoef(g, 1, 'x), g0 = polcoef(g, 0, 'x), zk);
  td2_chk(poldegree(g, 'x) == 2 && pollead(g) == 1, "td2_model_from_field: monic quadratic expected");
  zk = td2_zkimg(nfK, fl[3], fl[2].pol);
  [g1^2 - 4 * g0, fl[2], fl[3], 2 * fl[4] + td2_mimg0(nfK, zk, g1), zk];
}

\\ a model from a quadratic extension N of K given by nfN, the image aimg of the generator of K and s = sqrt(delta)
td2_model(nfK, delta, nfN, aimg, s) =
{
  my(zk = td2_zkimg(nfK, aimg, nfN.pol));
  td2_chk(s^2 == td2_mimg0(nfK, zk, delta), "td2_model: s^2 != delta");
  [td2_Kelt(nfK, delta), nfN, aimg, s, zk];
}

\\ images of the integral basis of K in N (the generator of K maps to aimg)
td2_zkimg(nfK, aimg, Npol) = vector(#nfK.zk, j, subst(lift(nfK.zk[j]), variable(nfK.pol), aimg) * Mod(1, Npol));
td2_mimg0(nfK, zk, a) = { my(c = nfalgtobasis(nfK, td2_Kelt(nfK, a))); sum(j = 1, #c, if (c[j], c[j] * zk[j], 0)); }
\\ g(t) for g in K[x] and t in N (Horner on the images of the coefficients)
td2_meval(nfK, zk, g, t) = { my(cs = Vec(td2_Kx(nfK, g)), r = 0); for (j = 1, #cs, r = r * t + td2_mimg0(nfK, zk, cs[j])); r; }
td2_nval(nf, a, w) = if (a == 0, oo, nfeltval(nf, a, w));

\\ Newton polygon data of the root near t (in the model m: nfN = m[2], images zk = m[5]) at the prime w: [r, rho] or 0
td2_hensel(nfK, m, w, f, fd, t) =
{
  my(fN = Pol(vector(poldegree(f, 'x) + 1, i, td2_mimg0(nfK, m[5], polcoef(f, poldegree(f, 'x) + 1 - i, 'x))), 'x), g, vs, r, rho = -oo);
  g = subst(fN, 'x, 'x + t);
  vs = vector(poldegree(g, 'x) + 1, i, td2_nval(m[2], polcoef(g, i - 1, 'x), w));
  if (vs[2] == oo, return(0));
  for (k = 2, #vs - 1, if (vs[k + 1] < oo, rho = max(rho, (vs[2] - vs[k + 1]) / (k - 1))));
  r = if (vs[1] == oo, oo, vs[1] - vs[2]);
  if (r <= rho, return(0));
  [r, rho];
}

\\ the small model place: local data as td2_place, with "kind" = "small" and per factor over K_v the data
\\ [m, w, sq, t, r, rho, Qd, rloc] (m the model, K itself for a root in K_v; rloc the local root, Qd its field or 0)
td2_smallplace(nfK, f, pr, models, Nlift = 0) =
{
  my(P = Map(), LV, fv, fd, e = pr.e, Ib, n, reps = List(), degs = List(), qf = List(), m0, sqK, n1 = 0, n2 = 0, Nv = 0,
     rts, T, cls = List(), cnt, t2, alleven = 1, Kv, Kb, KM, kerK, eps, D, fast = List());
  td2_chk(pr.p == 2 && pr.f == 1, "td2_smallplace: p = 2 and f(pr) = 1 only");
  td2_chk(poldegree(nfK.pol) > 1, "td2_smallplace: [K : Q] > 1 only");
  f = td2_Kx(nfK, f); fd = deriv(f, 'x); n = poldegree(f, 'x);
  if (Nlift == 0, Nlift = 16 * e + 40);
  LV = td2_lvinit(nfK, pr); fv = rich_lv_mapx(LV, f); Ib = idealpow(nfK, pr, Nlift);
  m0 = [1, nfK, Mod(variable(nfK.pol), nfK.pol), 1, td2_zkimg(nfK, Mod(variable(nfK.pol), nfK.pol), nfK.pol)];
  sqK = td2_sqinit(nfK, pr);
  \\ roots in K_v
  rts = iferr(rich_lv_roots(LV, 0, fv, -1, 4000), E, []); T = List();
  foreach (rts, r0, my(t = td2_lift(LV, r0, Ib), h = td2_hensel(nfK, m0, pr, f, fd, t), st = 1);
    if (h == 0, next);
    foreach (T, o, my(a = td2_nval(nfK, t - o[1], pr));
      if (a > h[2] && o[2] > h[2], st = 0, if (!(a < min(h[1], o[2])), st = -1)));
    td2_chk(st >= 0, "td2_smallplace: ambiguous roots in K_v");
    if (st, listput(T, [t, h[1], h[2], r0])));
  foreach (T, o, listput(reps, [m0, pr, sqK, o[1], o[2], o[3], 0, o[4]]); listput(degs, 1); n1++;
                 listput(fast, [0, o[4]]));
  \\ quadratic factors, model by model
  foreach (models, m,
    my(cd = rich_sqcoord(nfK, sqK, m[1]), Ws, w, Qd, kept = List(), mimgpr);
    if (cd == 0, next);
    \\ a second model of the same local field adds nothing (its roots are found in the first one)
    if (setsearch(Set(cls), cd), next);
    listput(cls, cd);
    mimgpr = td2_mimg0(nfK, m[5], nfbasistoalg(nfK, pr.gen[2]));
    Ws = [W | W <- idealprimedec(m[2], 2), idealval(m[2], idealadd(m[2], 2, mimgpr), W) > 0];
    td2_chk(#Ws == 1 && Ws[1].e * Ws[1].f == 2 * pr.e, "td2_smallplace: primes of a model above pr");
    w = Ws[1];
    Qd = rich_lv_quad(LV, rich_lv_map(LV, m[1]));
    td2_chk(Qd[6] == 0, "td2_smallplace: delta is a square in the local model");
    rts = iferr(rich_lv_roots(LV, Qd, fv, -1, 4000), E, []);
    foreach (rts, r0, my(ab = rich_lv_ab(Qd, r0), vb = rich_lv_val(LV, ab[2]), ag, bg, t, ts, h, a, st = 1);
      if (!vb[2] || vb[1] == oo, next);
      ag = td2_mimg0(nfK, m[5], td2_lift(LV, ab[1], Ib)); bg = td2_mimg0(nfK, m[5], td2_lift(LV, ab[2], Ib));
      t = ag + bg * m[4]; ts = ag - bg * m[4];
      h = td2_hensel(nfK, m, w, f, fd, t); if (h == 0, next);
      a = td2_nval(m[2], t - ts, w);
      if (!(a < h[1]), next);
      foreach (kept, o, foreach ([o[1], o[5]], oo2, my(a2 = td2_nval(m[2], t - oo2, w));
        if (a2 > h[2] && o[2] > h[2], st = 0, if (st && !(a2 < min(h[1], o[2])), st = -1))));
      td2_chk(st >= 0, "td2_smallplace: ambiguous roots in a model");
      if (st, listput(kept, [t, h[1], h[2], r0, ts])));
    foreach (kept, o, listput(reps, [m, w, td2_sqinit(m[2], w), o[1], o[2], o[3], Qd, o[4]]); listput(degs, 2); n2++;
                      listput(qf, m[1]); listput(fast, [Qd, o[4]])));
  cnt = n1 + 2 * n2;
  if (cnt != n, return(0));
  if (n == 5, n1++; alleven = 0);
  if (n1, alleven = 0);
  cnt = 1 + n1 * (n1 - 1) / 2 + n2; t2 = valuation(cnt, 2); td2_chk(cnt == 2^t2, "#J(K_v)[2] is not a power of 2");
  foreach (reps, R, Nv += 1 + #R[3][4]);
  mapput(P, "kind", "small"); mapput(P, "nfK", nfK); mapput(P, "pr", pr); mapput(P, "reps", Vec(reps)); mapput(P, "degs", Vec(degs));
  mapput(P, "N", Nv); mapput(P, "LV", LV); mapput(P, "fastreps", Vec(fast)); mapput(P, "qfields", Vec(qf));
  Kv = td2_Kvbasis(nfK, pr); Kb = Kv[1];
  KM = Mat(vector(#Kb, j, concat(vector(#reps, i, my(R = reps[i]); td2_sqcoord(R[1][2], R[3], td2_mimg0(nfK, R[1][5], Kb[j]))))));
  kerK = #Kb - matrank(Mod(KM, 2));
  eps = alleven && kerK == 0;
  D = t2 + 2 * pr.e * pr.f - eps;
  mapput(P, "Kbasis", Kb); mapput(P, "KM", KM); mapput(P, "Ksq", Kv[2]); mapput(P, "kerK", kerK);
  mapput(P, "tors2", t2); mapput(P, "alleven", alleven); mapput(P, "eps", eps); mapput(P, "D", D);
  mapput(P, "name", Str("p = 2 (e = ", pr.e, ", f = ", pr.f, "), factor degrees ", Vec(degs), " (small models)"));
  P;
}

\\ exact coordinates of the divisor with x-polynomial u at a small model place (0 when the precision check fails)
td2_smcoord(P, u) =
{
  my(nfK = mapget(P, "nfK"), col = [], z, vz, bnd, u1, nfN, t, w);
  u = td2_Kx(nfK, u);
  u1 = if (poldegree(u, 'x) == 2, polcoef(u, 1, 'x), 0);
  foreach (mapget(P, "reps"), R,
    nfN = R[1][2]; w = R[2]; t = R[4];
    z = td2_meval(nfK, R[1][5], u, t);
    vz = td2_nval(nfN, z, w); if (vz == oo, return(0));
    bnd = if (poldegree(u, 'x) == 2, R[5] + min(td2_nval(nfN, 2 * t + td2_mimg0(nfK, R[1][5], u1), w), R[5]), R[5]);
    if (vz + 1 + 2 * w.e > bnd, return(0));
    col = concat(col, td2_sqcoord(nfN, R[3], z)));
  col;
}

\\ ---------------------------------------------------------------- Richelot images directly (a known target dimension)
\\ When the 2-descent coordinates are out of reach on one side (a factor of degree 4 over K_v whose absolute field is
\\ too large, as on the Richelot dual at the places above 2 of K21), the same samplers and certificates can screen with
\\ the exact coordinates of the Richelot Kummer map itself: td2_kapplace(F, RR, pr, Dt) is a place Map of kind "kappa"
\\ whose coordinates are rich_loccoord(F, rich_place(F, pr), rich_kappa(F, RR, u)) (resultants over L and ideallog in
\\ L: exact) and whose target is Dt. Used with Dt = N_v - dim Im_v(kappa) of the other side (known exactly from its
\\ complete 2-descent image): the local Tate pairing makes Im kappa and Im kappa' exact annihilators, so their
\\ dimensions add up to N_v, and a span of dimension Dt certifies the image (the span is a lower bound, every kept
\\ divisor being certified). No quotient by K_v^x here (kappa is defined on J(K_v)); the fast screening uses Res(u, G2) in
\\ the local model (td2_kfastcoord; closed formula in the coefficients of u and G2, checked against polresultant).
td2_kapplace(F, RR, pr, Dt, qf = []) =
{
  my(P = Map(), Pr = rich_place(F, pr), nfK = mapget(F, "nfK"), LV, QL, G1l, rts);
  LV = td2_lvinit(nfK, pr); mapput(P, "LV", LV);
  \\ fast screening: Res(u, G2) in L_v = K_v(sqrt d) of the local model (G2 = A + sqrt(d) B), square classes by the
  \\ digit reduction; generator 7 samples near the roots of G1 in L_v
  QL = rich_lv_quad(LV, rich_lv_map(LV, mapget(F, "d")));
  if (QL[6] == 0,
    my(Al = rich_lv_mapx(LV, td2_Kx(nfK, mapget(RR, "A"))), Bl = rich_lv_mapx(LV, td2_Kx(nfK, mapget(RR, "B"))));
    mapput(P, "kfast", [QL, vector(3, i, Mod(polcoef(Al, i - 1, 'x) + polcoef(Bl, i - 1, 'x) * QL[7], QL[7]^2 - QL[1])), td2_lvq_prep(LV, QL)]);
    G1l = rich_lv_mapx(LV, td2_Kx(nfK, mapget(RR, "G1")));
    rts = iferr(rich_lv_roots(LV, QL, G1l, -1, 4000), E, []);
    mapput(P, "kreps", [[QL, r] | r <- rts]));
  mapput(P, "kind", "kappa"); mapput(P, "F", F); mapput(P, "RR", RR); mapput(P, "Prich", Pr); mapput(P, "pr", pr);
  mapput(P, "N", mapget(Pr, "N")); mapput(P, "D", Dt); mapput(P, "KM", matrix(mapget(Pr, "N"), 0)); mapput(P, "Kbasis", []);
  mapput(P, "degs", [4]); mapput(P, "qfields", qf);
  mapput(P, "name", Str("kappa image at p = ", pr.p, " (e = ", pr.e, ", f = ", pr.f, "), target ", Dt, " of ", mapget(Pr, "N")));
  P;
}
td2_kapcoord(P, u) = rich_loccoord(mapget(P, "F"), mapget(P, "Prich"), rich_kappa(mapget(P, "F"), mapget(P, "RR"), u));

\\ ---------------------------------------------------------------- disc trees (exhaustive local points)
\\ The random samplers find a point near a random x through an approximate square root of f(x) and Hensel's lemma;
\\ inside deep clusters of roots the margin |f'(x)|^2 / |f(x)| is small and the success rate falls like 2^(-m/2) at
\\ depth m, so whole classes of J(K_v)/2J(K_v) can stay out of reach (seen at e = 12). The disc tree finds the points
\\ of C over K_v (Qd = 0) or over a quadratic field Qd deterministically. For a disc c + uni^k O_W (uni a uniformiser
\\ of W, valuations v_W) write g(c + uni^k t) = sum a_i t^i (g = f on the chart x, or f*(s) = s^6 f(1/s) on the chart
\\ s = 1/x), v0 = v(a_0), m1 = min_{i >= 1} v(a_i), D = m1 - v0. For every t in O_W, g(c + uni^k t) = a_0 (1 + eps) with
\\ v(eps) >= D when v0 < m1. So: v0 odd and D > 0: no point in the disc; D > 2 v_W(2): every g value has the class of
\\ a_0 (squares iff a_0 is); a_0 = w^v0 u with u of obstruction level j (the first odd level where the digit reduction
\\ of td2_lvq_sqcoord meets a nonzero digit, or 2 v_W(2) for the AS digit) and j < D: no square in the disc (the digits
\\ of u below D are shared by all g values). Otherwise the disc is split into its q children (q = #residue field),
\\ down to the level kmax; a disc with D >= 2 v_W(2) - gap is not split further but tested at ntry random points
\\ (then the success rate is at least about 2^(-gap/2)); a disc accepted whole gives nacc random points (points of one
\\ disc can differ by formal group classes that are not in 2J). Returns the affine points [x, y] found (x, y in K_v, or in
\\ W for a field, then y is exact for x = the root of g(x) = y0^2 nearest to the sampled x).
td2_dtobst(c, fW, v2) =
{
  if (c[1], return(-1));
  for (i = 2, #c, if (c[i], return(if (i == #c, 2 * v2, 2 * ((i - 2) \ fW) + 1))));
  0;
}

td2_dtree(LV, cv, Qd, sd, kmax, nodemax = 400000, gap = 6, ntry = 4, nacc = 1) =
{
  my(e = mapget(LV, "e"), SP = td2_lvq_prep(LV, Qd), eW = SP[2], fW = SP[3], v2 = SP[4], one = mapget(LV, "one"), uni,
     th, res, stack, nodes = 0, out = List(), g = cv[sd], upw, nd, c, k, h, a, v0, m1, cl, j0, D, und = 0);
  if (Qd == 0,
    uni = mapget(LV, "Y") + 0 * one; res = [0, 1]
  ,
    th = Mod(Qd[4] + Qd[5] * Qd[7], Qd[7]^2 - Qd[1]);
    uni = if (eW == 2, th, Mod(mapget(LV, "Y") + 0 * one, Qd[7]^2 - Qd[1]));
    res = if (fW == 2, [0, 1, th, 1 + th], [0, 1]));
  upw = vector(kmax + 2); upw[1] = uni^0; for (i = 2, #upw, upw[i] = upw[i - 1] * uni);

  stack = List([[0 * uni, if (sd == 1, 0, 1)]]);
  while (#stack && nodes < nodemax,
    nd = stack[#stack]; listpop(stack); nodes++;
    c = nd[1]; k = nd[2];
    h = subst(g, 'x, c + upw[k + 1] * 'x);
    a = vector(poldegree(h, 'x) + 1, i, polcoef(h, i - 1, 'x));
    v0 = rich_lv_vf(LV, Qd, a[1]); m1 = oo;
    for (i = 2, #a, if (a[i] != 0, m1 = min(m1, rich_lv_vf(LV, Qd, a[i])[1])));
    if (m1 == oo, und++; next);
    if (v0[2] && v0[1] < m1,
      if (v0[1] % 2, next);
      D = m1 - v0[1];
      cl = td2_lvq_sqcoord(LV, SP, a[1]);
      if (type(cl) != "t_INT",
        j0 = td2_dtobst(cl, fW, v2);
        if (D > 2 * v2 || (j0 > 0 && j0 < D),
          if (j0 == 0, for (r = 1, nacc, listput(out, [c + upw[k + 1] * td2_rndloc(LV, Qd, 0), sd])));
          next);
        if (D >= 2 * v2 - gap,
          for (r = 1, ntry, my(t = c + upw[k + 1] * td2_rndloc(LV, Qd, 0), ct = td2_lvq_sqcoord(LV, SP, subst(g, 'x, t)));
            if (type(ct) != "t_INT" && ct == 0 * ct, listput(out, [t, sd])));
          next)));
    if (k >= kmax, und++; next);
    foreach (vecextract(res, numtoperm(#res, random((#res)!))), r, listput(stack, [c + r * upw[k + 1], k + 1])));
  \\ affine points
  my(pts = List());
  foreach (out, q, my(t = q[1], z = subst(g, 'x, t), pt = 0);
    iferr(
      if (Qd == 0,
        my(yy = rich_lv_sqrt(LV, z)); pt = td2_toaff(LV, 0, sd, t, yy)
      ,
        my(ap = rich_lv_approxsqrt(LV, Qd, z), rts, best = 0, bv = -oo);
        if (ap != 0 && ap != [],
          rts = iferr(rich_lv_roots(LV, Qd, g - ap[1]^2), E, []);
          foreach (rts, r, my(vv = rich_lv_vf(LV, Qd, r - t)[1]); if (vv > bv, bv = vv; best = r));
          if (best != 0 && !(sd == 2 && rich_lv_vf(LV, Qd, best)[1] == oo), pt = td2_toaff(LV, Qd, sd, best, ap[1]))))
    , E, pt = 0);
    if (pt != 0, listput(pts, pt)));
  [Vec(pts), nodes, und];
}

\\ ---------------------------------------------------------------- driver
\\ one candidate [u, v] from generator g, kept if its coordinates are new and it is certified. ST = [span, divs, stats,
\\ t0, verbose, name, per generator spans, FC] is updated in place (a named function with a reference argument: GP
\\ 2.17.4 leaks a copy of the captured objects at every call of a closure stored in a local variable). With fast
\\ screening (FC = ST[8] != 0) the local coordinates come first and only new classes are certified; otherwise the
\\ certificate comes first, then the exact coordinates.
td2_try(A, P, cand, g, ~ST) =
{
  my(cc, rr, rg, nfK = mapget(A, "nfK"), pr = mapget(P, "pr"));
  if (cand == 0, return(0));
  ST[3][g, 1]++;
  if (ST[8] != 0,
    \\ certified only when new for the span or for the span of its generator (the diagnostic "gendims")
    cc = td2_fastcoord(ST[8], cand[1]); if (type(cc) == "t_INT", return(0));
    rg = td2_span_add(ST[7][g], cc); rr = td2_span_add(ST[1], cc);
    if (!rr[2] && !rg[2], return(0));
    if (!td2_certify(nfK, pr, mapget(A, "f"), cand[1], cand[2]), return(0));
    ST[3][g, 2]++;
    if (rg[2], ST[7][g] = rg[1]);
    if (!rr[2], return(0))
  ,
    if (!td2_certify(nfK, pr, mapget(A, "f"), cand[1], cand[2]), return(0));
    ST[3][g, 2]++;
    cc = td2_coord(A, P, cand[1]); if (type(cc) == "t_INT", return(0));
    rg = td2_span_add(ST[7][g], cc); if (rg[2], ST[7][g] = rg[1]);
    rr = td2_span_add(ST[1], cc); if (!rr[2], return(0)));
  ST[1] = rr[1]; listput(ST[2], [cand[1], cand[2], cc]); ST[3][g, 3]++;
  if (ST[5], printf("    [%s] dim %d of %d (generator %d, %d s%s)\n", ST[6], ST[1][2], mapget(P, "D"), g,
                    (getabstime() - ST[4]) \ 1000, if (ST[8] != 0, ", fast coordinates", "")));
  1;
}

\\ exact coordinates of the divisors divs ([u, v, ...]): [span modulo the image of K_v^x, the divisors that enlarge it
\\ with their exact coordinates]
td2_verify(A, P, divs) =
{
  my(S = td2_span_new(P), kept = List(), cc, rr);
  foreach (divs, d,
    cc = td2_coord(A, P, d[1]); if (type(cc) == "t_INT", next);
    rr = td2_span_add(S, cc); if (rr[2], S = rr[1]; listput(kept, [d[1], d[2], cc])));
  [S, Vec(kept)];
}

\\ the local points of C over Qd (or K_v) with y = y0 whose x is nearest to x0 (largest valuation of x - x0)
td2_nearest(LV, cv, Qd, y0, x0) =
{
  my(pts = td2_ypoints(LV, cv, Qd, 1, y0), best = [], bv = -oo, vv);
  foreach (pts, pt, vv = rich_lv_vf(LV, Qd, pt[1] - x0)[1]; if (vv > bv, bv = vv; best = [pt]));
  best;
}

\\ one round of the generator gen (see td2_localimage); pool (rational points found so far) and ST updated in place
td2_round(A, P, LV, cv, Ib, qfd, groots, gen, ~pool, ~ST) =
{
  my(e = mapget(LV, "e"), yv, pts, Qd, dl, near, k);
  if (gen == 10,
    \\ a disc tree over a random quadratic extension (node cap: a random part of the tree)
    dl = td2_rnddelta(LV); if (rich_lv_issq(LV, dl) != 0, return(0)); Qd = rich_lv_quad(LV, dl);
    my(r = td2_dtree(LV, cv, Qd, 1 + random(2), Qd[3] * (3 * e + 4), 3000));
    foreach (r[1], pt, my(ab = rich_lv_ab(Qd, pt[1]), vb = rich_lv_val(LV, ab[2]));
      if (vb[2] && vb[1] < oo, td2_try(A, P, td2_cand_quad(LV, Qd, pt, Ib), 10, ~ST)));
    return(0));
  if (gen == 8,
    \\ P1 near a pool point P0 and P2 near another pool point P0', at independent random depths: the formal parts
    \\ P1 - P0 and P2 - P0' run along the directions of P0 and P0' in the formal group of J, independent when x(P0)
    \\ and x(P0') differ modulo pi, so P1 + P2 - D_inf sweeps a full box around P0 + P0' - D_inf (both formal
    \\ directions at every level; a single base point, generators 3 and 6, reaches the second direction only deep)
    my(i1 = 1 + random(#pool), i2 = 1 + random(#pool), n0, n1, p1, p2, k1, k2);
    if (i1 == i2, return(0));
    n0 = pool[i1]; n1 = pool[i2];
    k1 = floor(rich_lv_val(LV, n0[2])[1]) + random(3 * e + 3); k2 = floor(rich_lv_val(LV, n1[2])[1]) + random(3 * e + 3);
    p1 = td2_nearest(LV, cv, 0, n0[2] + rich_lv_pipow(LV, k1) * td2_rndloc(LV, 0, 0), n0[1]);
    p2 = td2_nearest(LV, cv, 0, n1[2] + rich_lv_pipow(LV, k2) * td2_rndloc(LV, 0, 0), n1[1]);
    if (#p1 && #p2, td2_try(A, P, td2_cand_pair(LV, p1[1], p2[1], Ib), 8, ~ST));
    return(0));
  if (gen == 7,
    \\ x = theta + pi^k w near a root theta of f (in K_v, or in the field of its quadratic factor), k in [0, 4e]; over
    \\ K_v also into a random quadratic extension: the Weil pairings with the 2-torsion points of a deep cluster of
    \\ roots only vary on such points
    my(rt = groots[1 + random(#groots)], x1, ap, z);
    Qd = rt[1];
    if (Qd == 0 && random(2), dl = td2_rnddelta(LV); if (rich_lv_issq(LV, dl) != 0, return(0)); Qd = rich_lv_quad(LV, dl));
    x1 = rt[2] + rich_lv_pipow(LV, random(4 * e + 1)) * td2_rndloc(LV, Qd, 0);
    z = subst(cv[1], 'x, x1);
    ap = iferr(rich_lv_approxsqrt(LV, Qd, z), E, 0);
    if (ap == 0 || ap == [], return(0));
    pts = td2_nearest(LV, cv, Qd, ap[1], x1);
    foreach (pts, pt,
      if (Qd == 0,
        if (#pool, td2_try(A, P, td2_cand_pair(LV, pt, pool[1 + random(#pool)], Ib), 7, ~ST));
        if (#pool < 300, listput(pool, pt), pool[1 + random(300)] = pt)
      ,
        my(ab = rich_lv_ab(Qd, pt[1]), vb = rich_lv_val(LV, ab[2]));
        if (vb[2] && vb[1] < oo, td2_try(A, P, td2_cand_quad(LV, Qd, pt, Ib), 7, ~ST))));
    return(0));
  if (gen == 1,
    yv = td2_yvalue(LV, cv, 0, random(3));
    pts = td2_ypoints(LV, cv, 0, yv[1], yv[2]);
    foreach (pts, pt,
      if (#pool, td2_try(A, P, td2_cand_pair(LV, pt, pool[1 + random(#pool)], Ib), 1, ~ST));
      if (#pool < 300, listput(pool, pt), pool[1 + random(300)] = pt));
    return(0));
  if (gen == 2 || gen == 4 || gen == 5,
    if (gen == 5, Qd = qfd[1 + random(#qfd)],
      dl = td2_rnddelta(LV);
      if (rich_lv_issq(LV, dl) != 0, return(0));
      Qd = rich_lv_quad(LV, dl));
    if (gen == 2, yv = td2_yvalue(LV, cv, Qd, random(3)));
    if (gen == 4,
      near = pool[1 + random(#pool)];
      k = floor(rich_lv_val(LV, near[2])[1]) + random(3 * e + 3);
      yv = [1, near[2] + rich_lv_pipow(LV, k) * td2_rndloc(LV, Qd, 0)]);
    if (gen == 5, yv = [1, td2_rndloc(LV, Qd, random(6 * e + 2))]);
    pts = td2_ypoints(LV, cv, Qd, yv[1], yv[2]);
    foreach (pts, pt, my(ab = rich_lv_ab(Qd, pt[1]), vb = rich_lv_val(LV, ab[2]));
      if (vb[2] && vb[1] < oo, td2_try(A, P, td2_cand_quad(LV, Qd, pt, Ib), gen, ~ST)));
    return(0));
  if (gen == 3,
    near = pool[1 + random(#pool)];
    k = floor(rich_lv_val(LV, near[2])[1]) + random(3 * e + 3);
    pts = td2_ypoints(LV, cv, 0, 1, near[2] + rich_lv_pipow(LV, k) * td2_rndloc(LV, 0, 0));
    foreach (pts, pt, td2_try(A, P, td2_cand_pair(LV, pt, near, Ib), 3, ~ST); if (#pool < 300, listput(pool, pt)));
    return(0));
  if (gen == 6,
    my(v0, s1, s2, dd, sq, w1, w2, p1, p2);
    near = pool[1 + random(#pool)];
    v0 = max(0, floor(rich_lv_val(LV, near[2])[1])) + 1;
    s1 = rich_lv_pipow(LV, v0 + random(3 * e + 2)) * td2_rndloc(LV, 0, 0);
    s2 = rich_lv_pipow(LV, 2 * v0 + random(6 * e + 4)) * td2_rndloc(LV, 0, 0);
    if (random(4) == 0, s1 = 0 * s1);
    dd = s1^2 - 4 * s2;
    sq = rich_lv_issq(LV, dd);
    if (sq < 0 || rich_lv_val(LV, dd)[1] == oo, return(0));
    if (sq == 1,
      my(r = rich_lv_sqrt(LV, dd));
      w1 = (s1 + r) / 2; w2 = (s1 - r) / 2;
      p1 = td2_nearest(LV, cv, 0, near[2] + w1, near[1]); p2 = td2_nearest(LV, cv, 0, near[2] + w2, near[1]);
      if (#p1 && #p2, td2_try(A, P, td2_cand_pair(LV, p1[1], p2[1], Ib), 6, ~ST))
    ,
      Qd = rich_lv_quad(LV, dd);
      w1 = Mod((s1 + Qd[7]) / 2, Qd[7]^2 - Qd[1]);
      p1 = td2_nearest(LV, cv, Qd, near[2] + w1, near[1]);
      foreach (p1, pt, my(ab = rich_lv_ab(Qd, pt[1]), vb = rich_lv_val(LV, ab[2]));
        if (vb[2] && vb[1] < oo, td2_try(A, P, td2_cand_quad(LV, Qd, pt, Ib), 6, ~ST)))));
  0;
}

\\ td2_localimage(A, P, {budget = 600000}, {verbose = 0}, {Nlift = 0}, {extra = []}, {check = 0}, {gw = 0}, {fast = 1}):
\\ samples candidate divisors in the local model, certifies them exactly (td2_certify), and keeps those whose mu_v
\\ coordinates are new modulo the image of K_v^x, until the span has dimension D_v or the time budget (ms) runs out.
\\ With fast = 1 (and every factor of f over K_v of degree <= 2) the screening uses the local coordinates of
\\ td2_fastcoord; the kept divisors are then checked with the exact coordinates (td2_coord: factor fields, or small
\\ models for a place of td2_smallplace), and "complete" refers to the exact check only (if it falls short, sampling
\\ goes on with exact coordinates). check > 0: check more rounds after D_v, failing if the span grows. extra:
\\ candidates [u, v] tried first. gw: weights of the generators (default all 1). A may be any Map with "nfK" and "f"
\\ when P comes from td2_smallplace. Generators:
\\  1 rational points from y-sampling (y an approximate square root of f(x1), or random of small or large valuation),
\\    each paired with a random earlier point;
\\  2 the same over a quadratic extension K_v(sqrt dl), dl uniform over the conductor (td2_rnddelta): P + P^sigma;
\\  3 a point near an earlier rational point P0 (y = y0 + pi^k u), paired with P0;
\\  4 a quadratic point near an earlier rational point;
\\  5 points over a quadratic factor field of f near its Weierstrass points (y small: y is the local parameter there,
\\    and P + P^sigma runs over a neighbourhood of a rational 2-torsion point, Haar-uniformly in y);
\\  6 two points near an earlier rational point P0 with y = y0 + w_i, w_1, w_2 the roots of w^2 - s1 w + s2 for s1, s2
\\    of independent random valuations (a neighbourhood of 0 in J: both formal directions at every level), rational
\\    or conjugate over K_v(sqrt(s1^2 - 4 s2)).
\\  7 points with x = theta + pi^k w near a root theta of f (k in [0, 4e], w random), over K_v, over a random quadratic
\\    extension, or over the field of the quadratic factor of theta (y an approximate square root of f(x), then the
\\    point with that y nearest to x): the classes that pair nontrivially with the 2-torsion points of a deep cluster
\\    of roots (a twin at distance 2e, say) come from such points.
\\  8 a point near a pool point P0 and a point near another pool point P0' (independent random depths): both
\\    directions of the formal group of J at every level around P0 + P0' - D_inf.
\\  9 (once, before the random rounds, when dt = 1) the K_v-points of the disc trees td2_dtree on both charts (kmax =
\\    3e + 4, 16 random tries per terminal disc, 3 points per disc accepted whole), each paired with the first one, then consecutive ones paired (the pivot pairs P_i + P_1 alone span a
\\    subspace of codimension up to 1 in the span of all pairs, since [P_i + P_j - D_inf] = [P_i + P_1 - D_inf] +
\\    [P_j + P_1 - D_inf] - [2 P_1 - D_inf]): every residue disc of C(K_v) down to that level, including the deep discs
\\    inside clusters that the random samplers miss;
\\ 10 the points of a disc tree over a random quadratic extension (td2_rnddelta), capped at 3000 nodes: P + P^sigma.
\\ Default weights: 1 for the random generators 1 to 8 and 10, 0 for 9 (not a random generator).
\\ Returns a Map: "divs" (list of [u, v, exact coordinates] of the kept divisors), "dim" (exact), "D", "complete",
\\ "fastdim" (dimension reached by the screening, or -1), "stats" (per generator: candidates, certified, kept; with
\\ fast screening only the candidates new for the screening are certified), "gendims" (per generator: dimension of
\\ the span of the coordinates of all its candidates, a diagnostic), "tries", "ms".
td2_localimage(A, P, budget = 600000, verbose = 0, Nlift = 0, extra = [], check = 0, gw = 0, fast = 1, dt = 1) =
{
  my(ncheck = 0, nfK = mapget(A, "nfK"), f = mapget(A, "f"), pr = mapget(P, "pr"), D = mapget(P, "D"), LV, cv, e, Ib, ST,
     pool = List(), gen, tries = 0, out = Map(), qf, qfd = [], ng = 10, FC = 0, vr, nfast = -1, gd, groots);
  e = pr.e;
  if (Nlift == 0, Nlift = 16 * e + 40);
  LV = if (mapisdefined(P, "LV"), mapget(P, "LV"), td2_lvinit(nfK, pr)); cv = td2_lvcurve(LV, f);
  mapput(LV, "Nlift", Nlift);
  Ib = idealpow(nfK, pr, Nlift);
  if (fast, FC = td2_fastinit(A, P, LV));
  ST = [0, List(), matrix(ng, 3), getabstime(), verbose, mapget(P, "name"), 0, FC];
  ST[1] = if (FC != 0, td2_fastspan_new(FC), td2_span_new(P)); ST[7] = vector(ng, i, ST[1]);
  if (gw == 0, gw = vector(ng, i, i != 9)); if (#gw < ng, gw = concat(gw, vector(ng - #gw, i, #gw + i != 9)));
  my(gcum = vector(ng, i, vecsum(gw[1..i])));
  qf = mapget(P, "qfields");
  qfd = vector(#qf, j, rich_lv_quad(LV, rich_lv_map(LV, qf[j])));
  \\ roots for generator 7: one per factor of f over K_v of degree <= 2 (the roots in K_v when the screening is off)
  groots = if (FC != 0, mapget(FC, "reps"), [[0, r] | r <- iferr(rich_lv_roots(LV, 0, rich_lv_mapx(LV, f), -1, 4000), E, [])]);
  foreach (extra, cand, if (ST[1][2] < D, td2_try(A, P, cand, 1, ~ST)));
  if (dt && ST[1][2] < D,
    \\ generator 9: the K_v-points of the disc trees (both charts) in random order, each paired with the first one, then
    \\ consecutive ones paired
    my(tp = List(), r, n, t9 = getabstime());
    for (sd = 1, 2, r = td2_dtree(LV, cv, 0, sd, 3 * e + 4, 400000, 6, 16, 3); foreach (r[1], pt, listput(tp, pt)));
    tp = Vec(tp); n = #tp;
    forstep (i = n, 2, -1, my(j = 1 + random(i), tmp = tp[i]); tp[i] = tp[j]; tp[j] = tmp);
    if (verbose, printf("    [%s] disc trees over K_v: %d points (%d ms)\n", ST[6], n, getabstime() - t9));
    for (i = 2, n, if (ST[1][2] >= D, break); td2_try(A, P, td2_cand_pair(LV, tp[i], tp[1], Ib), 9, ~ST));
    for (i = 2, n - 1, if (ST[1][2] >= D, break); td2_try(A, P, td2_cand_pair(LV, tp[i], tp[i + 1], Ib), 9, ~ST));
    foreach (tp, pt, if (#pool < 300, listput(pool, pt), pool[1 + random(300)] = pt)));
  while (1,
    while ((ST[1][2] < D || ncheck < check) && getabstime() - ST[4] < budget,
      tries++; if (ST[1][2] >= D, ncheck++);
      gen = if (#pool < 4, 1, my(rr = random(gcum[ng])); #[c | c <- gcum, c <= rr] + 1);
      if (gen == 5 && #qfd == 0, gen = 2);
      if (gen == 7 && #groots == 0, gen = 1);
      td2_round(A, P, LV, cv, Ib, qfd, groots, gen, ~pool, ~ST));
    td2_chk(ST[1][2] <= D, Str("the span exceeds D_v at ", mapget(P, "name"), ": the dimension rule or the coordinates are wrong"));
    gd = vector(ng, i, ST[7][i][2]);
    if (ST[8] == 0, break);
    \\ exact check of the divisors kept by the screening
    nfast = ST[1][2];
    vr = td2_verify(A, P, Vec(ST[2]));
    if (verbose, printf("    [%s] exact check of the %d divisors kept by the screening: dim %d of %d\n", ST[6], #ST[2], vr[1][2], D));
    td2_chk(vr[1][2] <= D, Str("the exact span exceeds D_v at ", mapget(P, "name")));
    ST[1] = vr[1]; ST[2] = List(vr[2]); ST[8] = 0; ST[7] = vector(ng, i, td2_span_new(P));
    if (ST[1][2] >= D || getabstime() - ST[4] >= budget, break));
  mapput(out, "divs", Vec(ST[2])); mapput(out, "dim", ST[1][2]); mapput(out, "D", D); mapput(out, "complete", ST[1][2] == D);
  mapput(out, "fastdim", nfast); mapput(out, "stats", ST[3]); mapput(out, "gendims", gd); mapput(out, "tries", tries);
  mapput(out, "ms", getabstime() - ST[4]);
  out;
}

\\ the algebra data from precomputed factor fields (as returned by td2_field) of f over K
td2_alg_from(nfK, f, flds, plist = [2]) =
{
  my(A = Map(), prod = 1);
  f = td2_Kx(nfK, f);
  foreach (flds, F, prod *= td2_Kx(nfK, F[1]));
  td2_chk(prod * pollead(f) == f, "the factor fields do not multiply to f");
  mapput(A, "nfK", nfK); mapput(A, "f", f); mapput(A, "lc", pollead(f)); mapput(A, "fd", deriv(f, 'x));
  mapput(A, "flds", flds); mapput(A, "plist", plist); mapput(A, "pre", td2_pre(nfK, flds));
  A;
}
