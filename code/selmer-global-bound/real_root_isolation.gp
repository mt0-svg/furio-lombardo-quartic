\\ real_root_isolation.gp: real root isolation of f = K21(b) by Moebius transform positivity, for the M3b discharge.
\\ q(y) = sum_k P_k (A + B y)^k (D + D y)^(n-k) = (D (1 + y))^n P((A + B y) / (D (1 + y))): if every coefficient of q has
\\ one sign (not all zero), P has that sign on (A/D, B/D). Rays: q(y) = sum_k P_k (C + s D y)^k D^(n-k) on (C/D, s oo).
\\ Output: breakpoints over D = 2^k, the kind of each piece, and the sign of the elements of K21 used by Lean at each root.
\\ Run from code/descent: gp -q ../selmer-global-bound/real_root_isolation.gp < /dev/null
default(parisizemax, 2*10^9); default(nbthreads, 1);
read("descent_search_lib.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
fP = subst(K21, b, X);          \\ f as a polynomial in X
mob(P, A, B, D) = { my(n = poldegree(P, X)); sum(k = 0, n, polcoef(P, k, X) * (A + B*y)^k * (D + D*y)^(n - k)); }
ray(P, C, D, s) = { my(n = poldegree(P, X)); sum(k = 0, n, polcoef(P, k, X) * (C + s*D*y)^k * D^(n - k)); }
sgnq(q) = { my(v = Vec(q), pos = 0, neg = 0); for (i = 1, #v, if (v[i] > 0, pos++); if (v[i] < 0, neg++)); if (neg == 0 && pos > 0, 1, if (pos == 0 && neg > 0, -1, 0)); }
fd = deriv(fP, X);
ev(P, A, D) = subst(P, X, A / D);
\\ VCA on [lo, hi] (numerators over D): returns list of [lo, hi, kind, sign], kind 0 = no root (f cert), 1 = monotone (f' cert)
vca(lo, hi, D) = {
  my(s = sgnq(mob(fP, lo, hi, D)), s1);
  if (s != 0, return([[lo, hi, 0, s]]));
  s1 = sgnq(mob(fd, lo, hi, D));
  if (s1 != 0, return([[lo, hi, 1, s1]]));
  my(mid = (lo + hi) / 2);
  if (denominator(mid) != 1, error("need a finer D"));
  concat(vca(lo, mid, D), vca(mid, hi, D));
}
k = 40; D = 2^k;
Cb = 4;   \\ outer bound: rays (-oo, -Cb) and (Cb, oo)
chk(sgnq(ray(fP, Cb * D, D, 1)) == 1, "f > 0 on (4, oo) (ray certificate)");
chk(sgnq(ray(fP, -Cb * D, D, -1)) == -1, "f < 0 on (-oo, -4) (ray certificate; odd degree)");
pcs = vca(-Cb * D, Cb * D, D);
print("pieces from VCA: ", #pcs);
for (i = 1, #pcs, my(p = pcs[i]); if (p[3] == 1, print("  monotone piece ", [p[1], p[2]] * 1. / D, " sign f' ", p[4], ", f at ends ", sign(ev(fP, p[1], D)), " ", sign(ev(fP, p[2], D)))));
\\ elements: P_z(X) = Dz * z (power basis numerator), sign of z at the root = sign of P_z at the root
elP(z) = subst(lift(Mod(nfbasistoalg(nf, z), K21)) * Dz, b, X);
eps = G[1]; foreach([2, 5, 7, 10, 11], i, eps = mulz(eps, G[i]));
els = [eps, G[2], G[4], G[8]];
roots = [p | p <- pcs, p[3] == 1];
{
for (r = 1, 3, my(lo = roots[r][1], hi = roots[r][2], ss, it = 0);
  while (1,
    ss = vector(#els, i, sgnq(mob(elP(els[i]), lo, hi, D)));
    if (vecmin(apply(abs, ss)) == 1, break);
    my(mid = (lo + hi) / 2); it++;
    if (sign(ev(fP, lo, D)) * sign(ev(fP, mid, D)) < 0, hi = mid, lo = mid));
  print("root ", r, ": small interval ", [lo, hi] * 1. / D, " after ", it, " bisections; signs of eps, g1, g3, g7: ", ss));
}
