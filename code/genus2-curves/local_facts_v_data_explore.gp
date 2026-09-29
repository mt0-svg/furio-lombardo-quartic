\\ local_facts_v_data_explore.gp: WP5 exploration. For both twists: A, B with h = A^2 - d B^2 (as local_facts_v_biquadratic.gp), the two elements
\\ of N = K_v(sqrt d) whose non-squareness (irr) and (nsq) need:
\\   D   = disc(A + w B) = D0 + D1 w,  D0 = a1^2 + d b1^2 - 4 a0, D1 = 2 a1 b1 - 4 b0;
\\   rho = Res(q, A + w B) = p0^2 - p0 p1 P1 + p1^2 P0, P1 = a1 + b1 w, P0 = a0 + b0 w, p_i = q_i - P_i
\\ (w^2 = d), and for z = z0 + z1 w the square root test: n^2 = N(z) = z0^2 - d z1^2 in K_v, then (z0 +- n)/2 must both
\\ be non-squares in K_v. K_v = Q_2[X]/(E) with sigma(theta) = theta* (Hensel from M4Cert's theta0), p-adic arithmetic.
\\ Prints the pi-adic valuations and the square classes.
\\ Run from code/genus2-curves: gp -q local_facts_v_data_explore.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../earlier-computations/richelot_data.gp");
red(g) = lift(Mod(1, K21) * g);
pr = [P | P <- idealprimedec(nf, 2), P.e == 3][1];
Msym(c) = [c[1], c[2]/2, c[3]/2; c[2]/2, c[4], c[5]/2; c[3]/2, c[5]/2, c[6]];
dd = [d0, d1];
lsq(a) = nfislocalpower(nf, pr, lift(Mod(a, K21)), 2);
gsq(a) = #nfroots(nf, 'y^2 - lift(Mod(a, K21))) > 0;
gsqrt(a) = nfroots(nf, 'y^2 - lift(Mod(a, K21)))[1];
vl(a) = if (a == 0, oo, nfeltval(nf, a, pr));
\\ K_v
PR = 240;
EE = 'X^3 + 37469486047374096441064*'X^2 + 16418729904282180494548*'X + 17325639337422721302482;
pa(c) = c + O(2^PR);
kv(v) = Mod(pa(v[1]) + pa(v[2])*'X + pa(v[3])*'X^2, EE);
cf(e, i) = polcoef(lift(e), i, 'X);
v2(c) = if (c == 0, 10^6, valuation(c, 2));
vpi(e) = min(3 * v2(cf(e, 0)), min(3 * v2(cf(e, 1)) + 1, 3 * v2(cf(e, 2)) + 2));
fK = Pol(Vec(K21), 'X);
th = kv([163180991353, 3522151726, 560510631928]);
for (i = 1, 12, th = th - subst(fK, 'X, th) / subst(deriv(fK, 'X), 'X, th));
print("f(theta*) valuation: ", vpi(subst(fK, 'X, th)));
sg(a) = subst(Pol(lift(Mod(a, K21)), 'b) , 'b, th);
PIK = Mod('X, EE);
\\ unit square test: s^2 = u mod pi^7 for some s mod 4
usq(u) = { forvec(s = [[0, 3], [0, 3], [0, 3]], my(e = u - kv(s)^2); if (e == 0 || vpi(e) >= 7, return(1))); 0 };
ksq(w) = { if (w == 0, return(1)); my(v = vpi(w)); if (v % 2, return(0)); usq(w / PIK^v) };
ksqrt(w) = { my(v = vpi(w), u, s = 0); if (v % 2, error("odd valuation")); u = w / PIK^v;
  forvec(t = [[0, 3], [0, 3], [0, 3]], my(e = u - kv(t)^2); if (e == 0 || vpi(e) >= 7, s = kv(t); break));
  if (s == 0, error("unit not a square"));
  for (i = 1, 12, s = (s + u / s) / 2); PIK^(v / 2) * s };
chk(name, z0, z1, dq) = {
  my(Nz = red(z0^2 - dq * z1^2), n, Z0 = sg(z0), p, m);
  printf("  %s: v(z0) = %s, v(z1) = %s, v(N) = %s; N square at v: %d, global: %d; zk denominators z0 %d, z1 %d, N %d\n", name,
    vl(z0), vl(z1), vl(Nz), lsq(Nz), gsq(Nz), denominator(zkc(z0)), denominator(zkc(z1)), denominator(zkc(Nz)));
  n = ksqrt(sg(Nz));
  printf("    check n^2 = N: v(n^2 - N) = %s (precision)\n", vpi(n^2 - sg(Nz)));
  p = (Z0 + n) / 2; m = (Z0 - n) / 2;
  printf("    v(n) = %d, v((z0+n)/2) = %s square %d, v((z0-n)/2) = %s square %d\n", vpi(n), vpi(p), ksq(p), vpi(m), ksq(m));
};
{ for (k = 1, 2,
    my(f = red(-dd[k] * matdet(Msym(Qc[1]) + 2*t*Msym(Qc[2]) + t^2*Msym(Qc[3]))), fr, fa, q, h, c, dq, u, wV, cub, A, B, rts);
    fr = polrecip(f); c = pollead(fr, t);
    fa = nffactor(nf, fr); q = fa[1, 1]; h = fa[2, 1];
    dq = red(polcoef(q, 1, t)^2 - 4 * polcoef(q, 0, t));
    u = polcoef(h, 3, t) / 2;
    wV = (polcoef(h, 2, t) - u^2 + dq * 'a) / 2;
    cub = red(dq * 'a * wV^2 - (u * wV - polcoef(h, 1, t) / 2)^2 - polcoef(h, 0, t) * dq * 'a);
    rts = nfroots(nf, cub); A = 0;
    foreach(rts, V0, if (V0 != 0 && gsq(V0),
      my(v0 = gsqrt(V0), w0 = red(subst(wV, 'a, V0)), z0);
      z0 = red((u * w0 - polcoef(h, 1, t) / 2) / (dq * v0));
      if (red((t^2 + u*t + w0)^2 - dq * (v0*t + z0)^2 - h) == 0, A = red(t^2 + u*t + w0); B = red(v0*t + z0); break)));
    if (A == 0, error("no A, B"));
    my(a1 = polcoef(A, 1, t), a0 = polcoef(A, 0, t), b1 = polcoef(B, 1, t), b0 = polcoef(B, 0, t), q1 = polcoef(q, 1, t), q0 = polcoef(q, 0, t));
    printf("k = %d: roots of the resolvent cubic: %d; zk denominators a1 %d a0 %d b1 %d b0 %d d %d; v(a1) %s v(a0) %s v(b1) %s v(b0) %s v(d) %s v(q1) %s v(q0) %s\n",
      k - 1, #rts, denominator(zkc(a1)), denominator(zkc(a0)), denominator(zkc(b1)), denominator(zkc(b0)), denominator(zkc(dq)),
      vl(a1), vl(a0), vl(b1), vl(b0), vl(dq), vl(q1), vl(q0));
    printf("  sigma check: v(E(sigma d)) ok, d square at v: %d (PARI), %d (K_v test); -3 square: %d, -3d square: %d\n", lsq(dq), ksq(sg(dq)), ksq(sg(-3)), ksq(sg(-3*dq)));
    my(D0 = red(a1^2 + dq * b1^2 - 4 * a0), D1 = red(2 * a1 * b1 - 4 * b0));
    chk("D", D0, D1, dq);
    my(P1 = a1 + b1 * 'w, P0 = a0 + b0 * 'w, p1 = q1 - P1, p0 = q0 - P0, rho, r0, r1);
    rho = lift(Mod(Mod(1, K21) * (p0^2 - p0 * p1 * P1 + p1^2 * P0), 'w^2 - dq));
    r0 = red(polcoef(rho, 0, 'w)); r1 = red(polcoef(rho, 1, 'w));
    chk("rho", r0, r1, dq);
  );
}
quit;
