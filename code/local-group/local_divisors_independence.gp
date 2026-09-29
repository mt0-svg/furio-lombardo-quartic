\\ local_divisors_independence.gp: the independence of the x - T classes of D_1..D_7 in H(f_v), f = (fRev k)^sigma, by three
\\ homomorphisms out of K_v[T]/(f) (p-adic model of completion_kv_lib.gp, data read from the Lean files):
\\   N' = K_v(w'), w'^2 = delta' = sigma(d)/4 (d = disc q), tau = -q1/2 + w' a root of q;
\\   M' = N'(x0), x0^2 = -P0 - P1 x0, P = A + w B = X^2 + P1 X + P0 (P1 = a1 + 2 b1 w', P0 = a0 + 2 b0 w'), x0 a root of h;
\\   psi1(x) = N_{N'/K_v}(x(tau)) mod squares, psi2(x) = N_{M'/N'}(x(x0)) mod squares, psi3(x) = x(x0) x(tau) mod squares.
\\ If x = c y^2 (c in K_v) all three are squares. For each c in F_2^7 - 0 we find the first test that fails for
\\ prod U_i(T)^c_i (U_i = X^2 + p_i X + r_i the reversed u_i) and print the valuations the Lean certificates will need.
\\ Run: gp -q local_divisors_independence.gp
default(parisizemax, 3*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../descent/descent_data_lib.gp");
read("completion_kv_lib.gp");
read("lean_data_reader.gp");
zkv(l, m) = sg(nfbasistoalg(nf, l~) / m);
\\ N' = QA K_v dl 0: pairs [x, y]
nmul(u, v, dl) = [u[1]*v[1] + dl*u[2]*v[2], u[1]*v[2] + u[2]*v[1]];
nnorm(u, dl) = u[1]^2 - dl*u[2]^2;
nsq(z, dl) = { my(x = z[1], y = z[2], n);
  if (y == 0 || vpi(y) > 2000, return(ksq(x) || ksq(x / dl)));
  if (!ksq(nnorm(z, dl)), return(0));
  n = ksqrt(nnorm(z, dl)); ksq((x + n) / 2) || ksq((x - n) / 2) };
nsqrt(z, dl) = { my(x = z[1], y = z[2], n, s0);
  if (y == 0 || vpi(y) > 2000, return(if (ksq(x), [ksqrt(x), 0], [0, ksqrt(x / dl)])));
  n = ksqrt(nnorm(z, dl)); if (!ksq((x + n) / 2), n = -n);
  s0 = ksqrt((x + n) / 2); [s0, y / (2 * s0)] };
nadd(u, v) = [u[1] + v[1], u[2] + v[2]];
nsc(c, u) = [c * u[1], c * u[2]];
\\ M' = QA N' A B (A = -P0, B = -P1): pairs of N' elements
mmul(u, v, A, B, dl) = { my(yy = nmul(u[2], v[2], dl));
  [nadd(nmul(u[1], v[1], dl), nmul(A, yy, dl)), nadd(nadd(nmul(u[1], v[2], dl), nmul(u[2], v[1], dl)), nmul(B, yy, dl))] };
mnorm(z, A, B, dl) = nadd(nadd(nmul(z[1], z[1], dl), nmul(B, nmul(z[1], z[2], dl), dl)), nsc(-1, nmul(A, nmul(z[2], z[2], dl), dl)));
mtr(z, B, dl) = nadd(nsc(2, z[1]), nmul(B, z[2], dl));
msq(z, A, B, dl) = { my(Nz = mnorm(z, A, B, dl), n, tr);
  if (!nsq(Nz, dl), return(0));
  n = nsqrt(Nz, dl); tr = mtr(z, B, dl);
  nsq(nadd(tr, nsc(2, n)), dl) || nsq(nadd(tr, nsc(-2, n)), dl) };
nv(z) = min(vpi(z[1]), vpi(z[2]));
{
  for (k = 1, 2,
    my(q0 = zkv(qDataL[k][1], qDenL[k]), q1 = zkv(qDataL[k][2], qDenL[k]), dq = zkv(dnDataL[k], qDenL[k]^2), dl,
       a0 = zkv(abDataL[k][1], maDenL[k]), a1 = zkv(abDataL[k][2], maDenL[k]), b0 = zkv(abDataL[k][3], mbDenL[k]),
       b1 = zkv(abDataL[k][4], mbDenL[k]), tau, P1, P0, A, B, R = read(Str("../earlier-computations/local_images_twist", k - 1, "_e3.bin")),
       ps1 = vector(7), ps2 = vector(7), ps3 = vector(7), cnt = [0, 0, 0, 0], hh);
    dl = dq / 4; tau = [-q1 / 2, 1];
    chq(vpi(dq - (q1^2 - 4*q0)) > 2000, "d = q1^2 - 4 q0");
    chq(nv(nadd(nadd(nmul(tau, tau, dl), nsc(q1, tau)), [q0, 0])) > 2000, "q(tau) = 0");
    P1 = [a1, 2 * b1]; P0 = [a0, 2 * b0]; A = nsc(-1, P0); B = nsc(-1, P1);
    \\ h(x0) = 0 with h = A(X)^2 - d B(X)^2 evaluated at x0 = [0, 1] in M'
    my(x0 = [[0, 0], [1, 0]], one = [[1, 0], [0, 0]], x02 = mmul(x0, x0, A, B, dl), Ax, Bx, hx);
    Ax = [nadd(nadd(x02[1], nsc(a1, x0[1])), [a0, 0]), nadd(x02[2], nsc(a1, x0[2]))];
    Bx = [nadd(nsc(b1, x0[1]), [b0, 0]), nsc(b1, x0[2])];
    hx = mmul(Ax, Ax, A, B, dl); my(bb = mmul(Bx, Bx, A, B, dl)); hx = [nadd(hx[1], nsc(-dq, bb[1])), nadd(hx[2], nsc(-dq, bb[2]))];
    chq(nv(hx[1]) > 2000 && nv(hx[2]) > 2000, "h(x0) = 0");
    printf("---- twist %d: v(delta') = %d, v(q0) %d v(q1) %d, v(P1) = %d %d, v(P0) = %d %d\n", k - 1, vpi(dl), vpi(q0), vpi(q1), vpi(P1[1]), vpi(P1[2]), vpi(P0[1]), vpi(P0[2]));
    for (i = 1, 7,
      my(uu = subst(lift(R[7][i][1]), 'x, t), u0 = polcoef(uu, 0, t), u1 = polcoef(uu, 1, t), p = sg(lift(Mod(u1, K21) / Mod(u0, K21))),
         r = sg(lift(1 / Mod(u0, K21))), Ut, Ux);
      Ut = nadd(nadd(nmul(tau, tau, dl), nsc(p, tau)), [r, 0]);
      Ux = [nadd([r, 0], nsc(-1, P0)), nadd([p, 0], nsc(-1, P1))];
      ps1[i] = nnorm(Ut, dl); ps2[i] = mnorm(Ux, A, B, dl); ps3[i] = mmul(Ux, [Ut, [0, 0]], A, B, dl);
      printf("  D_%d: v(p) %d v(r) %d; v(psi1) %d; v(psi2) %d %d (norm %d); v(U(tau)) %d %d\n", i, vpi(p), vpi(r), vpi(ps1[i]),
        vpi(ps2[i][1]), vpi(ps2[i][2]), vpi(nnorm(ps2[i], dl)), vpi(Ut[1]), vpi(Ut[2])));
    forvec (c = vector(7, j, [0, 1]), if (c != 0,
      my(x1 = prod(j = 1, 7, ps1[j]^c[j]), x2 = [1, 0], x3 = [[1, 0], [0, 0]], lvl);
      for (j = 1, 7, if (c[j], x2 = nmul(x2, ps2[j], dl); x3 = mmul(x3, ps3[j], A, B, dl)));
      lvl = if (!ksq(x1), 1, if (!nsq(x2, dl), 2, if (!msq(x3, A, B, dl), 3, 4)));
      cnt[lvl]++;
      if (lvl >= 2, printf("  c = %s: level %d; v(psi1) %d; psi2: v %d %d, norm v %d square %d; psi3 norm v %d %d\n", c, lvl, vpi(x1),
         vpi(x2[1]), vpi(x2[2]), vpi(nnorm(x2, dl)), ksq(nnorm(x2, dl)), nv(mnorm(x3, A, B, dl)), 0))));
    printf("  killed by psi1 %d, psi2 %d, psi3 %d, none %d\n", cnt[1], cnt[2], cnt[3], cnt[4]));
}
quit;
