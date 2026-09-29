\\ real_root_cert.gp: the real root certificate of K21Real.lean (M3b discharge), found here, rechecked by the Lean kernel.
\\ Transform of a coefficient list l (constant first, length L) by lists u, v: T(l) = sum_k l_k u^k v^(L-1-k), so that
\\ v(y) T(l)(y) = v(y)^L l(u(y)/v(y)). Interval (A/D, B/D): u = A + B y, v = D + D y; ray: u = C +- D y, v = D; point:
\\ u = A, v = D. A sign certificate: every coefficient of s T(l) is >= 0, one is > 0.
\\ Elements are given by their zk coordinates as in Lean (epsL, gensL[1], gensL[3], gensL[7], mL, pasted from the Lean
\\ data files), with power basis numerator combo(a) = sum_j a_j zkNum_j (evaluates to Dz * element at the root).
\\ Run from code/descent: gp -q ../selmer-global-bound/real_root_cert.gp < /dev/null
default(parisizemax, 2*10^9); default(nbthreads, 1);
read("descent_data_lib.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
fl = Vecrev(subst(K21, b, X));                     \\ fL, constant first, length 22
dl(l) = { my(n = #l); vector(n, k, if (k < n, k * l[k + 1], 0)); }   \\ Lean derivL: same length, trailing zero
chk(fl == [-4, 28, -112, 252, -336, 28, 560, -1072, 1008, -280, -770, 980, -609, 175, 2, 98, -84, 0, 0, 14, -7, 1], "fL matches Lean");
Tl(l, u, v) = { my(L = #l); sum(k = 0, L - 1, l[k + 1] * u^k * v^(L - 1 - k)); }
cert(s, l, u, v) = { my(q = s * Tl(l, u, v), c = if (q == 0, [0], Vec(q))); vecmin(c) >= 0 && vecmax(c) > 0; }
iv(A, B, D) = [A + B*y, D + D*y];
sgnI(l, A, B, D) = { my(w = iv(A, B, D)); if (cert(1, l, w[1], w[2]), 1, if (cert(-1, l, w[1], w[2]), -1, 0)); }
sgnP(l, A, D) = { if (cert(1, l, A, D), 1, if (cert(-1, l, A, D), -1, 0)); }
\\ the partition of [-4, 4] over D0
D0 = 32; C0 = 4 * D0;
chk(cert(1, fl, C0 + D0*y, D0), "f > 0 on (4, oo)");
chk(cert(-1, fl, -C0 - D0*y, D0), "f < 0 on (-oo, -4)");
bp = [-4, -2, -1, -7/8, -27/32, -13/16, -3/4, -1/2, 0, 1, 3/2, 7/4, 2, 4] * D0;
mono = [[-1, -7/8], [-27/32, -13/16], [7/4, 2]] * D0;
for (i = 1, #bp, chk(sgnP(fl, bp[i], D0) != 0, Str("f(", bp[i] / D0, ") != 0")));
{
for (i = 1, #bp - 1, my(A = bp[i], B = bp[i + 1], ism = #select(p -> p == [A, B], mono) > 0);
  chk(A < B, "increasing");
  if (ism, chk(sgnI(dl(fl), A, B, D0) != 0, Str("f' has a sign on ", [A, B] / D0)),
           chk(sgnI(fl, A, B, D0) != 0, Str("f has a sign on ", [A, B] / D0))));
}
print("mono signs of f': ", vector(3, i, sgnI(dl(fl), mono[i][1], mono[i][2], D0)));
\\ elements
cmb(a) = { my(r = vector(21)); for (j = 1, 21, r += a[j] * zkNum[j]); r; }
epsL = [26, -28, -8, -5, 1, -3, 0, 3, 9, -1, 8, -16, -3, 14, -6, -12, -8, 13, -3, -4, 0];
g1 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0];
g3 = [-1, -1, 0, 1, -1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0];
g7 = [-1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0];
mL = [-1005, 782, -1158, -1402, 998, 2617, -2135, 920, -2180, -2902, 976, -408, -1753, 625, 557, -919, -319, -253, -722, -1051, 877];
els = [cmb(epsL), cmb(g1), cmb(g3), cmb(g7), cmb(mL)];
\\ numerical sanity: the element values at the roots
rts = polrootsreal(subst(K21, b, X));
print("roots: ", rts);
for (r = 1, 3, print("root ", r, " values of eps, g1, g3, g7, m: ", vector(5, i, subst(Pol(Vecrev(els[i])), x, rts[r]) / Dz * 1.)));
\\ refine each monotone piece by bisection until every element has a certified sign (rational endpoints)
ri = vector(3);
{
for (r = 1, 3, my(lo = mono[r][1] / D0, hi = mono[r][2] / D0, ss, it = 0, sl = sign(subst(Pol(Vecrev(fl)), x, lo)));
  while (1,
    my(Dc = denominator([lo, hi]));
    ss = vector(#els, i, sgnI(els[i], lo * Dc, hi * Dc, Dc));
    if (vecmin(apply(abs, ss)) == 1, break);
    my(mid = (lo + hi) / 2); it++;
    if (sign(subst(Pol(Vecrev(fl)), x, mid)) == sl, lo = mid, hi = mid));
  ri[r] = [lo, hi];
  print("root ", r, ": ", [lo, hi], " after ", it, " bisections; signs of eps, g1, g3, g7, m: ", ss));
}
D1 = denominator(concat(ri));
print("D1 = ", D1, " = 2^", valuation(D1, 2));
\\ recheck everything over the common denominator D1, in the Lean format
{
for (r = 1, 3, my(A = ri[r][1] * D1, B = ri[r][2] * D1);
  chk(mono[r][1] * D1 <= A * D0 && B * D0 <= mono[r][2] * D1, Str("refined interval ", r, " inside its piece"));
  chk(sgnP(fl, A, D1) * sgnP(fl, B, D1) == -1, Str("f changes sign on refined interval ", r));
  print("root ", r, ": A = ", A, ", B = ", B, ", f signs at ends ", [sgnP(fl, A, D1), sgnP(fl, B, D1)],
        ", element signs ", vector(#els, i, sgnI(els[i], A, B, D1))));
}
