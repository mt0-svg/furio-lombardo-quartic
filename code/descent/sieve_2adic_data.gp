\\ sieve_2adic_data.gp: certificate data for the local step at lc = gO 14 (the prime above 2 with e = 6, f = 1) of M1,
\\ lean/FurioLombardo/M1/Data2.lean, used by Local2.lean (kill2: survE 5 and survE 7 are killed at lc).
\\ Not trusted: Lean rechecks every identity with the Kronecker checker.
\\ Inputs: /tmp/m1_gensLean.gp (see the header of descent_bruin_data.gp) and /tmp/m1w/surv.gp (see local_steps_design.gp).
\\ Design: pi = gO 14; for every normalized chart point P mod 8 with F(P) = 0 mod 8 and
\\ each k in {5, 7} (0-based index of sieveSurv), with G = gProd(survE k) = G' + 8 H (G' = G mod 8 on zk, balanced),
\\ one conic i in {0, 2} (Q1 or Q3) and w0 = Q_i(P) G':
\\   odd leaf    w0 = pi^v (1 + pi T), v odd, v < 18;
\\   defect leaf w0 = pi^(2j) ((1 + pi S)^2 + pi^d (1 + pi Z)), d odd, d < 12, 2j + d < 18.
\\ Also T12 = (gO 12 - 1)/pi and T13 = (gO 13 - 1)/pi.
\\ Output: without sieve_2adic_precisions.gp, /tmp/m1w/lc_data.lean with Kronecker precisions 0 (for measuring them); with it
\\ (lcK = minimal precisions in steps of 64 bits, measured by compiled evaluation of checkK),
\\ the final ../../FurioLombardo/M1/Data2.lean.
\\ Run: gp -q sieve_2adic_data.gp < /dev/null
default(parisizemax, 1500*10^6); default(nbthreads, 1);
LEANDIR = if (type(getenv("LEANOUT")) == "t_STR", getenv("LEANOUT"), "../../");  \\ LEANOUT=<dir>/ writes the Lean file under <dir> instead of lean/
read("descent_data_lib.gp");
read("/tmp/m1_gensLean.gp");
read("/tmp/m1w/surv.gp");
gz(i) = zkr(gensLean[i + 1]~);
Fi(P) = substvec(F, [x, y, z], P);
bal8(v) = vector(#v, i, my(r = v[i] % 8); if (r > 4, r - 8, r));
isintv(v) = { for (i = 1, #v, if (denominator(v[i]) != 1, return(0))); 1 };
maxd(v) = vecmax(apply(n -> #digits(abs(n) + 1), Vec(v)));
\\ zk coordinates of Q_i(P) (i = 1 or 3), from QcZ exactly as the Lean qev
qP(i, P) = { my(mon = [P[1]^2, P[1]*P[2], P[1]*P[3], P[2]^2, P[2]*P[3], P[3]^2]); sum(m = 1, 6, mon[m] * QcZ[i][m]) };
\\ chart points, in the order of the Lean list chartPts
r8 = [0..7]; r4 = [0, 2, 4, 6];
{chart = concat([concat(vector(8, a, vector(8, c, [r8[a], r8[c], 1]))),
  concat(vector(8, a, vector(4, c, [1, r8[a], r4[c]]))),
  concat(vector(4, a, vector(4, c, [r4[a], 1, r4[c]])))]);}
main() = {
  my(pi, pr, prs, U, Gs, Gp, Hs, pts, out, kk, T12, T13, o, nkk);
  pi = gz(14);
  prs = idealprimedec(nf, 2);
  pr = 0; for (t = 1, #prs, if (nfeltval(nf, pi, prs[t]) == 1, pr = prs[t]));
  if (pr == 0 || pr.e != 6 || pr.f != 1, print("FAIL prime"); return(0));
  for (t = 1, #prs, if (prs[t] != pr && nfeltval(nf, pi, prs[t]) != 0, print("FAIL pi not a pr-uniformizer only"); return(0)));
  if (abs(idealnorm(nf, pi)) != 2, print("FAIL norm pi"); return(0));
  U = nfeltdiv(nf, 2, nfeltpow(nf, pi, 6));
  if (!isintv(U) || nfeltval(nf, U, pr) != 0, print("FAIL U"); return(0));
  T12 = nfeltdiv(nf, nfeltadd(nf, gz(12), -1), pi); T13 = nfeltdiv(nf, nfeltadd(nf, gz(13), -1), pi);
  if (!isintv(T12) || !isintv(T13), print("FAIL T12 T13"); return(0));
  Gs = vector(2); Gp = vector(2); Hs = vector(2);
  for (kx = 1, 2, my(k0 = [5, 7][kx], e = surv[k0 + 1], G = vectorv(21, i, i == 1));
    for (i = 0, 17, if (e[i + 1], G = nfeltmul(nf, G, gz(i))));
    Gs[kx] = G; Gp[kx] = bal8(G)~; Hs[kx] = (G - Gp[kx]) / 8;
    if (!isintv(Hs[kx]), print("FAIL H"); return(0));
    if (nfeltval(nf, G, pr) != 1, print("FAIL val G ", k0); return(0)));
  pts = [P | P <- chart, Fi(P) % 8 == 0];
  print("chart points ", #chart, ", with F = 0 mod 8: ", #pts);
  out = vector(#pts, n, vector(2));
  for (n = 1, #pts, my(P = pts[n]);
    for (kx = 1, 2, my(best = 0, bsz = 10^9);
      foreach([1, 3], i, my(q = qP(i, P), w0, v, c, sz);
        w0 = nfeltmul(nf, q, Gp[kx]); v = nfeltval(nf, w0, pr);
        \\ consistency with the exact local test: the class of Q_i(P) G must not be a local square
        if (v < 18 && v % 2 == 1,
          my(T = nfeltdiv(nf, nfeltadd(nf, nfeltdiv(nf, w0, nfeltpow(nf, pi, v)), -1), pi));
          if (!isintv(T), print("FAIL T integral"); return(0));
          c = [0, i - 1, v, T]; sz = maxd(T);
          if (sz < bsz, best = c; bsz = sz));
        if (v < 18 && v % 2 == 0,
          my(A = nfeltdiv(nf, w0, nfeltpow(nf, pi, v)), s0 = vectorv(21, t, t == 1), D, dv, it = 0);
          while (1,
            D = nfeltadd(nf, A, -nfeltmul(nf, s0, s0));
            if (D == 0, dv = oo; break);
            dv = nfeltval(nf, D, pr);
            if (dv % 2 == 1 || dv >= 12, break);
            s0 = nfeltadd(nf, s0, nfeltpow(nf, pi, dv / 2)); it++;
            if (it > 20, print("FAIL loop"); return(0)));
          if (dv != oo && dv % 2 == 1 && dv < 12 && v + dv < 18,
            my(S = nfeltdiv(nf, nfeltadd(nf, s0, -1), pi), Z = nfeltdiv(nf, nfeltadd(nf, nfeltdiv(nf, D, nfeltpow(nf, pi, dv)), -1), pi));
            if (!isintv(S) || !isintv(Z), print("FAIL S Z integral"); return(0));
            if (nfislocalpower(nf, pr, nfeltmul(nf, q, Gs[kx]), 2), print("FAIL: defect certificate on a local square"); return(0));
            c = [1, i - 1, v / 2, dv, S, Z]; sz = max(maxd(S), maxd(Z));
            if (sz < bsz, best = c; bsz = sz))));
      if (best == 0, print("NO CERTIFICATE P = ", P, " k = ", [5, 7][kx]); return(0));
      out[n][kx] = best));
  print("all ", 2 * #pts, " leaves certified; kinds: odd ", sum(n = 1, #pts, sum(kx = 1, 2, out[n][kx][1] == 0)), ", defect ", sum(n = 1, #pts, sum(kx = 1, 2, out[n][kx][1] == 1)));
  print("max digits: G' ", maxd(concat(Gp[1], Gp[2])), ", H ", maxd(concat(Hs[1], Hs[2])), ", T12 T13 ", maxd(concat(T12, T13)),
    ", leaves ", vecmax(vector(#pts, n, vecmax(vector(2, kx, my(c = out[n][kx]); if (c[1] == 0, maxd(c[4]), max(maxd(c[5]), maxd(c[6]))))))));
  \\ Kronecker precisions (measured in Lean); nkk = [kG5, kG7, kT12, kT13, leaf precisions in the order of lcLeaves]
  nkk = 4 + 2 * #pts;
  kk = vector(nkk, t, 0);
  if (#externstr("ls sieve_2adic_precisions.gp 2>/dev/null") > 0, read("sieve_2adic_precisions.gp"); kk = lcK; if (#kk != nkk, print("FAIL #lcK"); return(0)));
  o = if (kk[1] == 0, "/tmp/m1w/lc_data.lean", Str(LEANDIR, "FurioLombardo/M1/Data2.lean"));
  system(Str("rm -f ", o));
  write1(o, "/-! Data of lane M1 (generated by code/descent/sieve_2adic_data.gp, PARI/GP): the local step at the prime `lc = gO 14`\nabove 2. Elements on PARI's integral basis (`zkE`). Rechecked by the kernel in Local2.lean. -/\n\nnamespace FurioLombardo.M1\n\nset_option maxRecDepth 100000\n\n/-- A leaf certificate: `odd i v kk T` (`Q_i(P) G' = π ^ v (1 + π T)`) or `dfc i j d kk S Z`\n(`Q_i(P) G' = π ^ (2 j) ((1 + π S) ^ 2 + π ^ d (1 + π Z))`); `kk` is the Kronecker precision. -/\ninductive LcCert : Type\n  | odd (i v kk : Nat) (T : List Int)\n  | dfc (i j d kk : Nat) (S Z : List Int)\n\n");
  write1(o, "/-- `(gO 12 - 1) / π` and `(gO 13 - 1) / π`. -/\ndef lcT12 : List Int := "); write1(o, lst(Vec(T12))); write1(o, "\n\n");
  write1(o, "def lcT13 : List Int := "); write1(o, lst(Vec(T13))); write1(o, "\n\n");
  write1(o, "/-- `G' = gProd (survE k) mod 8` for `k = 5, 7`. -/\ndef lcGp5 : List Int := "); write1(o, lst(Vec(Gp[1]))); write1(o, "\n\n");
  write1(o, "def lcGp7 : List Int := "); write1(o, lst(Vec(Gp[2]))); write1(o, "\n\n");
  write1(o, "/-- `H = (gProd (survE k) - G') / 8`. -/\ndef lcH5 : List Int := "); write1(o, lst(Vec(Hs[1]))); write1(o, "\n\n");
  write1(o, "def lcH7 : List Int := "); write1(o, lst(Vec(Hs[2]))); write1(o, "\n\n");
  write1(o, Str("/-- Kronecker precisions of the identities for `G` (k = 5, 7), `T12`, `T13`. -/\ndef lcKG : List Nat := ", lst(kk[1..4]), "\n\n"));
  write1(o, "/-- The leaves: `(P, cert for k = 5, cert for k = 7)`. -/\ndef lcLeaves : List (List Int × LcCert × LcCert) :=\n  [");
  for (n = 1, #pts,
    my(s = Str("(", lst(pts[n])));
    for (kx = 1, 2, my(c = out[n][kx], kn = kk[4 + 2 * (n - 1) + kx]);
      s = Str(s, ",\n    ", if (c[1] == 0, Str(".odd ", c[2], " ", c[3], " ", kn, " ", lst(Vec(c[4]))),
        Str(".dfc ", c[2], " ", c[3], " ", c[4], " ", kn, " ", lst(Vec(c[5])), " ", lst(Vec(c[6]))))));
    write1(o, Str(s, ")", if (n < #pts, ",\n  ", "]\n\n"))));
  write1(o, "end FurioLombardo.M1\n");
  print("written ", o);
  1;
}
main();
