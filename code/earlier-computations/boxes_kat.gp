\\ boxes_kat.gp: known-answer tests for the box covering of boxes.gp (reads /tmp/k21c/m9e/boxes_k<k>.txt).
\\ (K1) Cauchy estimate: at each known lift x_i the exact coefficients of w = d lambda / dX (from the tiny series,
\\      g_n = 2^(k(n+1)) (w0_(n+1), w1_(n+1))) satisfy v_pi(g_n) + 3 n (s - 1) >= vM, where vM is the sup norm bound
\\      of supbound() on the disc of radius 2^-(s-1), for every level s <= 6 at which supbound succeeds.
\\ (K2) Taylor bound: at random points P of random boxes, v_w(q(P) - q(P0)) >= incr(w, Taylor data, k + s) for
\\      q = Q1, Q2, Q3 and the three places above 2.
\\ (K3) Exclusion: at random points of excluded boxes, Q1/delta (or Q3/delta) is a non-square at the stated place.
\\ (K4) Constancy: at a random point of randomly chosen constant boxes, nu and the leading class equal those of the
\\      box centre (lambda_at at the new point); in the tail boxes, nu = nu1 + j and the class is e1 at points with
\\      v_2(X - X_i) = j >= J0.
\\ Run from code/earlier-computations after boxes.gp: gp -q boxes_kat.gp
default(parisizemax, 5*10^9); default(nbthreads, 1);
BOXLIB = 1;
read("boxes.gp");
setrand(20260927);
nfail = 0;
kat(c, msg) = if (!c, nfail++; print("KAT FAILED: ", msg));
startswith(s, p) = my(a = Vecsmall(s), b = Vecsmall(p)); #a >= #b && a[1 .. #b] == b;
lastnum(s) = my(a = Vecsmall(s), l = #a); while (a[l] != 32, l--); eval(Strchr(a[l + 1 .. #a]));
{
for (k = 0, 1,
  my(B = readvec(Str("/tmp/k21c/m9e/boxes_k", k, ".txt")), kp = [p | p <- KP, p[2] == k], t0 = getabstime());
  printf("twist %d: %d boxes read\n", k, #B);
  \\ (K1)
  foreach (kp, p, my(TT = [tt | tt <- TINY, tt[1] == p[1]][1], kk = DD[p[3]][4], nchk = 0);
    for (s = 1, 6, my(vM = supbound(k, p[3], p[4], s));
      if (vM == oo, next);
      for (n = 0, #TT[4] - 1, my(g = [Mod(TT[4][n + 1], K21), Mod(TT[5][n + 1], K21)] * 2^(kk * (n + 1)), vg = min(vw(IV, g[1]), vw(IV, g[2])));
        kat(vg + 3 * n * (s - 1) >= vM, Str("Cauchy estimate at x_", p[1], ", s = ", s, ", n = ", n, ": ", vg + 3 * n * (s - 1), " < ", vM)); nchk++));
    printf("  (K1) x_%d: %d Cauchy inequalities checked\n", p[1], nchk));
  \\ (K2)
  my(nk2 = 0, nk3 = 0, ex = [b | b <- B, startswith(b[4], "excluded")]);
  for (i = 1, 12, my(b = B[random(#B) + 1], di = b[1], s = b[3], X1 = b[2] + 2^s * random(2^10), c0 = centre(di, b[2]), c1 = centre(di, X1));
    for (j = 1, 3, my(q = QC[DD[di][1]][j], T = tayl(q, c0[1], c0[2]), q1 = tayl(q, c1[1], c1[2])[1]);
      for (w = 1, #PR2, kat(vw(w, q1 - T[1]) >= incr(w, T, DD[di][4] + s), Str("Taylor bound, box ", b[1 .. 3], ", q = Q", j, ", place ", w)); nk2++)));
  \\ (K3)
  for (i = 1, min(10, #ex), my(b = ex[random(#ex) + 1], di = b[1], s = b[3], X1 = b[2] + 2^s * random(2^10), c1 = centre(di, X1), ee = lastnum(b[4]), w, q1v, q3v, a);
    w = [ww | ww <- [1 .. #PR2], EW[ww] == ee][1];
    q1v = tayl(QC[DD[di][1]][1], c1[1], c1[2])[1]; q3v = tayl(QC[DD[di][1]][3], c1[1], c1[2])[1];
    a = if (q1v != 0, q1v, q3v) / DL[k + 1];
    kat(!nfislocalpower(nfK, PR2[w], lift(a), 2), Str("exclusion at a random point of box ", b[1 .. 3])); nk3++);
  printf("  (K2) %d Taylor bounds checked; (K3) %d exclusions checked\n", nk2, nk3);
  \\ (K4)
  my(cb = [b | b <- B, startswith(b[4], "constant")], tb = [b | b <- B, startswith(b[4], "tail")], nk4 = 0);
  for (i = 1, min(8, #cb), my(b = cb[random(#cb) + 1], di = b[1], s = b[3], X1 = b[2] + 2^s * (1 + 2 * random(2^8)), r0 = lam_centre(k, di, b[2]), r1 = lambda_at(k, discpt(DISCS[di], X1)));
    kat(r1[1] == "ok" && r1[2] == r0[2] && r1[3] == r0[3], Str("constancy in box ", b[1 .. 3], " at X = ", X1, ": ", r1[1 .. min(3, #r1)], " against ", r0[1 .. 3]));
    printf("    box %s: centre nu = %d, point X = %d: nu = %s, class %s\n", b[1 .. 3], r0[2], X1, r1[2], r1[3]); nk4++);
  foreach (tb, b, my(di = b[1], J0 = b[3], p = [pp | pp <- kp, pp[3] == di && (pp[4] - b[2]) % 2^J0 == 0][1], TT = [tt | tt <- TINY, tt[1] == p[1]][1],
      g0 = [Mod(TT[4][1], K21), Mod(TT[5][1], K21)] * 2^DD[di][4], pv = prc(k, g0), nu1 = v2vec(pv), e1 = apply(c -> c % 2, pv / 2^nu1));
    foreach ([J0, J0 + 1, J0 + 3], j, my(X1 = p[4] + 2^j * (1 + 2 * random(2^6)), r1 = lambda_at(k, discpt(DISCS[di], X1)));
      kat(r1[1] == "ok" && r1[2] == nu1 + j && r1[3] == e1~, Str("tail at x_", p[1], ", j = ", j, ": ", r1[1 .. min(3, #r1)], " against nu = ", nu1 + j, ", class ", e1~));
      printf("    tail at x_%d, j = %d: nu = %s (expected %d)\n", p[1], j, r1[2], nu1 + j); nk4++));
  printf("  (K4) %d points checked (%d ms)\n", nk4, getabstime() - t0));
printf("RESULT: %s\n", if (nfail == 0, "all known-answer tests pass", Str(nfail, " FAILURES")));
}
quit;
