\\ boxes_kat_random.gp: second known-answer test of the box covering (boxes.gp): random points of C(Q_2).
\\ For each twist and each of the five discs, random parameters X (modulo 2^20, plus points close to the known lifts
\\ and 12 points of the region R5 = disc 5, X odd): locate the unique box containing X and check its verdict at X:
\\ excluded boxes by the local square test of Q1/delta (or Q3/delta) at the stated place, constant boxes by nu and the
\\ leading class of lambda_at at X, tail boxes by nu = nu1 + v_2(X - X_i) and the class e1.
\\ Run from code/earlier-computations after boxes.gp: gp -q boxes_kat_random.gp
default(parisizemax, 5*10^9); default(nbthreads, 1);
BOXLIB = 1;
read("boxes.gp");
setrand(314159);
nfail = 0;
kat(c, msg) = if (!c, nfail++; print("KAT FAILED: ", msg));
startswith(s, p) = my(a = Vecsmall(s), b = Vecsmall(p)); #a >= #b && a[1 .. #b] == b;
lastnum(s) = my(a = Vecsmall(s), l = #a); while (a[l] != 32, l--); eval(Strchr(a[l + 1 .. #a]));
field(s, key) = {
  my(a = Vecsmall(s), b = Vecsmall(key), p = 0, e); for (i = 1, #a - #b + 1, if (a[i .. i + #b - 1] == b, p = i + #b; break));
  if (!p, return(oo)); e = p; while (e <= #a && a[e] != 44, e++); eval(Strchr(a[p .. e - 1]));
}
checkpt(k, B, kp, di, X1) = {
  my(bx = [b | b <- B, b[1] == di && (X1 - b[2]) % 2^b[3] == 0], b, vs);
  kat(#bx == 1, Str("point X = ", X1, " of disc ", di, " in exactly one box"));
  if (#bx != 1, return);
  b = bx[1]; vs = b[4];
  if (startswith(vs, "excluded"),
    my(ee = lastnum(vs), w = [ww | ww <- [1 .. #PR2], EW[ww] == ee][1], c1 = centre(di, X1), q1v = tayl(QC[DD[di][1]][1], c1[1], c1[2])[1], q3v = tayl(QC[DD[di][1]][3], c1[1], c1[2])[1]);
    kat(!nfislocalpower(nfK, PR2[w], lift(if (q1v != 0, q1v, q3v) / DL[k + 1]), 2), Str("excluded box ", b[1 .. 3], " at X = ", X1));
    printf("    k = %d, disc %d, X = %d: excluded box %s, non-square confirmed\n", k, di, X1, b[1 .. 3]); return);
  my(r1 = lambda_at(k, discpt(DISCS[di], X1)), nu, cl);
  if (startswith(vs, "constant"),
    nu = field(vs, "nu = "); cl = lam_centre(k, di, b[2])[3],
    my(p = [pp | pp <- kp, pp[3] == di && (pp[4] - b[2]) % 2^b[3] == 0][1], TT = [tt | tt <- TINY, tt[1] == p[1]][1],
       g0 = [Mod(TT[4][1], K21), Mod(TT[5][1], K21)] * 2^DD[di][4], pv = prc(k, g0), nu1 = v2vec(pv));
    if (X1 == p[4], printf("    k = %d, disc %d, X = %d: the known lift x_%d\n", k, di, X1, p[1]); return);
    nu = nu1 + valuation(X1 - p[4], 2); cl = apply(c -> c % 2, pv / 2^nu1)~);
  kat(r1[1] == "ok" && r1[2] == nu && r1[3] == cl && !r1[4], Str("box ", b[1 .. 3], " at X = ", X1, ": ", r1[1 .. min(4, #r1)], " against nu = ", nu, ", class ", cl));
  printf("    k = %d, disc %d, X = %d: %s box %s, nu = %s (predicted %d), class %s, in pr(W): %s\n", k, di, X1, if (startswith(vs, "tail"), "tail", "constant"), b[1 .. 3], r1[2], nu, r1[3], r1[4]);
}
{
for (k = 0, 1,
  my(B = readvec(Str("/tmp/k21c/m9e/boxes_k", k, ".txt")), kp = [p | p <- KP, p[2] == k], t0 = getabstime(), pts = List());
  for (di = 1, #DISCS, for (i = 1, 5, listput(pts, [di, random(2^20)])));
  foreach (kp, p, foreach ([3, 5, 8, 11], j, listput(pts, [p[3], p[4] + 2^j * (1 + 2 * random(2^8))])));
  if (k == 0, for (i = 1, 12, listput(pts, [5, 1 + 2 * random(2^19)])));
  printf("twist %d: %d random points\n", k, #pts);
  foreach (pts, pt, checkpt(k, B, kp, pt[1], pt[2]));
  printf("twist %d done (%d ms)\n", k, getabstime() - t0));
printf("RESULT: %s\n", if (nfail == 0, "all known-answer tests pass", Str(nfail, " FAILURES")));
}
quit;
