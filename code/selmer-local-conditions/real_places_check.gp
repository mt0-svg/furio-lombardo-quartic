\\ real_places_check.gp: independent recomputation of the real place claims
\\ ("Real places, no count needed") for f = fRev k, k = 0, 1, at the three real places of K21.
\\ Data read from the Lean sources (the definitions that will be frozen): K21 = Q[b]/(fL) (M1/Basic.lean),
\\ zk basis zkNum / Dz (M1/DataField.lean), FnData, qData, hData, qDen, hDen (Discharge/M3a/DataBruin.lean), with
\\ fRev k = (1/4) sum_j FE k (6 - j) X^j, q k, h k monic, c k = FE k 0 / 4 (Discharge/M3a/ConcreteDefs.lean).
\\ Exact parts: signs of elements of K21 at a real root beta_i of fL are decided on a rational isolating interval of
\\ beta_i (polsturm: one root of fL, no root of the element's representative), so every sign below is exact; real
\\ root counts of q (disc sign) and h (disc sign of a quartic); location and origin of the four real roots of fRev by
\\ exact signs of fRev, q, h at rational separators. Numerical parts (200 digits, margins printed): the x - T sign
\\ vectors of sample classes of each type of the case analysis, and the comparison with the stored local images of
\\ p21_29 (code/local-group/selmer_injectivity_places_twist<k>.bin, /tmp/k21c/sel/fields.bin).
\\ Run from code/selmer-local-conditions: gp -q real_places_check.gp < /dev/null > real_places_check.out
[x, t, b];
default(parisizemax, 900 * 10^6);
default(realprecision, 200);
default(nbthreads, 1);
NF = 0;
chq(c, msg) = if (c, printf("ok: %s\n", msg), NF++; printf("CHECK FAILED: %s\n", msg));
LEAN = "../../FurioLombardo/";
startswith(s, p) = my(A = Vecsmall(s), B = Vecsmall(p)); #A >= #B && A[1 .. #B] == B;
isblank(s) = my(A = Vecsmall(s)); #[c | c <- A, c != 32 && c != 9] == 0;
\\ the value of a Lean `def nm ... := <list>`: text after ":=" on the def line and the next lines up to a blank line
getdef(fn, nm) = {
  my(L = readstr(fn), pre = Str("def ", nm, " "), acc = "", on = 0);
  for (i = 1, #L, my(s = L[i]);
    if (!on,
      if (startswith(s, pre), on = 1; my(A = Vecsmall(s), p = 0);
        for (j = 1, #A - 1, if (A[j] == 58 && A[j + 1] == 61, p = j; break));
        if (p == 0, error("no := in ", s)); acc = Strchr(A[p + 2 .. #A])),
      if (isblank(s) || startswith(s, "/-") || startswith(s, "def ") || startswith(s, "theorem"), break);
      acc = Str(acc, s)));
  if (!on, error("no def ", nm, " in ", fn));
  eval(acc);
}
fL = getdef(Str(LEAN, "M1/Basic.lean"), "fL");
Dz = getdef(Str(LEAN, "M1/DataField.lean"), "Dz");
zkNum = getdef(Str(LEAN, "M1/DataField.lean"), "zkNum");
FnData = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "FnData");
qData = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qData");
hData = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hData");
qDen = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qDen");
hDen = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hDen");
{chq(#fL == 22 && fL[22] == 1 && #zkNum == 21 && #FnData == 2 && #FnData[1] == 7 && #FnData[2] == 7 && #qData[1] == 2 && #hData[1] == 4,
    "Lean data parsed: fL (22 coefficients, monic), zkNum (21), FnData (2 x 7), qData, hData");}
fZ = Pol(Vecrev(fL), 'b);
{chq(fZ == b^21 - 7*b^20 + 14*b^19 - 84*b^16 + 98*b^15 + 2*b^14 + 175*b^13 - 609*b^12 + 980*b^11 - 770*b^10 - 280*b^9 + 1008*b^8 - 1072*b^7 + 560*b^6 + 28*b^5 - 336*b^4 + 252*b^3 - 112*b^2 + 28*b - 4,
    "fL is the polynomial fZ of M1/Basic.lean");}
chq(polisirreducible(fZ), "fZ irreducible");
W = vector(21, j, Pol(Vecrev(zkNum[j]), 'b) / Dz);
zkE(a) = Mod(sum(j = 1, 21, a[j] * W[j]), fZ);
\\ fRev k, f_k (unreversed), q k, h k, c k (k = 0, 1 as index k + 1)
fRevK = vector(2, k, sum(j = 0, 6, zkE(FnData[k][7 - j]) / 4 * 'x^j));
fK = vector(2, k, sum(j = 0, 6, zkE(FnData[k][j + 1]) / 4 * 'x^j));
qK = vector(2, k, 'x^2 + zkE(qData[k][2]) / qDen[k] * 'x + zkE(qData[k][1]) / qDen[k]);
hK = vector(2, k, 'x^4 + sum(j = 0, 3, zkE(hData[k][j + 1]) / hDen[k] * 'x^j));
cK = vector(2, k, zkE(FnData[k][1]) / 4);
{for (k = 1, 2,
  chq(fRevK[k] == cK[k] * qK[k] * hK[k], Str("twist ", k - 1, ": fRev = c q h exactly over K21"));
  chq(pollead(fRevK[k]) == cK[k], Str("twist ", k - 1, ": lc(fRev) = c"));
  chq(poldegree(fRevK[k]) == 6 && poldisc(fRevK[k]) != 0, Str("twist ", k - 1, ": degree 6, disc != 0 (squarefree)")));}
\\ cross-check with the PARI definitions bruin_form.gp (F0, F1 in t over Q[b])
read("../earlier-computations/bruin_form.gp");
chq(K21 == fZ, "K21 of bruin_form.gp = fZ");
chq(fK[1] == Mod(1, fZ) * subst(F0, 't, 'x) && fK[2] == Mod(1, fZ) * subst(F1, 't, 'x), "f_k of the Lean data = F0, F1 of bruin_form.gp");
\\ ---------------------------------------------------------------- exact signs at the real places
RT = polrootsreal(fZ);
chq(#RT == 3, "K21 has exactly 3 real embeddings (polrootsreal, sorted increasingly)");
\\ rational isolating intervals, refined by bisection
ISO = vector(3, i, my(lo = floor(RT[i] * 10^30) / 10^30, hi = lo + 1 / 10^30); [lo, hi]);
for (i = 1, 3, chq(polsturm(fZ, ISO[i]) == 1 && subst(fZ, 'b, ISO[i][1]) * subst(fZ, 'b, ISO[i][2]) < 0, Str("isolating interval of beta_", i)));
\\ exact sign of an element g of K21 at beta_i
sgnK(g, i) = {
  my(G = lift(Mod(1, fZ) * g), I = ISO[i]);
  if (G == 0, error("sgnK: zero element"));
  if (type(G) != "t_POL", return(sign(G)));
  while (polsturm(G, I) > 0,
    my(m = (I[1] + I[2]) / 2); if (subst(fZ, 'b, m) == 0, error("rational root of fZ"));
    I = if (subst(fZ, 'b, I[1]) * subst(fZ, 'b, m) < 0, [I[1], m], [m, I[2]]));
  sign(subst(G, 'b, I[1]));
}
chq(sgnK(Mod(b, fZ) - floor(RT[1]) , 1) == sign(RT[1] - floor(RT[1])) && sgnK(-1 + 0 * b, 2) == -1, "sgnK on known values");
\\ the numerical embedding (200 digits)
embC(g, i) = subst(lift(Mod(1, fZ) * g), 'b, RT[i]);
embP(P, i) = Pol(apply(c -> embC(c, i), Vec(P)), 'x);
\\ nf.roots order of nfinit (the numbering of places 5, 6, 7 in selmer_bound_subsets / p21_29): real roots first, increasing
{
  my(nfK = nfinit([fZ, 10]));
  chq(nfK.pol == fZ && nfK.r1 == 3 && vecmax(vector(3, i, abs(nfK.roots[i] - RT[i]))) < 10^-30, "nfinit(K21).roots[1..3] = the sorted real roots (place 4 + i = beta_i)");
}
\\ exact sign of a polynomial over K21 evaluated at a rational s, at beta_i
sgnAt(P, s, i) = sgnK(subst(P, 'x, s), i);
WR = [[1, 1, 1, 1], [1, -1, -1, 1], [-1, 1, 1, -1], [-1, -1, -1, -1]];
inWR(sv) = setsearch(Set(WR), sv) > 0;
\\ sign vector (at the sorted real roots rr) of the class of a real polynomial P evaluated at T, margins recorded
MARG = 10^10;
sv(P, rr) = vector(4, j, my(z = subst(P, 'x, rr[j])); MARG = min(MARG, abs(z)); sign(z));
\\ numeric real roots of a real polynomial, sorted, and the complex ones
rrts(P) = my(Z = polroots(P), R = List(), C = List()); foreach (Z, z, if (abs(imag(z)) < 10^-100, listput(R, real(z)), listput(C, z))); [vecsort(Vec(R)), Vec(C)];
{
  for (k = 1, 2, for (i = 1, 3,
    my(f = fRevK[k], q = qK[k], h = hK[k], lcs = sgnK(cK[k], i), dq = sgnK(poldisc(q), i), dh = sgnK(poldisc(h), i), fR, qR, hR, rr, cr, seps, sf, sq, sh, orig, lck);
    printf("==== twist %d, real place %d (beta_%d = %.12f)\n", k - 1, 4 + i, i, RT[i]);
    lck = sgnK(pollead(fK[k]), i);
    printf("  sign lc(fRev) = %d, sign lc(f_k) (unreversed model) = %d, sign disc(q) = %d, sign disc(h) = %d, sign f_k(0) = %d\n", lcs, lck, dq, dh, sgnK(polcoef(fK[k], 0), i));
    chq(dq == 1 && dh == -1, "q has exactly 2 real roots (disc > 0), h exactly 2 (quartic with disc < 0)");
    fR = embP(f, i); qR = embP(q, i); hR = embP(h, i);
    [rr, cr] = rrts(fR);
    chq(#rr == 4 && #cr == 2, "numerically 4 real roots and one complex pair");
    printf("  real roots r1..r4 of fRev: %s\n  complex pair: %s\n", apply(z -> precision(z, 20), rr), apply(z -> precision(z, 20), cr));
    \\ rational separators s0 < r1 < s1 < r2 < s2 < r3 < s3 < r4 < s4
    seps = vector(5, j, if (j == 1, floor(rr[1]) - 1, if (j == 5, ceil(rr[4]) + 1, bestappr((rr[j - 1] + rr[j]) / 2, 10^6))));
    chq(vecsort(seps) == seps && vecmin(vector(4, j, min(rr[j] - seps[j], seps[j + 1] - rr[j]))) > 0, "separators interlace the numeric roots");
    sf = vector(5, j, sgnAt(f, seps[j], i)); sq = vector(5, j, sgnAt(q, seps[j], i)); sh = vector(5, j, sgnAt(h, seps[j], i));
    printf("  separators %s\n  exact signs at the separators: fRev %s, q %s, h %s\n", seps, sf, sq, sh);
    orig = vector(4, j, if (sq[j] != sq[j + 1] && sh[j] == sh[j + 1], "q", if (sh[j] != sh[j + 1] && sq[j] == sq[j + 1], "h", "?")));
    chq(#[o | o <- orig, o == "q"] == 2 && #[o | o <- orig, o == "h"] == 2,
        "exact: each interval (s_(j-1), s_j) holds one sign change of exactly one of q, h; two for q, two for h (so exactly one root per interval)");
    printf("  origin of r1..r4 (exact): %s\n", orig);
    if (lcs == -1,
      chq(sf == [-1, 1, -1, 1, -1], "exact: lc < 0 and fRev < 0, > 0, < 0, > 0, < 0 at s0..s4: f > 0 exactly on (r1, r2), (r3, r4)"),
      chq(sf == [1, -1, 1, -1, 1], "exact: lc > 0 and fRev > 0, < 0, > 0, < 0, > 0 at s0..s4: f > 0 exactly on (-oo, r1), (r2, r3), (r4, oo)");
      printf("  lc(fRev) > 0 here: GoodSextic (fRev k).map sigma fails (lc a square in R), the Lean Jac is not A(R) and W_r does not apply\n"));
    \\ the x - T image, case by case (computed where lc < 0)
    if (lcs == -1,
      my(p1 = (rr[1] + rr[2]) / 2, p2 = (rr[3] + rr[4]) / 2, tors = List(), pts, imgs = List(), fd = deriv(fR), rho);
      MARG = 10^10;
      chq(sv(p1 - 'x, rr) == [1, -1, -1, -1] && sv(p2 - 'x, rr) == [1, 1, 1, -1], "x - T at a point of (r1, r2) is (+,-,-,-), at a point of (r3, r4) is (+,+,+,-)");
      \\ (B) u coprime to f: two real points (sampled on both ovals), a double point, an irreducible u
      pts = concat(vector(3, t, rr[1] + (rr[2] - rr[1]) * t / 4), vector(3, t, rr[3] + (rr[4] - rr[3]) * t / 4));
      for (a = 1, 6, for (c = a, 6, my(u = ('x - pts[a]) * ('x - pts[c]), s = sv(u, rr)); listput(imgs, s); chq(inWR(s), Str("(B) u = (x - a)(x - b), a, b = points ", a, ", ", c, ": ", s, " in W_r"))));
      chq(inWR(sv('x^2 + 1, rr)) && inWR(sv(('x - rr[1] - 1/3)^2 + 1/5, rr)), "(B) u irreducible over R: trivial sign vector, in W_r");
      \\ (C) u | f (2-torsion): muJ_Tpt gives [(u - f/u)(T)]; the six real pairs and the complex pair rho
      rho = ('x - cr[1]) * ('x - cr[2]); rho = Pol(apply(real, Vec(rho)), 'x);
      my(divs = concat(vector(6, t, my(pr = [[1,2],[1,3],[1,4],[2,3],[2,4],[3,4]][t]); ('x - rr[pr[1]]) * ('x - rr[pr[2]])), [rho]));
      foreach (divs, u, my(dr = divrem(fR, u), r = dr[1], s = sv(u - r, rr)); chq(vecmax(apply(abs, Vec(dr[2]))) < 10^-150, "(C) u divides f"); listput(imgs, s); chq(inWR(s), Str("(C) u | f, u roots ", apply(z -> precision(z, 6), polroots(u)), ": muJ_Tpt sign vector ", s, " in W_r")));
      \\ (D) u = (x - r_i)(x - b), b on an oval: one Cantor step [<u, Y - v>] = [<w, Y + v>], w = (v^2 - f)/u (degree 4, coprime to f)
      for (ii = 1, 4, foreach ([pts[2], pts[5]], bb,
        my(u = ('x - rr[ii]) * ('x - bb), yb = sqrt(subst(fR, 'x, bb)), v = yb * ('x - rr[ii]) / (bb - rr[ii]), num = v^2 - fR, dv = divrem(num, u), w = dv[1], s, pred);
        chq(abs(subst(num, 'x, rr[ii])) < 10^-150 && vecmax(apply(abs, Vec(dv[2]))) < 10^-150 && poldegree(w) == 4, Str("(D) i = ", ii, ", b = ", precision(bb, 6), ": u | v^2 - f, w of degree 4"));
        chq(vecmin(apply(z -> abs(subst(w, 'x, z)), concat(rr, cr))) > 10^-20, "(D) w coprime to f (nonzero at the six roots)");
        s = sv(w, rr); listput(imgs, s);
        pred = vector(4, j, if (j == ii, -sign(subst(fd, 'x, rr[ii])) * sign(rr[ii] - bb), sign(subst(u, 'x, rr[j]))));
        chq(s == pred, Str("(D) sign vector ", s, " = the predicted (sgn u(r_j), j != i; -sgn f'(r_i) sgn(r_i - b) at i)"));
        chq(inWR(s), "(D) in W_r"));
        );
      chq(vector(4, j, sign(subst(fd, 'x, rr[j]))) == [1, -1, 1, -1], "f'(r1..r4) signs (+,-,+,-)");
      my(img = Set(apply(s -> if (s[1] < 0, -s, s), Vec(imgs))));
      printf("  image of the sampled classes modulo the diagonal: %s; smallest |value| used %.3e\n", img, MARG);
      chq(img == Set([[1, 1, 1, 1], [1, -1, -1, 1]]), "the sampled classes fill W_r modulo the diagonal (dimension 1)"));
    );
  );
}
\\ negative controls: the membership test rejects the other pairings, and for -fRev (lc > 0, the twist by -1) the
\\ points of the two ovals (-oo, r1) u (r4, oo) and (r2, r3) give a class outside W_r
{
  chq(!inWR([1, -1, 1, -1]) && !inWR([1, 1, -1, -1]) && !inWR([1, 1, 1, -1]), "negative control: inWR rejects (+,-,+,-), (+,+,-,-), (+,+,+,-)");
  my(rr = rrts(embP(fRevK[1], 1))[1], a = (rr[2] + rr[3]) / 2, c = rr[4] + 1, s = sv(('x - a) * ('x - c), rr));
  chq(subst(-embP(fRevK[1], 1), 'x, a) > 0 && subst(-embP(fRevK[1], 1), 'x, c) > 0 && !inWR(s),
      Str("negative control: for -fRev at place 5, the pair of points over ", precision(a, 6), " and ", precision(c, 6), " has sign vector ", s, ", outside W_r"));
}
\\ ---------------------------------------------------------------- comparison with the stored local images of p21_29
\\ coordinates at a real place (sel_realcoord): signs (1 = negative) at the real embeddings of L (root thL of G1) above
\\ beta_i, then of N (root thN of h), in increasing embedding index; W_w (4 x 2 over F2) from selmer_injectivity_places_twist<k>.bin.
\\ The x - T classes of fRev (root r) and f_k (root theta) correspond through r = 1/theta, so the partition of the four
\\ real roots given by W_w, carried to r = 1/theta and sorted, must be {r1, r4} | {r2, r3} where lc(fRev) < 0.
{
  my(FF = read("/tmp/k21c/sel/fields.bin"), nfK = FF[1], nfL = FF[2], nfN = FF[3], aL = FF[4], thL = FF[5], aN = FF[6], thN = FF[7]); my(eL = nfeltembed(nfL, aL), eN = nfeltembed(nfN, aN), tL = nfeltembed(nfL, thL), tN = nfeltembed(nfN, thN));
  chq(subst(nfK.pol, variable(nfK.pol), 'b) == fZ, "fields.bin: nfK.pol = fZ (binary files keep variable numbers, not names)");
  for (k = 1, 2,
    my(D = read(Str("../local-group/selmer_injectivity_places_twist", k - 1, ".bin")), locs = D[3], offs = D[2]);
    for (i = 1, 3,
      my(jsL, jsN, th, Wm, e, A, rr, rinv, idx, lcs);
      jsL = [j | j <- [1 .. nfL.r1], abs(eL[j] - RT[i]) < 10^-20]; jsN = [j | j <- [1 .. nfN.r1], abs(eN[j] - RT[i]) < 10^-20];
      chq(#jsL == 2 && #jsN == 2, Str("twist ", k - 1, ", place ", 4 + i, ": two real embeddings of L and of N above beta_", i));
      th = concat(vector(2, t, real(tL[jsL[t]])), vector(2, t, real(tN[jsN[t]])));
      Wm = Mod(locs[4 + i], 2);
      chq(matsize(Wm) == [4, 2] && matrank(Wm) == 2 && matrank(matconcat([Wm, Mod([1, 1, 1, 1]~, 2)])) == 2, "W_w has dimension 2 and contains the diagonal (the image of R^x)");
      e = 0; for (c = 1, 2, my(col = lift(Wm[, c])); if (col != [0,0,0,0]~ && col != [1,1,1,1]~, e = col));
      if (e == 0, e = lift(Wm[, 1] + Wm[, 2]));
      A = [j | j <- [1 .. 4], e[j] == 1];
      chq(#A == 2, "the non-diagonal class of W_w has weight 2 (a partition into two pairs)");
      rr = rrts(embP(fRevK[k], i))[1]; rinv = apply(t -> 1 / t, th);
      idx = vector(4, j, my(d = vector(4, l, abs(rinv[j] - rr[l])), m = vecmin(d)); [l | l <- [1 .. 4], d[l] == m][1]);
      chq(vecsort(idx) == [1, 2, 3, 4] && vecmax(vector(4, j, abs(rinv[j] - rr[idx[j]]))) < 10^-30, "1/theta at the L, N embeddings are the four real roots of fRev");
      lcs = sgnK(cK[k], i);
      printf("  twist %d, place %d: coordinates (L, L, N, N) are the roots r_%s of fRev; W_w pair %s = {r_%d, r_%d}; sign lc(fRev) = %d\n",
             k - 1, 4 + i, idx, A, idx[A[1]], idx[A[2]], lcs);
      my(P = Set([idx[A[1]], idx[A[2]]]));
      if (lcs == -1,
        chq(P == [2, 3] || P == [1, 4], "lc < 0: the p21_29 local image is W_r = {sgn(r1) = sgn(r4), sgn(r2) = sgn(r3)}"),
        chq(P == [1, 2] || P == [3, 4], "lc > 0: the p21_29 local image pairs {r1, r2} | {r3, r4} (not W_r)"))));
}
printf("DONE, %d failed checks\n", NF);
quit;
