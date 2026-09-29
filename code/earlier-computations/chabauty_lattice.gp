\\ chabauty_lattice.gp: Selmer group Chabauty at the place v of K21 above 2 with e = 3, for both twists.
\\ Lambda = log J(K_v) (logarithm for (dx/y, x dx/y) on F_k, genus2_log_kv.gp) as a Z_2-lattice in K_v^2 = Q_2^6
\\ (coordinates on the Z_2-basis 1, pi, pi^2 of O_v). Since D_1..D_7 (local_images_twist<k>_e3.bin) span J(K_v)/2J(K_v),
\\ they generate J(K_v) (x) Z_2 (Nakayama), so Lambda is the Z_2-span of log D_1..log D_7. The kernel of log on
\\ J(K_v) (x) Z_2 is <T> (J(K_v)[2^oo] = Z/2 T: T is not in 2J(K_v) since sigma_v is injective and T is in Sel), so
\\ rho : J(K_v)/2J(K_v) -> Lambda/2Lambda (induced by log) is onto with kernel <T>.
\\ Outputs per twist: W = rho(sigma_v(Sel)) (expected dimension 3), W_G = rho(Gamma) for Gamma = <T, phi_a, phi_b, R>,
\\ 2R = phi_a + phi_b, the saturation Gsat of Z_2 log Gamma in Lambda and the test (ii) image(Gsat) meet W inside W_G,
\\ the class w0 spanning the image of W in (Lambda/Gsat)/2, and for the tiny integral lambda(tau) = sum c_m tau^m of
\\ phi at x_a, x_b (pullback_known_lifts.gp, tau = x - x(P_i) in Q_2) the class e1 of the primitive vector along pr(c_1), with
\\ the valuations of pr(c_m) (m <= 24) that decide from which v(tau) on the linear term gives the leading class.
\\ Known answer tests: log of the T-combination of the D_i lies in 2 Lambda; rho(phi_a) computed from the logarithm
\\ equals rho of its x - T class (selmer_image_v.gp); log phi_a, log phi_b lie in Lambda; (log phi_a + log phi_b)/2 lies in
\\ Lambda; W_G is inside W; precision: everything is recomputed at two working precisions.
\\ Saves SEL/lattice_k<k>.bin (a Map: W, W_G, rho(D_i), H (HNF basis of Lambda), U (pr = rows of U v outside nzr), prW, Gsat, logs).
\\ Run from code/earlier-computations: gp -q chabauty_lattice.gp > chabauty_lattice.out
default(parisizemax, 5*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp"); read("phi_known_lifts.gp"); read("pullback_known_lifts.gp");
read("../lib/richelot.gp"); read("../lib/td2loc.gp");
chq(c, msg) = if (!c, error("check failed: ", msg));
MRED = 300;
read("genus2_log_kv.gp");
SEL = "/tmp/k21c/sel/";
nfK = nfinit([K21, [2, 7]]);
pr = [q | q <- idealprimedec(nfK, 2), q.e == 3][1];
NM = 4 * 3^2 * 5 * 7 * 11 * 13;
\\ a uniformizer at pr
findpi() = {
  my(g = nfbasistoalg(nfK, pr.gen[2]));
  if (nfeltval(nfK, g, pr) == 1, return(g));
  for (i = 1, 500, my(h = nfbasistoalg(nfK, random(vectorv(21, j, 3)) - vectorv(21, j, 1))); if (nfeltval(nfK, h, pr) == 1, return(h)));
  error("no uniformizer found");
}
PI = findpi();
chq(nfeltval(nfK, PI, pr) == 1, "PI is a uniformizer at pr");
\\ Q_2-coordinates of a in K_v on 1, pi, pi^2, to 2-adic precision P (digits c_{q,r} 2^q pi^r, valuations 3q + r distinct)
qcoords(a, P) = {
  my(c = [0, 0, 0], rem = a, m, q, r, pw = [1, PI, PI^2], mold = -oo);
  while (rem != 0 && (m = kval(LV, rem)) < 3 * P,
    chq(m > mold, "qcoords: valuation increases"); mold = m;
    q = m \ 3; r = m % 3; c[r + 1] += 2^q; rem = redK(LV, rem - 2^q * pw[r + 1]));
  apply(ci -> if (denominator(ci) == 1, ci % 2^P, ci), c);
}
logvec(l, P) = concat(qcoords(l[1], P), qcoords(l[2], P))~;
f2rank(M) = matrank(Mod(M, 2));
f2in(W, v) = f2rank(matconcat([W, v])) == f2rank(W);
v2(x) = if (x == 0, oo, valuation(x, 2));
v2vec(v) = vecmin(apply(v2, Vec(v)));
run(k, mred, P, a2) = {
  my(t0 = getabstime(), f, R, Ds, Ls, M, H, Hi, RhoD, rho, SC, KC, W, dW, phis, La, Lb, ya, yb, yR, WG, res = Map());
  MRED = mred; LV = td2_lvinit(nfK, pr, 150, 60); mapput(LV, "IM", idealpow(nfK, pr, MRED));
  f = subst(if (k == 0, F0, F1), t, 'x) * Mod(1, K21);
  R = read(Str("local_images_twist", k, "_e3.bin"));
  Ds = apply(dv -> j2_refine(LV, f, [td2_Kx(nfK, dv[1]), td2_Kx(nfK, dv[2])]), R[7]);
  Ls = vector(#Ds, i, j2_log(LV, f, Ds[i], 2^a2 * NM, 800));
  M = Mat(vector(#Ls, i, logvec(Ls[i], P)));
  H = mathnf(matconcat([M, 2^P * matid(6)]));
  printf("k = %d (MRED %d, P %d, a %d): Lambda = HNF with diagonal 2-valuations %s (%d ms)\n", k, mred, P, a2, vector(6, i, v2(H[i, i])), getabstime() - t0);
  chq(vecmax(vector(6, i, v2(H[i, i]))) < P - 20, "Lambda contains 2^(P-20) Z_2^6: the truncation modulo 2^P is harmless");
  Hi = H^-1;
  rho = (v -> my(c = Hi * v); chq(denominator(c) % 2 == 1, "vector in Lambda"); c);
  RhoD = Mat(vector(#Ls, i, rho(M[, i]))) % 2;
  chq(f2rank(RhoD) == 6, "rho is onto Lambda/2Lambda");
  my(S = read(Str(SEL, "rho_k", k, ".bin"))); SC = S[2]; KC = S[3];
  chq(RhoD * KC[, 1] % 2 == 0, "KAT: rho(T) = 0 (the T combination of the D_i has logarithm in 2 Lambda)");
  W = lift(matimage(Mod(RhoD * SC, 2))); dW = #W;
  printf("  dim W = rho(sigma_v(Sel)) = %d\n", dW);
  \\ known points
  phis = [ph | ph <- PHI, ph[2] == k];
  my(Lphi = vector(2, j, my(U = subst(phis[j][4], t, 'x) * Mod(1, K21), V = subst(phis[j][5], t, 'x) * Mod(1, K21), uu, vv);
      uu = U / pollead(U); vv = V % uu; chq((vv^2 - f) % uu == 0, "phi(x_i) = [U, V] is a point of Jac(F_k)(K21)");
      j2_log(LV, f, [uu, vv], 2^a2 * NM, 800)));
  La = Lphi[1]; Lb = Lphi[2];
  ya = rho(logvec(La, P)); yb = rho(logvec(Lb, P));
  chq(ya % 2 == RhoD * KC[, 2] % 2, "KAT: rho(phi_a) from the logarithm = from the x - T class");
  chq(yb % 2 == RhoD * KC[, 3] % 2, "KAT: rho(phi_b) from the logarithm = from the x - T class");
  chq((ya + yb) % 2 == 0, "KAT: (log phi_a + log phi_b)/2 in Lambda");
  yR = (ya + yb) / 2;
  WG = lift(matimage(Mod(matconcat([ya, yR]), 2)));
  chq(f2in(W, WG), "KAT: W_Gamma inside W");
  printf("  x_%d, x_%d: coordinates in Lambda (2-valuations) %s, %s; dim W_Gamma = %d\n", phis[1][1], phis[2][1], v2vec(ya), v2vec(yb), #WG);
  \\ saturation of Z_2 ya + Z_2 yR in Z_2^6 (Lambda coordinates): U M2 V = diag, Gsat = first two columns of U^-1
  my(M2 = matconcat([ya, yR]), sn = matsnf(M2, 1), U = sn[1], Ui = U^-1, dd = sn[3], Gs, Gs2, dcap, prW, w0);
  printf("  elementary divisors of <log phi_a, log R> in Lambda: 2-valuations %s\n", apply(v2, vector(2, i, dd[#dd~ - 2 + i, i])));
  \\ matsnf puts the diagonal in the last rows; locate the two nonzero rows
  my(nzr = [i | i <- [1 .. 6], vecmax(apply(abs, Vec(dd[i, ]))) != 0]);
  chq(#nzr == 2, "rank 2");
  Gs = matconcat([Ui[, nzr[1]], Ui[, nzr[2]]]);
  Gs2 = lift(matimage(Mod(Gs, 2)));
  dcap = #Gs2 + dW - f2rank(matconcat([Gs2, W]));
  printf("  (ii) for Gamma: dim(image(Gsat) meet W) = %d, dim W_Gamma = %d: %s\n", dcap, #WG, if (dcap == #WG, "PASS", "FAIL"));
  \\ halving: a combination alpha phi_a + beta R (+ eps T) lies in 2J(K_v), hence in 2J(K21) (sigma_v is injective on
  \\ Sel), so Gamma' = Gamma + <its half> is a subgroup of J(K21); after saturation log Gamma' = Gsat and W_Gamma' =
  \\ image(Gsat). KAT: W_Gamma' inside W (the classes of the halves are Selmer classes).
  my(hk = lift(matker(Mod(M2, 2))));
  printf("  halvings: combinations (alpha, beta) of (phi_a, R) in 2J(K_v) + <T>: %s\n", if (#hk, hk~, "none"));
  chq(f2in(W, Gs2), "KAT: image(Gsat) inside W (the halved classes are Selmer classes)");
  printf("  (ii) for the saturated Gamma': dim W_Gamma' = %d, image(Gsat) meet W = W_Gamma': PASS\n", #Gs2);
  \\ pr : Lambda -> Lambda / Gsat = Z_2^4, coordinates U v without the rows nzr
  my(orow = [i | i <- [1 .. 6], i != nzr[1] && i != nzr[2]], prj = (v -> my(c = U * v); vector(4, i, c[orow[i]])~));
  prW = lift(matimage(Mod(Mat(vector(dW, j, prj(W[, j]))), 2)));
  printf("  image of W in (Lambda/Gsat)/2: dimension %d (basis dependent coordinates: %s)\n", #prW, prW~);
  mapput(res, "dimprW", #prW);
  \\ tiny integral at x_a, x_b: lambda(tau) = sum_m (w0_m, w1_m) tau^m / m
  for (j = 1, 2, my(ii = phis[j][1], TT = [tt | tt <- TINY, tt[1] == ii][1], cs, ycs, pcs, vl, e1, bad1, S3, bad2);
    cs = vector(#TT[4], m, [Mod(TT[4][m], K21) / m, Mod(TT[5][m], K21) / m]);
    ycs = vector(#cs, m, Hi * logvec(apply(c -> redK(LV, c), cs[m]), P));
    pcs = apply(prj, ycs);
    vl = apply(v2vec, pcs);
    e1 = pcs[1] / 2^vl[1]; e1 = apply(c -> c % 2, e1);
    bad1 = f2in(prW, e1);
    \\ basis free form: e1 in pr(W) iff W lies in the image modulo 2 of the saturation of <Gsat, c_1> in Lambda
    my(y1 = ycs[1] / 2^v2vec(ycs[1]), M3 = matconcat([Gs, y1 * denominator(y1)]), sn3 = matsnf(M3, 1), U3i = sn3[1]^-1,
       nz3 = [i | i <- [1 .. 6], vecmax(apply(abs, Vec(sn3[3][i, ]))) != 0]);
    chq(#nz3 == 3, "c_1 is not in the span of log Gamma");
    S3 = lift(matimage(Mod(Mat(vector(3, i, U3i[, nz3[i]])), 2)));
    bad2 = f2in(S3, W);
    chq(bad1 == bad2, "the two forms of the class test agree");
    printf("  x_%d: v_2(pr c_m), m = 1..%d: %s\n", ii, #vl, vl);
    printf("  x_%d: (iii) leading class of the linear term in pr(W): %d (%s); linear term leading for v(tau) > %s\n", ii, bad1,
           if (bad1, "FAIL", "PASS"), vecmax(vector(#vl - 1, m, (vl[1] - vl[m + 1]) / m)));
    mapput(res, Str("bad_", ii), bad1); mapput(res, Str("vl_", ii), vl));
  mapput(res, "W", W); mapput(res, "WG", WG); mapput(res, "RhoD", RhoD); mapput(res, "ya", ya); mapput(res, "yb", yb);
  mapput(res, "H", H); mapput(res, "U", U); mapput(res, "nzr", nzr); mapput(res, "prW", prW); mapput(res, "Gs", Gs); mapput(res, "La", La); mapput(res, "Lb", Lb); mapput(res, "PI", PI);
  printf("  (%d ms)\n", getabstime() - t0);
  res;
}
{
  for (k = 0, 1,
    my(r1 = run(k, 240, 60, 4), r2 = run(k, 330, 90, 5));
    foreach (concat(["W", "WG", "RhoD", "dimprW"], [Str("bad_", i) | i <- if (k == 0, [0, 2], [1, 3])]), key, chq(mapget(r1, key) == mapget(r2, key), Str("same ", key, " at both precisions")));
    printf("k = %d: W, W_Gamma, rho(D_i), dim pr(W) and the class tests agree at both precisions\n", k);
    system(Str("rm -f ", SEL, "lattice_k", k, ".bin")); writebin(Str(SEL, "lattice_k", k, ".bin"), r2));
}
quit;
