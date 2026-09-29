\\ selmer_image_v.gp: the 2-Selmer group of Jac(F_k)/K21 at the place v above 2 with e = 3, written in the basis of
\\ J(K_v)/2J(K_v) given by the certified local divisors D_1..D_7 of local_images_twist<k>_e3.bin (for Selmer group Chabauty).
\\ For each twist k: the x - T coordinates c_i of D_i at v (td2_coord, the same code path as the local
\\ images of p21_29), a check that c_1..c_7 are a basis of the local image modulo the image of K_v^x, and the coefficients
\\ (over F_2, in the basis D_i) of the columns of G X (the Selmer space X of p21_29/p21_31, dimension 19, whose image
\\ modulo K_v^x is sigma_v(Sel), dimension 4) and of the known classes T, phi(x_a), phi(x_b).
\\ Input: SEL/selX_k<k>.bin written by sigma_v_injective.gp. Output: SEL/rho_k<k>.bin = [k, SelCoef (7 x 19), KnownCoef
\\ (7 x 3), names of the known classes].
\\ Run from code/earlier-computations: gp -q selmer_image_v.gp < /dev/null
default(parisizemax, 9*10^9); default(nbthreads, 1); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp"); read("field_l42_polynomial.gp"); read("field_n84_polynomial.gp");
read("../lib/richelot.gp"); read("../lib/td2loc.gp");
read("norm_relation_lib.gp"); read("prym_two_descent_lib.gp");
\\ solve M z = c over F_2 (M with independent columns); returns z or 0 when c is not in the span
f2solve(M, c) = { my(z = matsolvemod(M, 2, c)); if (type(z) == "t_INT", return(0)); lift(Mod(z, 2)); }
{
  my(t0 = getabstime(), FF = sel_fields(), AA = [sel_alg(FF, 0), sel_alg(FF, 1)], PL = sel_places(AA[1]), fin = PL[1]);
  for (k = 0, 1,
    my(A = AA[k + 1], S = read(Str(SEL, "selX_k", k, ".bin")), GX = S[1], LVk = S[3], offs = S[4], KMs = S[6], nms = S[7],
       j3 = [j | j <- [1 .. #fin], mapget(fin[j], "pr").p == 2 && mapget(fin[j], "pr").e == 3], P, o, rr, KMv, R, Cv, B, rk,
       SelCoef, KnCoef, selr);
    chk(#j3 == 1, "one place above 2 with e = 3"); j3 = j3[1]; P = fin[j3];
    chk(nms[j3] == mapget(P, "name"), "place order of selX matches");
    o = offs[j3]; rr = vector(o[2], r, o[1] + r);
    selr = (M -> matrix(#rr, #M, i, c, M[rr[i], c]));
    KMv = KMs[j3];
    R = read(Str("local_images_twist", k, "_e3.bin"));
    chk(R[1] == k && R[3] == 3 && R[6] == 1, "complete J side run at e = 3");
    Cv = Mat(vector(#R[7], i, td2_coord(A, P, R[7][i][1])));
    B = matconcat([Cv, KMv]); rk = matrank(Mod(B, 2));
    printf("k = %d, place %s: %d divisors, rank of [c_i, K_v^x] = %d = %d + rank K_v^x image %d; D_v = %d\n", k, mapget(P, "name"),
           #Cv, rk, #Cv, matrank(Mod(KMv, 2)), mapget(P, "D"));
    chk(rk == #Cv + #KMv && #Cv == mapget(P, "D"), "c_1..c_7 are a basis of the local image modulo K_v^x");
    SelCoef = matrix(#Cv, #GX); KnCoef = matrix(#Cv, #LVk);
    my(GXv = selr(GX), LVv = selr(LVk));
    for (c = 1, #GX, my(z = f2solve(B, GXv[, c])); chk(z != 0, "Selmer column in the local image");
      for (i = 1, #Cv, SelCoef[i, c] = z[i]));
    for (c = 1, #LVk, my(z = f2solve(B, LVv[, c])); chk(z != 0, "known class in the local image");
      for (i = 1, #Cv, KnCoef[i, c] = z[i]));
    printf("  rank of sigma_v(Sel) in the D basis: %d; known classes (T, phi(x_a), phi(x_b)) in the D basis:\n", matrank(Mod(SelCoef, 2)));
    for (c = 1, #LVk, printf("    %s\n", KnCoef[, c]~));
    printf("  basis of sigma_v(Sel) in the D basis (columns): %s\n", lift(matimage(Mod(SelCoef, 2))));
    wbin(Str(SEL, "rho_k", k, ".bin"), [k, SelCoef, KnCoef, ["T", "phi_a", "phi_b"]]));
  printf("done (%d ms)\n", getabstime() - t0);
}
quit;
