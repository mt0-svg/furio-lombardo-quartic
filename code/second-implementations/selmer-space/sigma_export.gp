\\ sigma_export.gp: text export of the F_2 data behind sigma_v injective (p21_31) and the D-basis coordinates of
\\ p21_35 at the place v above 2 with e = 3, for the second implementation of that linear algebra in Sage
\\ (code/second-implementations/selmer-space/sigma_check.sage). Writes code/second-implementations/selmer-space/sigma_twist<k>.txt with, as GP matrices of 0/1 entries:
\\   GXv (rows of v of the 19 generators of X), KMv (image of K_v^x at v), LVv (rows of v of T, phi_a, phi_b),
\\   Cv (x - T coordinates at v of the certified local divisors D_1..D_7, td2_coord), KMbar, LV (all places, for the
\\   relation among T, phi_a, phi_b), dX, and SelCoef, KnCoef of rho_k<k>.bin (for the comparison).
\\ Input: /tmp/k21c/sel/selX_k<k>.bin (sigma_v_injective.gp) and code/earlier-computations/data/selmer_image_v_twist<k>.bin (selmer_image_v.gp).
\\ Run from code/earlier-computations: gp -q ../second-implementations/selmer-space/sigma_export.gp < /dev/null
\\ (run in the workspace under a resource cap, cap -m 10G -c 1 -t 29m).
default(parisizemax, 9*10^9); default(nbthreads, 1); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp"); read("field_l42_polynomial.gp"); read("field_n84_polynomial.gp");
read("../lib/richelot.gp"); read("../lib/td2loc.gp");
read("norm_relation_lib.gp"); read("prym_two_descent_lib.gp");
{
  my(FF = sel_fields(), AA = [sel_alg(FF, 0), sel_alg(FF, 1)], PL = sel_places(AA[1]), fin = PL[1]);
  for (k = 0, 1,
    my(A = AA[k + 1], S = read(Str(SEL, "selX_k", k, ".bin")), GX = S[1], KMbar = S[2], LV = S[3], offs = S[4], KMs = S[6],
       nms = S[7], j3 = [j | j <- [1 .. #fin], mapget(fin[j], "pr").p == 2 && mapget(fin[j], "pr").e == 3], P, o, rr, selr,
       R, Cv, rho = read(Str("data/selmer_image_v_twist", k, ".bin")), fn = Str("../second-implementations/selmer-space/sigma_twist", k, ".txt"));
    if (#j3 != 1, error("one place e = 3")); j3 = j3[1]; P = fin[j3];
    if (nms[j3] != mapget(P, "name"), error("place order"));
    o = offs[j3]; rr = vector(o[2], r, o[1] + r);
    selr = (M -> matrix(#rr, #M, i, c, M[rr[i], c]));
    R = read(Str("local_images_twist", k, "_e3.bin"));
    Cv = Mat(vector(#R[7], i, td2_coord(A, P, R[7][i][1])));
    system(Str("rm -f ", fn));
    write(fn, "k = ", k, ";");
    write(fn, "place = \"", mapget(P, "name"), "\";");
    write(fn, "dX = ", S[8], ";");
    write(fn, "GXv = ", lift(Mod(selr(GX), 2)), ";");
    write(fn, "KMv = ", lift(Mod(KMs[j3], 2)), ";");
    write(fn, "LVv = ", lift(Mod(selr(LV), 2)), ";");
    write(fn, "Cv = ", lift(Mod(Cv, 2)), ";");
    write(fn, "KMbar = ", lift(Mod(KMbar, 2)), ";");
    write(fn, "LV = ", lift(Mod(LV, 2)), ";");
    write(fn, "SelCoef = ", lift(Mod(rho[2], 2)), ";");
    write(fn, "KnCoef = ", lift(Mod(rho[3], 2)), ";");
    printf("k = %d: wrote %s (rows at v: %d; GX %d x %d; KMbar %d x %d)\n", k, fn, #rr, #GX~, #GX, #KMbar~, #KMbar));
}
quit;
