\\ two_torsion_image_v.gp: direct check of hypothesis (b) of
\\ FurioLombardo.Discharge.M3a.localTwoTorsion_route_of_factors, in the original model y^2 = f_k = c G1 h:
\\ the local x - T image mu_v(T) of T = [W1 + W2 - Dinf] (W1, W2 above the roots of the quadratic factor G1) at the
\\ place v above 2 with e = 3 is nonzero in A_v^x / (K_v^x A_v^x2). Uses td2loc (code/lib) and the cached factor fields
\\ and place data of prym_two_descent.gp (/tmp/k21c/sel/fields.bin, places.bin). The reversed model has the same class
\\ modulo K_v^x and squares (the translation of the x - T map).
\\ Run from code/earlier-computations: gp -q ../genus2-curves/two_torsion_image_v.gp
default(parisizemax, 5 * 10^9); default(nbthreads, 1); default(realprecision, 60);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp"); read("field_l42_polynomial.gp"); read("field_n84_polynomial.gp");
read("../lib/richelot.gp"); read("../lib/td2loc.gp");
read("norm_relation_lib.gp"); read("prym_two_descent_lib.gp");
{
  my(FF = sel_fields(), PL, P);
  for (k = 0, 1,
    my(A = sel_alg(FF, k), G1x = subst(RIN[k + 1][2], t, x), c, KM, r0, r1);
    if (k == 0, PL = sel_places(A));
    P = [Q | Q <- PL[1], mapget(Q, "pr").p == 2 && mapget(Q, "pr").e == 3][1];
    printf("k = %d: place %s, factor degrees %s, tors2 %d, eps %d, D_v %d, coordinates %d\n", k, mapget(P, "name"),
      mapget(P, "degs"), mapget(P, "tors2"), mapget(P, "eps"), mapget(P, "D"), mapget(P, "N"));
    c = td2_coord(A, P, td2_Kx(mapget(A, "nfK"), G1x / pollead(G1x)));
    KM = mapget(P, "KM");
    r0 = matrank(Mod(KM, 2)); r1 = matrank(Mod(concat(KM, c), 2));
    printf("  mu_v(T) coordinates %s\n  rank of K_v^x image %d, with mu_v(T) %d: mu_v(T) nonzero modulo K_v^x: %d\n",
      c~, r0, r1, r1 > r0));
}
quit;
