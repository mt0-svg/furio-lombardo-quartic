\\ w_component_models.gp: exact component models at w3 and w2 (probe, stage 1 of the w-places data).
\\ At a place w (M2's generator alpha) with L42 = K21(om), om^2 = eps, not split at w, the component field is
\\ F = K_w[Y]/(Y^2 - B Y - A) with A, B in O_K21 chosen so that om = y + c Y exactly (y in O_K21, c = alpha^j or 2 alpha^j):
\\   ramified (unit part of eps at odd depth t < 2e): c = alpha^(m + (t-1)/2), A = (eps - y^2)/c^2, B = -2y/c;
\\   unramified (depth 2e): c = alpha^(m + e) (the w-part of 2 alpha^m, no other prime), A = (eps - y^2)/c^2, B = -2y/c.
\\ Checks: A, B integral, the shape (Eisenstein: v(A) = 1, v(B) >= 1; unramified: A = -1, B = 1 mod w), om = y + cY is a root
\\ of X^2 - eps in F (exact), and iota(eN) is a square in F (zero coordinates on the standard basis of selmer_rows_lib).
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-local-conditions/w_component_models.gp < /dev/null > ../selmer-local-conditions/w_component_models.out 2>&1
default(parisizemax, 800 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp");
read("../selmer-local-conditions/selmer_rows_lib.gp"); read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
SBu7 = -1;
T00 = getabstime();
zk(z) = nfalgtobasis(nfK, z)~;
isint(z) = denominator(nfalgtobasis(nfK, z)) == 1;
\\ the square class of a w-unit u in K_w: [t, s] with v(u - s^2) = t maximal (t odd < 2e, or 2e: unramified class,
\\ or > 2e: u a square); s a small integral representative
sqclass(W, u) = {
  my(C0 = sb_comp(W, 1), al = mapget(W, "al"), e = mapget(W, "e"), NP = 2 * e + 8, z, rr, d, s = Mod(1, K21), tt = 0);
  z = redK(W, u, NP); rr = liftres(C0, ksqrt(C0, res(C0, z))); z = redK(W, z / rr^2, NP); s = s * rr;
  for (s1 = 1, 2 * e - 1, d = res(C0, redK(W, (z - 1) / al^s1, NP)); if (d == 0, next);
    if (s1 % 2, tt = s1; break); rr = 1 + al^(s1 / 2) * liftres(C0, ksqrt(C0, d)); z = redK(W, z / rr^2, NP); s = redK(W, s * rr, NP));
  if (!tt, my(d4 = res(C0, redK(W, (z - 1) / 4, NP))); tt = if (d4 == 0, 2 * e + 1, 2 * e));
  [tt, redK(W, s, NP)];
}
model(W, name) = {
  my(al = mapget(W, "al"), e = mapget(W, "e"), v0 = vw(W, EPSa), m, u, sc, tt, s, yy, cc, A, B, C, om, iEN, ce);
  printf("==== %s: v(eps) = %d\n", name, v0);
  if (v0 % 2, error("odd valuation of eps: not handled by this probe"));
  m = v0 / 2; u = EPSa / al^(2 * m); sc = sqclass(W, u); tt = sc[1]; s = sc[2];
  printf("  unit part of eps at depth %d (2e = %d)\n", tt, 2 * e);
  yy = Mod(lift(al^m * s), K21);
  if (tt < 2 * e, if (tt % 2 == 0, error("even depth")); cc = al^(m + (tt - 1) / 2), if (tt == 2 * e, cc = al^(m + e), error("eps a square at w")));
  A = (EPSa - yy^2) / cc^2; B = -2 * yy / cc;
  chq(isint(A) && isint(B), Str(name, ": A, B in O_K21 (zk integer coordinates)"));
  printf("  bits of A, B: %d, %d; v(A) = %d, v(B) = %d\n", bits5(zk(A)), bits5(zk(B)), vw(W, A), vw(W, B));
  if (tt < 2 * e, chq(vw(W, A) == 1 && vw(W, B) >= 1, Str(name, ": Eisenstein shape"));  C = sb_comp(W, 2, A, B, 1),
    chq(vw(W, A + 1) >= 1 && vw(W, B - 1) >= 1, Str(name, ": unramified shape, A = -1, B = 1 mod w")); C = sb_comp(W, 2, A, B, 0));
  om = mapget(C, "one") * (yy + cc * Y1);
  chq(om^2 == EPSa * mapget(C, "one"), Str(name, ": om = y + c Y satisfies om^2 = eps exactly in K21[Y]/(P1)"));
  iEN = EN[1] + EN[2] * om; iEN = nfbasistoalg(nfK, EN[1]) + nfbasistoalg(nfK, EN[2]) * om;
  printf("  v_F(iota(eN)) = %d\n", val(C, iEN));
  ce = coords(C, iEN);
  printf("  iota(eN) on the standard basis: %s\n", ce[1]);
  chq(ce[1] == 0 * ce[1], Str(name, ": iota(eN) is a square in F (h splits into two components isomorphic to F)"));
  [yy, cc, A, B, C];
}
{
  sb_init();
  EPSa = nfbasistoalg(nfK, KofList(leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL")));
  EN = [KofList(leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL")) / 2, KofList(leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL")) / 2];
  zkNum = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"); Dz = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz");
  chq(vector(21, j, Pol(Vecrev(zkNum[j]), 'b) / Dz) == nfK.zk, "nfK.zk = M1's zkNum / Dz");
  foreach ([3, 2], pi, my(W = sb_place(pi)); model(W, SB_PNAME[pi]));
  printf("DONE, %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00);
}
