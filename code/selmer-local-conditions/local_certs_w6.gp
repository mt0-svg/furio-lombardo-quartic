\\ local_certs_w6.gp: certificate data at w3 in the format of the Lean files PlaceW3*.lean.
\\ Model (w_component_models.gp): F = K_w3[Y]/(Y^2 - B Y - A), om = sqrt(eps) = y + c Y exactly, c = alpha^5, A, B in O_K21.
\\ Standard basis of F^x/F^x2 at a component (14 elements, the order of Echelon's pivots):
\\   Y;  1 + alpha^j Y (j = 0 .. 11, depth 2j + 1);  5 = 1 + 4 * 1 (depth 2e_F = 24, trace 1).
\\ Certificate of an integral element X of F (a pair of K21 elements on 1, Y) with bits a (14 bits, bit 0 = Y,
\\ bit j + 1 = 1 + alpha^j Y, bit 13 = 5): with m = v_F(S_tot), m = 2 mh + ep, S_tot = alpha^mh Y^ep S'',
\\ S'' = (1 + alpha c0) + s1 Y, the exact identity in K21[Y]/(P1)
\\   X * B_a - alpha^(2 mh) (Y^2)^ep S''^2 = alpha^n0 R0 + alpha^n1 R1 Y,  n0 = m + 13, n1 = m + 12,
\\ with c0, s1, R0, R1 in O_K21 (zk integer lists), B_a = Y^a0 5^a13 prod_j (1 + alpha^j Y)^a_(j+1).
\\ Then ||X B_a - S_tot^2|| <= ||Y||^(2m + 25) < ||4|| ||S_tot||^2, so X B_a is a square in F.
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-local-conditions/local_certs_w6.gp < /dev/null > ../selmer-local-conditions/local_certs_w6.out 2>&1
default(parisizemax, 800 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp"); read("richelot_data.gp");
read("../selmer-local-conditions/selmer_rows_lib.gp"); read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
OUTL = "/tmp/sb8/PlaceW3Data.cand.lean";
SBu7 = -1;
T00 = getabstime();
zk(z) = nfalgtobasis(nfK, z)~;
isint(z) = denominator(nfalgtobasis(nfK, z)) == 1;
zkl(z) = my(v = nfalgtobasis(nfK, z)); if (denominator(v) != 1, error("zkl: not integral")); Str(Vec(v));
sqclass(W, u) = {
  my(C0 = sb_comp(W, 1), al = mapget(W, "al"), e = mapget(W, "e"), NP = 2 * e + 8, z, rr, d, s = Mod(1, K21), tt = 0);
  z = redK(W, u, NP); rr = liftres(C0, ksqrt(C0, res(C0, z))); z = redK(W, z / rr^2, NP); s = s * rr;
  for (s1 = 1, 2 * e - 1, d = res(C0, redK(W, (z - 1) / al^s1, NP)); if (d == 0, next);
    if (s1 % 2, tt = s1; break); rr = 1 + al^(s1 / 2) * liftres(C0, ksqrt(C0, d)); z = redK(W, z / rr^2, NP); s = redK(W, s * rr, NP));
  if (!tt, my(d4 = res(C0, redK(W, (z - 1) / 4, NP))); tt = if (d4 == 0, 2 * e + 1, 2 * e));
  [tt, redK(W, s, NP)];
}
\\ one certificate: X integral in F; returns [a (bitmask), mh, ep, c0, s1, n0, n1, R0, R1] and checks it exactly
w3cert(C, X, name) = {
  my(al = mapget(mapget(C, "W"), "al"), one = mapget(C, "one"), bas = mapget(C, "bas"), ce, av, m, mh, ep, S, S2, Ba = one, R, n0, n1, v0, c0, s1, R0, R1, NP);
  ce = coords(C, X); if (!verC(C, X, ce), error("w3cert: verC failed for ", name));
  av = ce[1]; m = ce[2]; S = ce[3]; ep = m % 2; mh = (m - ep) / 2; NP = 2 * m + 40;
  S2 = red(C, (Y1^2 * one / al)^mh * S, NP);
  my(cS = co(C, S2)); c0 = (cS[1] - 1) / al; s1 = cS[2];
  if (!isint(c0) || !isint(s1), error("w3cert: S'' not of the shape (1 + alpha c0) + s1 Y for ", name));
  for (i = 1, #av, if (av[i], Ba = Ba * bas[i]));
  R = X * Ba - al^(2 * mh) * (Y1^2 * one)^ep * ((1 + al * c0) + s1 * Y1)^2;
  n0 = m + 13; n1 = m + 12;
  my(cR = co(C, R)); R0 = cR[1] / al^n0; R1 = cR[2] / al^n1;
  if (!isint(R0) || !isint(R1), error("w3cert: remainder not in alpha^n0 O + alpha^n1 O Y for ", name, ": v = ", vw(mapget(C, "W"), cR[1]), ", ", vw(mapget(C, "W"), cR[2]), ", m = ", m));
  [sum(i = 1, #av, av[i] * 2^(i - 1)), mh, ep, c0, s1, n0, n1, R0, R1];
}
certstr(c) = Str("⟨", c[1], ", ", c[2], ", ", c[3], ", ", zkl(c[4]), ", ", zkl(c[5]), ", ", c[6], ", ", c[7], ", ", zkl(c[8]), ", ", zkl(c[9]), "⟩");
{
  my(W, e, al, EPSa, EN, m, u, sc, tt, yy, cc, A, B, C, om, one, mybas, gLs, certs = List(), t0);
  sb_init();
  EPSa = nfbasistoalg(nfK, KofList(leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL")));
  zkNum = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"); Dz = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz");
  chq(vector(21, j, Pol(Vecrev(zkNum[j]), 'b) / Dz) == nfK.zk, "nfK.zk = M1's zkNum / Dz");
  W = sb_place(3); e = mapget(W, "e"); al = mapget(W, "al");
  \\ model
  sc = sqclass(W, EPSa); tt = sc[1]; chq(vw(W, EPSa) == 0 && tt == 11, "w3: eps is a unit of odd depth 11");
  yy = Mod(lift(sc[2]), K21); cc = al^5; A = (EPSa - yy^2) / cc^2; B = -2 * yy / cc;
  chq(isint(A) && isint(B) && isint(yy) && vw(W, A) == 1 && vw(W, B) >= 1, "w3: y, A, B in O_K21, Eisenstein (v(A) = 1, v(B) >= 1)");
  C = sb_comp(W, 2, A, B, 1); one = mapget(C, "one");
  om = one * (yy + cc * Y1); chq(om^2 == EPSa * one, "w3: (y + alpha^5 Y)^2 = eps in K21[Y]/(P1)");
  mybas = concat([[Y1 * one], vector(12, j, one * (1 + al^(j - 1) * Y1)), [5 * one]]);
  chq(vector(12, j, val(C, mybas[j + 1] - 1)) == vector(12, j, 2 * j - 1), "w3: 1 + alpha^j Y has depth 2j + 1 (j = 0 .. 11)");
  mapput(C, "bas", mybas);
  chq(vector(14, i, coords(C, mybas[i])[1]) == vector(14, i, vector(14, l, l == i)), "w3: the coordinates of the basis are the unit vectors");
  \\ probe: the 29 generators of L42 at the q component
  gLs = vector(29, s1, leandef5(Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean"), Str("gL_", s1 - 1)));
  t0 = getabstime();
  for (s1 = 1, 29, my(z0 = nfbasistoalg(nfK, KofList(gLs[s1][1])), z1 = nfbasistoalg(nfK, KofList(gLs[s1][2])), X0 = one * (z0 + z1 * (yy + cc * Y1)));
    listput(certs, w3cert(C, X0, Str("gL_", s1 - 1))));
  printf("  29 certificates of the L42 generators at the q component (%d ms); bits: %s\n", getabstime() - t0, apply(c -> c[1], Vec(certs)));
  printf("  m values: %s\n", apply(c -> 2 * c[2] + c[3], Vec(certs)));
  system("mkdir -p /tmp/sb8");
  system(Str("rm -f ", OUTL));
  write(OUTL, Str("def w3yL : List ℤ := ", zkl(yy)));
  write(OUTL, Str("def w3AL : List ℤ := ", zkl(A)));
  write(OUTL, Str("def w3BL : List ℤ := ", zkl(B)));
  for (d = 0, 80, write(OUTL, Str("def w3al_", d, " : List ℤ := ", zkl(al^d))));
  write(OUTL, Str("def w3alPow : List (List ℤ) := [", strjoin(vector(81, d, Str("w3al_", d - 1)), ", "), "]"));
  for (n = 0, 14, my(cY = co(C, Y1^n * one)); write(OUTL, Str("def w3Y_", n, " : List ℤ × List ℤ := (", zkl(cY[1]), ", ", zkl(cY[2]), ")")));
  write(OUTL, Str("def w3Ypow : List (List ℤ × List ℤ) := [", strjoin(vector(15, n, Str("w3Y_", n - 1)), ", "), "]"));
  for (i = 1, #certs, write(OUTL, Str("def w3cL_", i - 1, " : WCert := ", certstr(certs[i]))));
  write(OUTL, Str("def w3certL : List WCert := [", strjoin(vector(#certs, i, Str("w3cL_", i - 1)), ", "), "]"));
  printf("  bits of alpha^80: %d, of Y^14: %d\n", bits5(zk(al^80)), bits5(apply(zk, co(C, Y1^14 * one))));
  printf("DONE, %d failed checks (%d ok, %d ms)\n", NFAIL, NOK, getabstime() - T00);
}
