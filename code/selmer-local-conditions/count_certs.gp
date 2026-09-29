\\ count_certs.gp: the certificate data of the count at w3, w2 (dyadic, residue F_2) and w7 (above 7), in
\\ M1's integral basis, for the Kronecker tests of Count/Cert.lean (ck_isSquare, ck_not_isSquare_depth,
\\ ck_not_isSquare_odd) and Count/KE.lean (nAt_ne_zero_of_check). The uniformizers are M2's al2, al3, al7 (each
\\ generates its prime). Every element is integral; b = 1 in every certificate.
\\ Y = 4 fRev_k(x) (Count/KE.lean gE k x 0, square class of fRev_k(x)): square, with t, Y - t^2 = al^n a,
\\   t^2 = al^m a', a' a_i = 1 + al c_a, n > m + 2e (e = v(2): 12, 6, 0).
\\ Non-squares Y = 46^2 d (dnData), Y = 4 c_k (FnData k 0), Y = 46^2 ND (zData k 2): odd depth (Y - t^2 = al^n a,
\\   t^2 = al^m a', a, a' units, n - m odd < 2e) or odd valuation (Y = al^n a, a a unit).
\\ nAt: nE = tN0(G_0..G_4), G_j the coefficients of 4 fRev_k(X + x) (= 256 nAt), nu = D / nE integral, D > 0 minimal.
\\ Input count_lean_data.gp (sh count_lean_data.sh, a copy of the Lean lists). Writes the Lean data file
\\ ../../FurioLombardo/Discharge/SelmerBasis/Count/CertData.lean.
\\ Run from code/selmer-local-conditions: gp -q count_certs.gp < /dev/null > count_certs.out 2>&1 (LEANOUT=<dir>/ writes CertData.lean to <dir> instead)
default(parisizemax, 10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("count_lean_data.gp");
o = Mod(1, K21); red(g) = lift(o * g);
el(l) = lift(nfbasistoalg(nf, l~));
cz(z) = {my(v = nfalgtobasis(nf, z)); if (denominator(v) != 1, error("not integral")); Vec(v)};
{AL = Map(); mapput(AL, "w2", [-2, 2, 0, 1, 0, -2, 1, -1, 0, 2, 0, 1, 2, -1, 0, 2, 1, -1, 0, 1, -1]);
 mapput(AL, "w3", [1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
 mapput(AL, "w7", [-2, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1]);}
P2 = idealprimedec(nf, 2);
PR = Map(); mapput(PR, "w2", [pr | pr <- P2, pr.e == 12][1]); mapput(PR, "w3", [pr | pr <- P2, pr.e == 6][1]);
mapput(PR, "w7", idealprimedec(nf, 7)[1]);
foreach(["w2", "w3", "w7"], w, if (idealhnf(nf, el(mapget(AL, w))) != idealhnf(nf, mapget(PR, w)), error(Str("al does not generate ", w))));
vw(z, pr) = if (z == 0, oo, idealval(nf, z, pr));
\\ 4 fRev_k (constant term first: FE k 6, ..., FE k 0)
fr4 = vector(2, k, sum(i = 0, 6, el(FnData[k][7 - i]) * t^i));
tN0(c0, c1, c2, c3, c4) = 64 * c0^3 * c4 - 16 * c0^2 * c2^2 - 32 * c0^2 * c1 * c3 + 24 * c0 * c1^2 * c2 - 5 * c1^4;
\\ inverse modulo the prime (F_2: 1)
invm(a, pr) = {
  if (pr.f == 1, if (pr.p != 2, error("f = 1, p odd")); return(1));
  my(M = nfmodprinit(nf, pr), z = nfmodprlift(nf, nfmodpr(nf, a, M)^(-1), M));
  if (type(z) == "t_COL", z = nfbasistoalg(nf, z)); red(lift(z));
}
\\ [a_i, c_a] with a a_i = 1 + al c_a
unitc(a, A, pr) = {my(ai = invm(a, pr), ca = red((a * ai - 1) / A)); if (vw(a, pr) != 0, error("not a unit")); [cz(ai), cz(ca)]};
\\ greedy approximate square root of an even valuation z at a dyadic pr with residue F_2 (count_square_classes.gp)
depth(z, pr, A, E) = {
  my(v = vw(z, pr), s = 1, d);
  if (v % 2, return([v, -1, 0]));
  for (i = 1, 4 * E + 4, d = vw(red(z - A^v * s^2), pr) - v;
    if (d % 2 || d > 2 * E, break);
    s = red(s + A^(d / 2)));
  [v, d, red(A^(v / 2) * s)];
}
\\ Lean output
LF = Str(if (#getenv("LEANOUT"), getenv("LEANOUT"), "../../FurioLombardo/Discharge/SelmerBasis/Count/"), "CertData.lean");
out = List();
emitL(name, v) = listput(out, Str("def ", name, " : List ℤ := ", lst(v)));
emitN(name, n) = listput(out, Str("def ", name, " : ℕ := ", n));
emitZ(name, n) = listput(out, Str("def ", name, " : ℤ := ", n));
\\ square certificate of Y from t: n = m + 2e + 1
sqcert(name, Y, T, w) = {
  my(pr = mapget(PR, w), A = el(mapget(AL, w)), E = if (pr.p == 2, pr.e, 0), m = vw(red(T^2), pr), n = m + 2 * E + 1, a, a1, u);
  if (vw(red(Y - T^2), pr) < n, error(Str(name, ": not deep enough")));
  a = red((Y - T^2) / A^n); a1 = red(T^2 / A^m); u = unitc(a1, A, pr);
  emitL(Str(name, "T"), cz(T)); emitL(Str(name, "A"), cz(a)); emitL(Str(name, "B"), cz(a1));
  emitL(Str(name, "Bi"), u[1]); emitL(Str(name, "Cb"), u[2]); emitN(Str(name, "n"), n); emitN(Str(name, "m"), m);
  printf("%s: square at %s, v(Y) = %d, v(Y - t^2) = %d, n = %d, m = %d, e = %d\n", name, w, vw(Y, pr), vw(red(Y - T^2), pr), n, m, E);
}
\\ non-square certificate of Y: odd valuation or odd depth
nsqcert(name, Y, w) = {
  my(pr = mapget(PR, w), A = el(mapget(AL, w)), E = if (pr.p == 2, pr.e, 0), v = vw(Y, pr), a, u, r, n, m, T, a1, u1);
  if (v % 2,
    a = red(Y / A^v); u = unitc(a, A, pr);
    emitL(Str(name, "A"), cz(a)); emitL(Str(name, "Ai"), u[1]); emitL(Str(name, "Ca"), u[2]); emitN(Str(name, "n"), v);
    printf("%s: not a square at %s, odd valuation %d\n", name, w, v); return);
  if (pr.p != 2, error(Str(name, ": even valuation at an odd place")));
  r = depth(Y, pr, A, E);
  if (r[2] % 2 == 0 || r[2] >= 2 * E, error(Str(name, ": depth ", r[2], " is not odd < 2e")));
  T = r[3]; m = vw(red(T^2), pr); n = m + r[2];
  a = red((Y - T^2) / A^n); u = unitc(a, A, pr); a1 = red(T^2 / A^m); u1 = unitc(a1, A, pr);
  emitL(Str(name, "T"), cz(T)); emitL(Str(name, "A"), cz(a)); emitL(Str(name, "Ai"), u[1]); emitL(Str(name, "Ca"), u[2]);
  emitL(Str(name, "B"), cz(a1)); emitL(Str(name, "Bi"), u1[1]); emitL(Str(name, "Cb"), u1[2]);
  emitN(Str(name, "n"), n); emitN(Str(name, "m"), m);
  printf("%s: not a square at %s, v = %d, odd depth %d (n = %d, m = %d, 2e = %d)\n", name, w, v, r[2], n, m, 2 * E);
}
\\ nAt: nu = D / nE
ncert(name, k, x) = {
  my(g = subst(fr4[k], t, t + x), G = vector(5, j, red(polcoef(g, j - 1, t))), N = red(tN0(G[1], G[2], G[3], G[4], G[5])), z, D);
  if (N == 0, error(Str(name, ": N0 = 0")));
  z = nfalgtobasis(nf, 1 / Mod(N, K21)); D = denominator(z);
  emitL(Str(name, "Nu"), Vec(z * D)); emitZ(Str(name, "D"), D);
  printf("%s: nAt != 0, D has %d digits, max |nu| has %d digits\n", name, #Str(D), #Str(vecmax(abs(Vec(z * D)))));
}
{
  my(A2 = el(mapget(AL, "w2")), A3 = el(mapget(AL, "w3")), X, Y, r, pr);
  \\ base abscissas (count_base_abscissas.out, count_base_point_w7.out)
  my(xs = [["w2", 1, 0], ["w3", 1, 0], ["w2", 2, red(1 + A2 + A2^2 + A2^3 + A2^5 + A2^7)], ["w3", 2, red(1 + A3^5)],
    ["w7", 2, el([6199031, 20450819, 5736469, -14122989, 14655443, -16672666, 24578767, -9205733, 34317805, 8848738, 6377953, 27441228, -2113159, -30481, 2879294, 2689841, 2257573, 458141, -2282422, -1461659, -813604])]]);
  foreach(xs, P, my(w = P[1], k = P[2], x = P[3], nm = Str(w, "k", k - 1));
    pr = mapget(PR, w);
    if (x != 0, emitL(Str(nm, "x"), cz(x)));
    Y = red(subst(fr4[k], t, x));
    if (w == "w7",
      X = 2 * el([-18021906, 13527234, 14458822, 2048053, 16024274, 35554008, 33806080, 21959546, 1983226, 13114262, 7311045, 2249737, 1656690, 28812, 823543, -2050454, 1908795, -895573, 2427411, -725102, -693889]),
      r = depth(Y, pr, el(mapget(AL, w)), pr.e); if (r[2] <= 2 * pr.e, error(Str(nm, ": f(x) depth ", r[2]))); X = r[3]);
    sqcert(Str(nm, "sq"), Y, X, w);
    ncert(nm, k, x));
  \\ non-squares: d at w3 (both twists, dnData k), c_k at w3, c_1 at w2, c_1 and ND_1 at w7
  for (k = 1, 2, nsqcert(Str("w3k", k - 1, "d"), el(dnData[k]), "w3"));
  for (k = 1, 2, nsqcert(Str("w3k", k - 1, "c"), el(FnData[k][1]), "w3"));
  nsqcert("w2k1c", el(FnData[2][1]), "w2");
  nsqcert("w7k1c", el(FnData[2][1]), "w7");
  if (zDen[2][3] != 46^2, error("zDen"));
  nsqcert("w7k1nd", el(zData[2][3]), "w7");
  \\ |2| = 1 at w7: 2 * 4 = 1 + al7 * (7 / al7)
  emitL("w7two", cz(red(7 / el(mapget(AL, "w7")))));
  \\ the depth 2e classes left to the local side: d and c_0 at w2
  r = depth(el(dnData[1]), mapget(PR, "w2"), A2, 12); printf("w2: 46^2 d: v = %d, depth %d (2e = 24)\n", r[1], r[2]);
  r = depth(el(FnData[1][1]), mapget(PR, "w2"), A2, 12); printf("w2: 4 c_0: v = %d, depth %d (2e = 24)\n", r[1], r[2]);
  printf("dnData twist independent: %d\n", dnData[1] == dnData[2]);
}
{
  my(s = "import Mathlib\n\n/-!\n# Count lane: certificate data at w2, w3, w7\n\nGenerated by code/selmer-local-conditions/count_certs.gp (log count_certs.out) from the Lean lists of\nM3a's DataBruin.lean and LocalData.lean; checked by the Kronecker tests of Count/AtW3.lean, AtW2.lean,\nAt7.lean. Names: place, twist, kind (`sq` square of `4 fRev_k(x)`, `d`, `c`, `nd` non-squares, `Nu`, `D`\nfor `nAt`), field.\n-/\n\nnamespace FurioLombardo.Discharge.SelmerBasis.Count.Data\n\n");
  for (i = 1, #out, s = Str(s, out[i], "\n\n"));
  s = Str(s, "end FurioLombardo.Discharge.SelmerBasis.Count.Data\n");
  system(Str("rm -f ", LF)); write1(LF, s); printf("wrote %d definitions to %s\n", #out, LF);
}
print("DONE");
