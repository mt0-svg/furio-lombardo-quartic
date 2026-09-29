\\ count_certs_w12.gp: the two depth 2e = 24 non-square certificates at w2 for the count
\\ (Count/AtW2.lean): Y = 46^2 d (dnData, twist independent) and Y = 4 c_0 (FnData 0 0), with t, Y - t^2 = al^n a (al^n from the table w2alPow),
\\ t^2 = al^m a', a a_i = 1 + al c_a, a' a'_i = 1 + al c'_a, n = m + 2e (e = 12, al = M2's al2).
\\ Since the residue field of w2 is F_2, Y / t^2 = 1 + 4 u with u a unit is not a square.
\\ The precisions of the four Kronecker tests per certificate come from the exact emulation of checkK
\\ (../selmer-local-conditions/w6_kernel_emulation_lib.gp, with the fast keprec of ../selmer-local-conditions/local_data_v.gp); negative controls: the tests fail
\\ at one bit less, and with a flipped datum.
\\ Input ../selmer-local-conditions/count_lean_data.gp (sh ../selmer-local-conditions/count_lean_data.sh, a copy of the Lean lists).
\\ Writes the Lean data file ../../FurioLombardo/Discharge/SelmerBasis/Count/AtW2Data.lean.
\\ Run from code/selmer-local-conditions: gp -q count_certs_w12.gp < /dev/null > count_certs_w12.out 2>&1 (LEANOUT=<dir>/ writes AtW2Data.lean to <dir> instead)
default(parisizemax, 10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../selmer-local-conditions/count_lean_data.gp");
read("../selmer-global-bound/tower_lib.gp");
read("../selmer-local-conditions/w6_kernel_emulation_lib.gp");
LEAN = "../../FurioLombardo/";
KZN = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"); KDZ = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz");
KFL = leandef5(Str(LEAN, "M1/Basic.lean"), "fL");
NFAIL = 0; NOK = 0;
chq(c, msg) = if (!c, NFAIL++; printf("CHECK FAILED: %s\n", msg), NOK++; printf("ok: %s\n", msg));
chq(vector(21, j, Pol(Vecrev(KZN[j]), 'b) / KDZ) == nf.zk, "nf.zk = M1's zkNum / Dz");
chq(Pol(Vecrev(KFL), 'b) == K21, "M1's fL = K21");
\\ fast keprec (local_data_v.gp)
keprec(e) = {
  my(b = kebnd(e), k = max(8, #binary(2 * b)), k2, N, WN, v, gN, q, Q, k1);
  for (i = 0, 8, if (kecheck(e, k + i), return(k + i)));
  k2 = 2 * k + 64;
  for (r = 1, 6,
    N = 2^k2; WN = apply(l -> evalLN(N, l), KZN); v = kevalN(e, WN); gN = evalLN(N, KFL);
    if (v % gN != 0, error("keprec: not divisible"));
    q = v / gN; Q = kedigits(k2, kelen(e), q);
    if (evalLN(N, Q) == q && 4 * maxabs(Q) < 2^k2,
      k1 = #binary(2 * (b + #KFL * maxabs(KFL) * maxabs(Q)));
      for (i = 0, 40, if (kecheck(e, k1 + i), return(k1 + i))));
    k2 *= 2);
  error("keprec: no precision found");
}
\\ KE.pow of Kron.lean: pow 0 = int 1, pow 1 = e, pow (n + 2) = mul (pow (n + 1)) e
kepow(e, n) = if (n == 0, KINT(1), n == 1, e, KMUL(kepow(e, n - 1), e));
keval(e) = { my(tt = e[1]); if (tt == 0, if (#e[2] == 0, Mod(0, K21), zkr(e[2])), tt == 1, Mod(e[2], K21), tt == 2, keval(e[2]) + keval(e[3]), tt == 3, keval(e[2]) - keval(e[3]), keval(e[2]) * keval(e[3])); }
o = Mod(1, K21); red(g) = lift(o * g);
el(l) = lift(nfbasistoalg(nf, l~));
cz(z) = {my(v = nfalgtobasis(nf, z)); if (denominator(v) != 1, error("not integral")); Vec(v)};
AL2 = [-2, 2, 0, 1, 0, -2, 1, -1, 0, 2, 0, 1, 2, -1, 0, 2, 1, -1, 0, 1, -1];
chq(AL2 == leandef5(Str(LEAN, "M2/SpecialData.lean"), "al2"), "al2 = Lean's M2.Special.al2");
A2 = el(AL2);
PR2 = [pr | pr <- idealprimedec(nf, 2), pr.e == 12][1];
chq(idealhnf(nf, A2) == idealhnf(nf, PR2) && PR2.f == 1, "al2 generates w2 (e = 12, f = 1)");
E2 = 12;
vw(z) = if (z == 0, oo, idealval(nf, z, PR2));
\\ residue field F_2: every unit is its own inverse modulo al, a a_i = 1 + al c_a with a_i = 1
unitc(a) = { if (vw(a) != 0, error("not a unit")); my(ca = red((a - 1) / A2)); if (denominator(nfalgtobasis(nf, ca)) != 1, error("unitc")); [cz(1), cz(ca)]; }
\\ greedy square root (count_certs.gp): stops at an odd depth or a depth above 2e, else lifts
depth(z) = {
  my(v = vw(z), s = 1, d);
  if (v % 2, return([v, -1, 0]));
  for (i = 1, 4 * E2 + 4, d = vw(red(z - A2^v * s^2)) - v;
    if (d % 2 || d > 2 * E2, break);
    if (d == 2 * E2, break);
    s = red(s + A2^(d / 2)));
  [v, d, red(A2^(v / 2) * s)];
}
out = List();
emitL(name, v) = listput(out, Str("def ", name, " : List Int := ", lst(v)));
emitN(name, n) = listput(out, Str("def ", name, " : Nat := ", n));
\\ the table of powers al^d, d = 0 .. NPOW - 1 (w2alPow), checked in Lean by al^0 = 1 and al^(d+1) = al^d al
NPOW = 81; ALP = vector(NPOW, d, cz(red(A2^(d - 1))));
alp(d) = if (d >= NPOW, error("alp: table too short"), ALP[d + 1]);
\\ the four tests, as KE expressions (Count/AtW2.lean ck_not_isSquare_depth_two_e: al^n from the table)
tests(Y, T, a, ai, ca, a1, ai1, ca1, n, m) = {
  my(al = KLIN(AL2));
  [KSUB(KSUB(Y, KMUL(KLIN(T), KLIN(T))), KMUL(KLIN(alp(n)), KLIN(a))),
   KSUB(KMUL(KLIN(a), KLIN(ai)), KADD(KINT(1), KMUL(al, KLIN(ca)))),
   KSUB(KMUL(KLIN(T), KLIN(T)), KMUL(KLIN(alp(m)), KLIN(a1))),
   KSUB(KMUL(KLIN(a1), KLIN(ai1)), KADD(KINT(1), KMUL(al, KLIN(ca1))))];
}
PRECS = List();
d2ecert(name, YE) = {
  my(Y = red(keval(YE)), r = depth(Y), T, m, n, a, u, a1, u1, ex, pr, flip);
  if (r[2] != 2 * E2, error(Str(name, ": depth ", r[2], " is not 2e")));
  T = r[3]; m = vw(red(T^2)); n = m + 2 * E2;
  chq(vw(red(Y - T^2)) == n, Str(name, ": v(Y - t^2) = ", n, " = v(t^2) + 2e exactly"));
  a = red((Y - T^2) / A2^n); u = unitc(a); a1 = red(T^2 / A2^m); u1 = unitc(a1);
  chq(vw(a) == 0 && vw(a1) == 0, Str(name, ": a, a' are units at w2"));
  ex = tests(YE, cz(T), cz(a), u[1], u[2], cz(a1), u1[1], u1[2], n, m);
  chq(vecmin(apply(q -> keval(q) == 0, ex)), Str(name, ": the four tests are identities in K21"));
  pr = apply(keprec, ex);
  chq(vecmin(vector(4, i, kecheck(ex[i], pr[i]))), Str(name, ": checkK passes at precisions ", pr));
  chq(!vecmax(vector(4, i, kecheck(ex[i], pr[i] - 1))), Str(name, ": negative control, checkK fails at one bit less"));
  flip = cz(a); flip[1] += 1;
  chq(!kecheck(tests(YE, cz(T), flip, u[1], u[2], cz(a1), u1[1], u1[2], n, m)[1], pr[1]), Str(name, ": negative control, a flipped datum fails"));
  \\ the class: 1 + 4 u with u a unit (u = al^24 a / (4 a'))
  chq(vw(red(A2^(2 * E2) * a / (4 * a1))) == 0, Str(name, ": Y / t^2 = 1 + 4 u with u a unit"));
  emitL(Str(name, "T"), cz(T)); emitL(Str(name, "A"), cz(a)); emitL(Str(name, "Ai"), u[1]); emitL(Str(name, "Ca"), u[2]);
  emitL(Str(name, "B"), cz(a1)); emitL(Str(name, "Bi"), u1[1]); emitL(Str(name, "Cb"), u1[2]);
  emitN(Str(name, "n"), n); emitN(Str(name, "m"), m);
  listput(PRECS, [name, pr]);
  printf("%s: not a square at w2, v(Y) = %d, v(t^2) = %d, depth 2e = %d (n = %d, m = %d), precisions %s\n", name, vw(Y), m, n - m, n, m, pr);
}
chq(dnData[1] == dnData[2], "dnData twist independent");
d2ecert("w2d", KLIN(dnData[1]));
d2ecert("w2k0c", KLIN(FnData[1][1]));
\\ a known answer test of the depth: 4 c_1 has odd depth 11 at w2 (CertData w2k1c)
chq(depth(el(FnData[2][1]))[2] == 11, "known answer: 4 c_1 has odd depth 11 at w2");
\\ the power table: al^0 = 1 and al^(d+1) = al^d al (d < NPOW - 1), one precision for all its checks
TAB = concat([KSUB(KLIN(alp(0)), KINT(1))], vector(NPOW - 1, d, KSUB(KLIN(alp(d)), KMUL(KLIN(alp(d - 1)), KLIN(AL2)))));
chq(vecmin(apply(q -> keval(q) == 0, TAB)), "power table: the checks are identities in K21");
TPS = apply(keprec, TAB); TP = vecmax(TPS);
chq(vecmin(apply(q -> kecheck(q, TP), TAB)), Str("power table: checkK passes at precision ", TP));
chq(!kecheck(TAB[[i | i <- [1 .. #TAB], TPS[i] == TP][1]], TP - 1), "power table: negative control, the largest check fails at one bit less");
FL = alp(40); FL[1] += 1;
chq(!kecheck(KSUB(KLIN(FL), KMUL(KLIN(alp(39)), KLIN(AL2))), TP), "power table: negative control, a flipped entry fails");
for (d = 0, NPOW - 1, emitL(Str("w2al_", d), alp(d)));
{ my(s = "def w2alPow : List (List Int) := ["); for (d = 0, NPOW - 1, s = Str(s, "w2al_", d, if (d < NPOW - 1, ", ", ""))); listput(out, Str(s, "]")); }
emitN("w2alPrec", TP);
LF = Str(if (#getenv("LEANOUT"), getenv("LEANOUT"), "../../FurioLombardo/Discharge/SelmerBasis/Count/"), "AtW2Data.lean"); system(Str("rm -f ", LF));
{
  my(s = "/-!\n# Count lane: the depth 2e certificates at w2\n\nGenerated by code/selmer-local-conditions/count_certs_w12.gp (log count_certs_w12.out) from the Lean lists of M3a's DataBruin.lean:\n`46² d` (`w2d`, twist independent) and `4 c_0` (`w2k0c`), `Y - t² = al2^n a`, `t² = al2^m a'`, `n = m + 24`,\nwith `al2^n` read from the table `w2alPow` (`al2^0 = 1`, `al2^(d+1) = al2^d al2`, precision `w2alPrec`).\n-/\n\nnamespace FurioLombardo.Discharge.SelmerBasis.Count.Data\n\n");
  for (i = 1, #out, s = Str(s, out[i], "\n\n"));
  s = Str(s, "end FurioLombardo.Discharge.SelmerBasis.Count.Data\n");
  write1(LF, s); printf("wrote %d definitions to %s\n", #out, LF);
}
printf("precisions: %s\n", Vec(PRECS));
printf("DONE, %d failed checks (%d ok)\n", NFAIL, NOK);
