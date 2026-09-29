\\ log_branch.gp: the branch table of the logarithm bounds and its checks.
\\ Data read from Lean: the boxes of lean/FurioLombardo/M4/Data.lean (T_k.excluded, T_k.constant, T_k.tails, la, qa),
\\ the known lifts (Discharge/M3a/DataBruin.lean liftData, dData, QcData; M1/DataField.lean zkNum, Dz; M1/Basic.lean fL;
\\ Discharge/M3a/Concrete.lean x_i.p), the local field (Discharge/M4Cert/Kv.lean e0, e1, e2; M4Cert/Data.lean theta0).
\\ Libraries (read only): code/covering/centres_ball_lib.gp (the setup and Abel-Prym map of centres_cert.gp), which reads
\\ abel_prym_lib.gp, bruin_form.gp, discs_q2.txt, completion_kv.gp and code/lib/pball.gp.
\\ Parts:
\\ (1) boxes per twist and disc, pairwise disjointness (c = c' mod 2^min(s, s')), total measure;
\\ (2) uniqueness of Y: (a) the derivative of F in the dependent coordinate at the residue point (odd on discs 1, 5 only;
\\     the residue points of discs 2, 3, 4 are singular mod 2); (b) the certificate: with 2^m the 2-part of the content of
\\     G = F(discPt d X Y), (G(X, Y) - G(X, Y')) / (2^m (Y - Y')) is an integer polynomial, odd at every residue;
\\ (3) the branch table: p21_46's liftP root at X = c (negated on the tail of x_2), encoded as (a0 + a1 pi + a2 pi^2)/pi^e;
\\     writes lean/FurioLombardo/Discharge/M4Log/BranchData.lean and log_branch_table.txt;
\\ (4) known answer checks: (a) lamD(c) = log phi(lift_B(c)) - la against the Lean c.y modulo 2^q at every constant box
\\     centre, with a negative control (opposite branch); (b) at the tails, 2 w0 by finite differences on the table's branch
\\     against the Lean t.g modulo 2^20, and the table's lift at Xi against sigma(x_i);
\\ (5) conventions of the reversed model (code evidence) and the linear normalization A of Defs.lean against pbj_log.
\\ Run from code/earlier-computations:
\\   gp -q ../covering/log_branch.gp < /dev/null > ../covering/log_branch.out 2>&1
\\ Env: M4L_MW (pi-adic cap, default 1000), M4L_MW5 (cap of the part 5 numerics, default 2000), M4L_PARTS (default "12345"), M4L_WRITE (0: do not write the Lean file).
default(parisizemax, 1200 * 10^6); default(nbthreads, 1);
MW0 = if (getenv("M4L_MW"), eval(getenv("M4L_MW")), 1000);
PARTS = if (getenv("M4L_PARTS"), getenv("M4L_PARTS"), "12345");
WRITE = if (getenv("M4L_WRITE"), eval(getenv("M4L_WRITE")), 1);
MW5 = if (getenv("M4L_MW5"), eval(getenv("M4L_MW5")), 2000);
read("../covering/centres_ball_lib.gp");
T00 = getabstime();
NFAIL = 0;
fail(msg) = NFAIL++; print("FAIL: ", msg);
ok(c, msg) = if (!c, fail(msg)); c;
haspart(n) = my(v = Vecsmall(PARTS)); #[c | c <- Vec(v), c == 48 + n] > 0;
LEAN = "../../FurioLombardo/";
OUTD = "../covering/";
BRANCHF = Str(if (type(getenv("LEANOUT")) == "t_STR", Str(getenv("LEANOUT"), "FurioLombardo/"), LEAN), "Discharge/M4Log/BranchData.lean");  \\ LEANOUT=<dir>/ writes the Lean file under <dir> instead of lean/
TABF = Str(OUTD, "log_branch_table.txt");

\\ ---------------------------------------------------------------- reading Lean definitions
afterkey(s, key) = {
  my(A = Vecsmall(s), B = Vecsmall(key));
  for (i = 1, #A - #B + 1, if (A[i .. i + #B - 1] == B, return(if (i + #B > #A, "", Strchr(A[i + #B .. #A])))));
  error("afterkey: key not found: ", key);
}
brk(s) = { my(v = Vecsmall(s)); for (i = 1, #v, if (v[i] == 40, v[i] = 91, v[i] == 41, v[i] = 93)); Strchr(v); }
\\ the lines of a Lean file (optionally a sed range), with the anonymous constructor and vector brackets made gp brackets
leanLines(file, rng) = externstr(Str("sed -n '", rng, "' ", file, " | sed -e 's/⟨/[/g' -e 's/⟩/]/g' -e 's/!\\[/[/g'"));
leanDef(L, name) = {
  my(i0 = 0, s = "", v, bal, st);
  for (i = 1, #L, if (startswith(L[i], Str("def ", name, " ")), i0 = i; break));
  chq(i0, Str("Lean definition ", name));
  for (i = i0, #L,
    s = Str(s, " ", L[i]);
    v = Vecsmall(afterkey(s, ":="));
    bal = 0; st = 0;
    for (j = 1, #v, if (v[j] == 91, bal++; st = 1, v[j] == 93, bal--));
    if (st && bal == 0, break);
    if (!st && #[c | c <- Vec(v), c != 32] > 0, break));
  eval(brk(afterkey(s, ":=")));
}
DAT = vector(2, k, leanLines(Str(LEAN, "M4/Data.lean"), Str("/^namespace T", k - 1, "$/,/^end T", k - 1, "$/p")));
EX = vector(2, k, leanDef(DAT[k], "excluded"));
CB = vector(2, k, leanDef(DAT[k], "constant"));
TB = vector(2, k, leanDef(DAT[k], "tails"));
LA = vector(2, k, leanDef(DAT[k], "la"));
QA = vector(2, k, leanDef(DAT[k], "qa"));
{printf("Lean data (M4/Data.lean): twist 0: %d excluded, %d constant, %d tail boxes, qa = %d; twist 1: %d excluded, %d constant, %d tail boxes, qa = %d\n",
  #EX[1], #CB[1], #TB[1], QA[1], #EX[2], #CB[2], #TB[2], QA[2]);}

\\ ---------------------------------------------------------------- (1) boxes
disjoint(b1, b2) = (b1[1] - b2[1]) % 2^min(b1[2], b2[2]) != 0;
part1() = {
  my(tot = 0);
  print("\n== (1) boxes of lane M4's covering per twist and disc (Data.lean; boxAt takes the first box of branchTable, constant then tails)");
  \\ known answers: {0 mod 2, 1 mod 4, 3 mod 4} disjoint of measure 1; negative control {1 mod 4, 5 mod 8} overlap
  my(kat = [[0, 1], [1, 2], [3, 2]], katok = 1);
  for (i = 1, 3, for (j = i + 1, 3, if (!disjoint(kat[i], kat[j]), katok = 0)));
  ok(katok && sum(i = 1, 3, 2^-kat[i][2]) == 1, "part 1 known answer");
  ok(!disjoint([1, 2], [5, 3]), "part 1 negative control");
  printf("  checker: known answer {0 mod 2, 1 mod 4, 3 mod 4} disjoint, measure 1: %d; negative control {1 mod 4, 5 mod 8} flagged as overlap: %d\n",
    katok, !disjoint([1, 2], [5, 3]));
  for (k = 0, 1, for (d = 1, 5,
    my(B = List());
    foreach (EX[k + 1], e, if (e[1] == d, listput(B, [e[2], e[3], "excluded"])));
    foreach (CB[k + 1], e, if (e[1] == d, listput(B, [e[2], e[3], "constant"])));
    foreach (TB[k + 1], e, if (e[1] == d, listput(B, [e[2], e[3], Str("tail x_", e[4])])));
    B = Vec(B);
    my(ov = List(), ms = sum(i = 1, #B, 2^-B[i][2]), nn = [0, 0, 0], unn = 0);
    for (i = 1, #B, for (j = i + 1, #B, if (!disjoint(B[i], B[j]), listput(ov, [B[i], B[j]]))));
    for (i = 1, #B, if (B[i][1] >= 2^B[i][2] || B[i][1] < 0, unn++));
    foreach (B, b, if (b[3] == "excluded", nn[1]++, b[3] == "constant", nn[2]++, nn[3]++));
    tot += #ov;
    printf("  k = %d disc %d: %d excluded, %d constant, %d tail; overlapping pairs %d; measure of the union (sum 2^-s) %s; centres outside [0, 2^s): %d\n",
      k, d, nn[1], nn[2], nn[3], #ov, ms, unn);
    foreach (ov, o, printf("    OVERLAP k = %d disc %d: (c %d, s %d, %s) and (c %d, s %d, %s)\n", k, d, o[1][1], o[1][2], o[1][3], o[2][1], o[2][2], o[2][3]));
    if (#ov, fail(Str("overlap k = ", k, " disc ", d)))));
  printf("  part 1: %d overlapping pairs in total\n", tot);
}

\\ ---------------------------------------------------------------- (2) uniqueness of Y
discPtL(d, X, Y) = {if (d == 1, [2 * X, 2 * Y, 1], d == 2, [1 + 2 * X, 2 * Y, 1], d == 3, [1 + 2 * X, 1 + 2 * Y, 1],
  d == 4, [2 * X, 1, 2 * Y], d == 5, [1 + 2 * X, 1, 2 * Y], error("disc"));}
depv(d) = if (d <= 3, y, z);
part2() = {
  print("\n== (2) uniqueness of the root Y of F(discPt d X Y) = 0 (F = Fq of p21_46, the plane quartic)");
  my(Fl = 'x^4 + 3*'x^3*'y - 3*'x^2*'y*'z - 3*'x^2*'z^2 + 6*'x*'y^3 - 6*'x*'y^2*'z + 3*'x*'y*'z^2 - 2*'x*'z^3 + 4*'y^4 + 2*'y^3*'z - 5*'y*'z^3, nu = 0);
  ok(Fl == Fq, "Fq of p21_46 equals the quartic typed here");
  print("  (a) the criterion as stated: dF/d(dependent coordinate) at the residue point odd for every X mod 2");
  print("  (b) the certificate used: G(X, Y) = F(discPt d X Y) = 2^m G1(X, Y), 2^m = the 2-part of the content of G, and");
  print("      G1(X, Y) - G1(X, Y') = (Y - Y') H(X, Y, Y') with H in Z[X, Y, Y'] odd at every residue: then G(X, .) has at most one root in Z_2");
  for (d = 1, 5,
    my(pt = discPtL(d, 'XX, 'YY), G = substvec(Fq, [x, y, z], pt), Dd = substvec(deriv(Fq, depv(d)), [x, y, z], pt), res = [], H, hres = [], G2, m, rp, sing, H1, h1res = []);
    for (X = 0, 1, for (Y = 0, 1, res = concat(res, substvec(Dd, ['XX, 'YY], [X, Y]) % 2)));
    rp = discPtL(d, 0, 0) % 2;
    sing = vecmax(apply(v -> substvec(deriv(Fq, v), [x, y, z], rp) % 2, [x, y, z])) == 0;
    m = valuation(content(G), 2);
    G2 = substvec(G, ['YY], ['YP]);
    H = (G - G2) / (2^m * ('YY - 'YP));
    chq(denominator(content(H)) == 1 && type(H) == "t_POL", "H integral polynomial");
    for (X = 0, 1, for (Y = 0, 1, for (Yp = 0, 1, hres = concat(hres, substvec(H, ['XX, 'YY, 'YP], [X, Y, Yp]) % 2))));
    printf("  disc %d: (a) dF/d%s at discPt d X Y mod 2 = %s, values at (X, Y) mod 2 %s: %s; residue point %s singular mod 2 (all partials even): %d\n",
      d, depv(d), Dd * Mod(1, 2), res, if (vecmin(res) == 1, "odd", "EVEN"), rp, sing);
    printf("          (b) m = %d, H mod 2 at all (X, Y, Y') mod 2 = %s: %s\n", m, hres, if (vecmin(hres) == 1, "odd, at most one root Y for every X", "NOT odd"));
    if (vecmin(res) != 1, nu++);
    ok(vecmin(hres) == 1, Str("uniqueness certificate disc ", d));
    \\ negative control for (b) on the singular discs: with 2^(m - 1) in place of 2^m the quotient is even
    if (m > 1, H1 = (G - G2) / (2^(m - 1) * ('YY - 'YP));
      for (X = 0, 1, for (Y = 0, 1, for (Yp = 0, 1, h1res = concat(h1res, substvec(H1, ['XX, 'YY, 'YP], [X, Y, Yp]) % 2))));
      printf("          negative control: with 2^%d in place of 2^%d, H mod 2 = %s (even: the checker reports it)\n", m - 1, m, h1res);
      ok(vecmax(h1res) == 0, "part 2 negative control (b)")));
  printf("  (a) fails on %d discs (the residue points of discs 2, 3, 4 are singular points of F mod 2); (b) holds on all 5 discs\n", nu);
  \\ negative control for (a): the derivative in x at the residue point of disc 1 is even
  my(pt = discPtL(1, 'XX, 'YY), Dx = substvec(deriv(Fq, x), [x, y, z], pt), vx = []);
  for (X = 0, 1, for (Y = 0, 1, vx = concat(vx, substvec(Dx, ['XX, 'YY], [X, Y]) % 2)));
  printf("  negative control (a): dF/dx at discPt 1 X Y mod 2 = %s, values %s (even: the checker reports even values)\n", Dx * Mod(1, 2), vx);
  ok(vecmax(vx) == 0, "part 2 negative control (a)");
}

\\ ---------------------------------------------------------------- the point, the lift, the table root
\\ the disc point at the integer X0: [P balls, chart, c1, c (integer approximation of the dependent coordinate), kP, Y]
cpt(d, X0) = {
  my(D = DISCS[d], ch = D[1], c1 = D[2] + 2^D[4] * X0, var = VA[ch][2], F1 = subst(FA[ch], VA[ch][1], c1), c = D[3] + O(2^(NP + 10)), it = 0, Fv, Dv, kP, cb, P, Yp);
  while (valuation(subst(F1, var, c), 2) < NP, c -= subst(F1, var, c) / subst(deriv(F1, var), var, c); it++; chq(it < 400, "Newton"));
  c = truncate(c); Fv = valuation(subst(F1, var, c), 2); Dv = valuation(subst(deriv(F1, var), var, c), 2);
  if (Fv == oo, kP = MW, chq(Fv > 2 * Dv, "Hensel for the point"); kP = Fv - Dv);
  chq(kP >= D[4] && (c - D[3]) % 2^D[4] == 0, "the root lies in the disc");
  cb = pb(c, 3 * kP);
  P = if (ch == 1, [pb_c(c1), cb, pb_one], [pb_c(c1), pb_one, cb]);
  chq(ch == 1 || ch == 2, "chart");
  Yp = (c - D[3]) / 2;
  \\ the representative of p21_46 is discPt d X0 Y exactly (no rescaling), Y = (c - b0)/2 up to O(2^(kP - 1))
  chq(discPtL(d, X0, Yp) == if (ch == 1, [c1, c, 1], [c1, 1, c]), "p21_46's point is discPt d X Y");
  NREP++;
  [P, ch, c1, c, kP, Yp];
}
\\ p21_46's liftP: [P5, wh (1: r, 0: s), the root ball]
liftP46(P, SB, QF) = {
  my(q = vector(3, j, qeval(QF[j], P)), rr, ss);
  rr = if (pb_nz(q[1]), csqrt(pb_div(q[1], SB[7])), 0);
  if (rr != 0, ss = pb_div(q[2], pb_mul(SB[7], rr)); return([concat(P, [rr, ss]), 1, rr]));
  ss = csqrt(pb_div(q[3], SB[7])); chq(ss != 0, "a lift to D_delta(K_v)"); rr = pb_div(q[2], pb_mul(SB[7], ss));
  [concat(P, [rr, ss]), 0, ss];
}
\\ the lift of P on the branch (wh, rho): the root of Q_wh/delta nearest rho (Newton from rho, certified), then the
\\ certified branch condition |x - rho| < |x + rho| and the lift equations within the balls
liftTab(P, SB, QF, wh, rho) = {
  my(q = vector(3, j, qeval(QF[j], P)), al = pb_div(q[if (wh, 1, 3)], SB[7]), rb, o, P5, vm, vp);
  rb = pb_sqrt_cert(al, pb_sqrt_newton(al, rho, 14));
  chq(rb != 0, "liftTab: certified square root");
  vp = pb_vc(rb[1] + rho); vm = min(rb[2], pb_vc(rb[1] - rho));
  chq(vp < rb[2] && vm > vp, "liftTab: certified branch condition");
  o = pb_div(q[2], pb_mul(SB[7], rb));
  P5 = if (wh, concat(P, [rb, o]), concat(P, [o, rb]));
  my(e1 = pb_sub(q[1], pb_mul(SB[7], pb_mul(P5[4], P5[4]))), e2 = pb_sub(q[2], pb_mul(SB[7], pb_mul(P5[4], P5[5]))), e3 = pb_sub(q[3], pb_mul(SB[7], pb_mul(P5[5], P5[5]))));
  chq(!pb_nz(e1) && !pb_nz(e2) && !pb_nz(e3), "liftTab: lift equations");
  [P5, vm - vp];
}
\\ encoding of a root ball: [v, e, [a0, a1, a2] (exact integers of pi^e centre), ball precision]
enc(rb) = {
  my(c = rb[1], v = pb_vc(c), e = max(0, -v), w = lift(c * Mod(PBV, PB_EP)^e), a = vector(3, i, polcoef(w, i - 1, PBV)));
  chq(vecmax(apply(denominator, a)) == 1, "enc: integral coordinates");
  [v, e, a, rb[2]];
}
decT(a, e) = Mod(a[1] + a[2] * PBV + a[3] * PBV^2, PB_EP) / Mod(PBV, PB_EP)^e;

\\ ---------------------------------------------------------------- (3) the branch table
TAB = vector(2); SBK = vector(2); QFK = 0; PGLOB = 0; NREP = 0;
part3() = {
  print("\n== (3) the branch table (p21_46 liftP root at X = c; negated on the tail of x_2)");
  QFK = [qform(Q1), qform(Q2), qform(Q3)];
  my(raw = vector(2));
  for (k = 0, 1,
    SBK[k + 1] = bapm_init(k);
    my(L = List(), bx = concat(apply(e -> [e[1], e[2], e[3], 0, -1], CB[k + 1]), apply(e -> [e[1], e[2], e[3], 1, e[4]], TB[k + 1])));
    foreach (bx, b,
      my(cp = cpt(b[1], b[2]), lp = liftP46(cp[1], SBK[k + 1], QFK), rb = lp[3], flip = (k == 0 && b[4] == 1 && b[5] == 2), en);
      if (flip, rb = pb_neg(rb));
      en = enc(rb);
      listput(L, [b[1], b[2], b[3], lp[2], en, b[4], b[5], flip, cp[5]]));
    raw[k + 1] = Vec(L));
  \\ the common P: 3 P - e >= v + 30 for every entry, so reducing a_i modulo 2^P keeps v(rho - table) >= v + 30
  printf("  the point of p21_46 (cpoint) at the %d centres is discPt d c Y exactly, Y = (y_c - b0)/2, no rescaling: %d of %d\n", NREP, NREP, #raw[1] + #raw[2]);
  ok(NREP == #raw[1] + #raw[2], "representatives");
  PGLOB = vecmax(concat(apply(R -> vecmax(apply(r -> ceil((r[5][1] + r[5][2] + 30) / 3), R)), raw)));
  printf("  P = %d (a_i reduced to [0, 2^P))\n", PGLOB);
  for (k = 0, 1,
    TAB[k + 1] = vector(#raw[k + 1], i, my(r = raw[k + 1][i], en = r[5], aP = apply(t -> t % 2^PGLOB, en[3]), rt = decT(aP, en[2]), vd);
      \\ vd: v(rho_exact - rho_table) >= min(ball precision, v(table - centre))
      vd = min(en[4], pb_vc(rt - decT(en[3], en[2])));
      chq(vd >= en[1] + 30, "table root correct to v + 30");
      [r[1], r[2], r[3], r[4], aP, en[2], en[1], vd, r[6], r[7], r[8], r[9]]);
    printf("  twist %d: %d entries (%d constant, %d tail); wh = r on %d, s on %d; v(rho) in [%d, %d]; e in [%d, %d]; min of v(rho_exact - rho_table) - v(rho): %d\n",
      k, #TAB[k + 1], #CB[k + 1], #TB[k + 1], #[t | t <- TAB[k + 1], t[4] == 1], #[t | t <- TAB[k + 1], t[4] == 0],
      vecmin(apply(t -> t[7], TAB[k + 1])), vecmax(apply(t -> t[7], TAB[k + 1])), vecmin(apply(t -> t[6], TAB[k + 1])), vecmax(apply(t -> t[6], TAB[k + 1])),
      vecmin(apply(t -> t[8] - t[7], TAB[k + 1])));
    foreach (TAB[k + 1], t, printf("    k=%d %s disc %d c %d s %d: wh %s, rho = (%d, %d, %d) / pi^%d, v(rho) %d, v(rho_exact - rho_table) >= %d, Hensel precision of the point 2^-%s%s\n",
      k, if (t[9], Str("tail x_", t[10]), "const"), t[1], t[2], t[3], if (t[4], "r", "s"), t[5][1], t[5][2], t[5][3], t[6], t[7], t[8], if (t[12] == MW, "exact", t[12]),
      if (t[11], " (negated: tail of x_2)", ""))));
  \\ outputs
  system(Str("rm -f ", TABF));
  for (k = 0, 1, foreach (TAB[k + 1], t, write(TABF, [k, t[1], t[2], t[3], t[4], t[5], t[6], t[7], t[9]])));
  if (WRITE, writelean());
}
leanentry(t) = Str("⟨", t[1], ", ", t[2], ", ", t[3], ", ", if (t[4], "true", "false"), ", (", t[5][1], ", ", t[5][2], ", ", t[5][3], "), ", t[6], "⟩");
writelean() = {
  my(f = BRANCHF);
  system(Str("rm -f ", f));
  write(f, "import Mathlib\n");
  write(f, "/-!\n# Branch table of lane lean-m4log (generated by code/covering/log_branch.gp, PARI/GP)\n");
  write(f, Str("An entry `⟨disc, c, s, wh, (a0, a1, a2), e⟩` of `branchTable k` is a box `{X : X ≡ c mod 2^s}` of the disc `disc` of\n",
    "lane M4's covering (lean/FurioLombardo/M4/Data.lean, the constant boxes of `T_k.constant` then the tail boxes of\n",
    "`T_k.tails`, in that order) with its branch: over the disc point `pKv disc X` the lift `x` of `D_δ(K_v)` with\n",
    "`‖x.r - ρ‖ < ‖x.r + ρ‖` (`wh = true`) or `‖x.s - ρ‖ < ‖x.s + ρ‖` (`wh = false`), where\n",
    "`ρ = (a0 + a1 pv + a2 pv²) / pv ^ e`. The reference root `ρ` is the root chosen by `liftP` of\n",
    "code/earlier-computations/centres_cert.gp at the box centre `X = c` (`r = √(Q1/δ)` when `Q1(P(c))` is certified\n",
    "nonzero and a square, else `s = √(Q3/δ)`), negated on the tail box of `x_2` (twist 0, disc 1, `Xi = 1`), whose branch has\n",
    "`2 w0 = +t.g`. It is correct to `v_pv(ρ) + 30`: `v_pv(ρ_exact - ρ) ≥ v_pv(ρ) + 30`, with `a_i` reduced to `[0, 2^", PGLOB, ")`.\n-/\n"));
  write(f, "namespace FurioLombardo.Discharge.M4Log\n");
  write(f, Str("/-- A box `(disc, c, s)` of lane M4's covering with its branch: `wh = true` fixes the lift by `r`,\n",
    "`false` by `s`; the reference root is `(rho.1 + rho.2.1 pv + rho.2.2 pv²) / pv ^ e`. -/\n",
    "structure BranchBox where\n  disc : ℕ\n  c : ℕ\n  s : ℕ\n  wh : Bool\n  rho : ℤ × ℤ × ℤ\n  e : ℕ\nderiving DecidableEq\n"));
  write(f, "/-- The branch table of twist `k`: the constant boxes of `T_k.data.constant`, then the tail boxes of `T_k.data.tails`, in the order of Data.lean. -/");
  write(f, "def branchTable : Fin 2 → List BranchBox");
  for (k = 0, 1, write(f, Str("  | ", k, " => [", strjoin(apply(leanentry, TAB[k + 1]), ",\n    "), "]")));
  write(f, "\nend FurioLombardo.Discharge.M4Log");
  printf("  wrote %s (%d + %d entries) and %s\n", f, #TAB[1], #TAB[2], TABF);
}

\\ ---------------------------------------------------------------- (4a) the centres of the constant boxes
LOGN = 2^4 * NM; TGT4 = 200;
lamlog(SB, D, tg) = iferr(pbj_log(SB[8], D, LOGN, tg), E, pbj_log(SB[8], D, 2^5 * NM, tg))[1];
part4a() = {
  print("\n== (4a) lamD(c) = log phi(lift_B(c)) - log phi_a with the table's branch, against the Lean c.y modulo 2^q");
  printf("  MW = %d pi-digits, pbj_log with N = 2^4 * %d (2^5 on failure), target %d; log phi_a = the Lean la (modulo 2^qa)\n", MW, NM, TGT4);
  for (k = 0, 1,
    my(SB = SBK[k + 1], nagree = 0, nfull = 0, nsame = 0, minp = 10^9, t0 = getabstime(), neg = 0);
    for (i = 1, #CB[k + 1],
      my(cb = CB[k + 1][i], t = TAB[k + 1][i], cp, lt, l46, D, L, co, lam, pe, ag, same);
      chq(t[1] == cb[1] && t[2] == cb[2] && t[3] == cb[3] && t[9] == 0, "table order");
      cp = cpt(cb[1], cb[2]);
      lt = liftTab(cp[1], SB, QFK, t[4], decT(t[5], t[6]));
      l46 = liftP46(cp[1], SB, QFK);
      same = l46[2] == t[4] && !pb_nz(pb_sub(lt[1][4], l46[1][4])) && !pb_nz(pb_sub(lt[1][5], l46[1][5]));
      D = bapm_phi(SB, lt[1]);
      L = lamlog(SB, D, TGT4); co = lvec(L);
      lam = vector(6, j, co[1][j] - LA[k + 1][j]);
      pe = vecmin(concat([cb[6], QA[k + 1]], co[2]));
      ag = vecmin(vector(6, j, my(dd = lam[j] - cb[7][j]); denominator(dd) % 2 == 1 && valuation(numerator(dd), 2) >= pe));
      minp = min(minp, vecmin(co[2]));
      if (ag, nagree++); if (pe >= cb[6], nfull++); if (same, nsame++);
      if (!ag || pe < cb[6] || !same, printf("    NOTE k=%d disc %d c %d s %d: agreement %d modulo 2^%d (q = %d), same lift as p21_46 %d\n", k, cb[1], cb[2], cb[3], ag, pe, cb[6], same));
      \\ negative control on the first box: the opposite branch must disagree with c.y
      if (i == 1,
        my(ln = liftTab(cp[1], SB, QFK, t[4], -decT(t[5], t[6])), Dn = bapm_phi(SB, ln[1]), Ln = lvec(lamlog(SB, Dn, TGT4)), lamn = vector(6, j, Ln[1][j] - LA[k + 1][j]),
           agn = vecmin(vector(6, j, my(dd = lamn[j] - cb[7][j]); denominator(dd) % 2 == 1 && valuation(numerator(dd), 2) >= pe)));
        neg = !agn;
        printf("  negative control k=%d disc %d c %d s %d, opposite branch: agreement with c.y modulo 2^%d: %d (0 expected)\n", k, cb[1], cb[2], cb[3], pe, agn)));
    printf("  twist %d: %d constant box centres; agreement with c.y: %d; comparison precision >= q: %d; table lift = p21_46 lift: %d; least 2-adic precision of the log coordinates %d; negative control ok %d (%d ms)\n",
      k, #CB[k + 1], nagree, nfull, nsame, minp, neg, getabstime() - t0);
    ok(nagree == #CB[k + 1] && nfull == #CB[k + 1] && nsame == #CB[k + 1] && neg, Str("part 4a twist ", k)));
}

\\ ---------------------------------------------------------------- (4b) the tails
\\ zk coordinates of M1 -> K21: zkE(a) = sum a_j zkNum_j(theta) / Dz
ZKL = leanLines(Str(LEAN, "M1/DataField.lean"), "1,$p");
ZKNUM = leanDef(ZKL, "zkNum"); DZ = leanDef(ZKL, "Dz");
FL = leanDef(leanLines(Str(LEAN, "M1/Basic.lean"), "1,$p"), "fL");
zkE(a) = Mod(sum(j = 1, 21, a[j] * Polrev(ZKNUM[j], b)), K21) / DZ;
BRL = leanLines(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "1,$p");
LIFTD = leanDef(BRL, "liftData"); DDATA = leanDef(BRL, "dData"); QCD = leanDef(BRL, "QcData");
XP = vector(4, i, eval(brk(afterkey(externstr(Str("grep -A1 'def x", i - 1, " ' ", LEAN, "Discharge/M3a/Concrete.lean | tail -1 | sed -e 's/!\\[/[/'"))[1], ":="))));
part4b() = {
  print("\n== (4b) tails: 2 w0 on the table's branch against t.g, and the table's lift at Xi against sigma(x_i)");
  \\ the Lean data of K21 against bruin_form.gp
  ok(Polrev(FL, b) == K21, "fL = K21");
  my(mons = [x^2, x*y, x*z, y^2, y*z, z^2], Qs = [Q1, Q2, Q3], qok = 1, dok);
  for (i = 1, 3, for (j = 1, 6, my(m = mons[j], c = polcoef(polcoef(polcoef(Qs[i], poldegree(m, x), x), poldegree(m, y), y), poldegree(m, z), z));
    if (zkE(QCD[i][j]) != Mod(c, K21), qok = 0)));
  dok = zkE(DDATA[1]) == Mod(d0, K21) && zkE(DDATA[2]) == Mod(d1, K21);
  printf("  Lean data: fL = K21 %d; QcData = Q1, Q2, Q3 of bruin_form %d; dData = [d0, d1] %d; x_i.p (Concrete.lean) = %s\n", Polrev(FL, b) == K21, qok, dok, XP);
  ok(qok && dok, "QcData, dData");
  \\ the local field: E of M4Cert/Kv.lean and theta0 of M4Cert/Data.lean against completion_kv.gp
  my(KVL = leanLines(Str(LEAN, "Discharge/M4Cert/Kv.lean"), "1,$p"), EL = 'x^3 + leanDef(KVL, "e2") * 'x^2 + leanDef(KVL, "e1") * 'x + leanDef(KVL, "e0"),
     th0 = leanDef(leanLines(Str(LEAN, "Discharge/M4Cert/Data.lean"), "1,$p"), "θ0"), vth);
  vth = pb_vc(KV_TH[1] - decT(th0, 0));
  printf("  local field: E of M4Cert = E of p21_44 %d; v_pi(theta* of p21_44 - theta0 of M4Cert) = %d (>= 99 needed: sigma of M4Cert = kv of p21_44)\n", subst(EL, 'x, PBV) == PB_EP, vth);
  ok(subst(EL, 'x, PBV) == PB_EP && vth >= 99, "local field");
  for (k = 0, 1,
    my(SB = SBK[k + 1], nc = #CB[k + 1]);
    for (it = 1, #TB[k + 1],
      my(tb = TB[k + 1][it], t = TAB[k + 1][nc + it], d = tb[1], Xi = tb[5], ix = tb[4], rho = decT(t[5], t[6]), cp, lt, l46, same46, opp46, xr, xs, lam, sg, D0, L0, ests = List(), gd, xpt);
      chq(t[1] == d && t[2] == tb[2] && t[9] == 1 && t[10] == ix, "tail order");
      cp = cpt(d, Xi);
      lt = liftTab(cp[1], SB, QFK, t[4], rho);
      l46 = liftP46(cp[1], SB, QFK);
      same46 = !pb_nz(pb_sub(lt[1][4], l46[1][4])) && !pb_nz(pb_sub(lt[1][5], l46[1][5]));
      opp46 = !pb_nz(pb_add(lt[1][4], l46[1][4])) && !pb_nz(pb_add(lt[1][5], l46[1][5]));
      \\ sigma(x_i): the Lean lift (zk coordinates) mapped to K_v; x_i.p rescaled to the representative discPt d Xi Y
      xpt = XP[ix + 1];
      my(Pint = if (cp[2] == 1, [cp[3], cp[4], 1], [cp[3], 1, cp[4]]), lm);
      chq(cp[5] == MW, "the known point is an exact disc point");
      lm = if (xpt[3] != 0, Pint[3] / xpt[3], Pint[2] / xpt[2]);
      chq(Pint == lm * xpt, "x_i.p is proportional to discPt d Xi Y");
      my(rk = zkE(LIFTD[ix + 1][1]), sk = zkE(LIFTD[ix + 1][2]), dl = Mod(if (k == 0, d0, d1), K21), Pk = xpt, qv = vector(3, j, substvec(Qs[j], [x, y, z], Pk) * Mod(1, K21)));
      chq(qv[1] == dl * rk^2 && qv[2] == dl * rk * sk && qv[3] == dl * sk^2, "lift equations of x_i over K21");
      xr = pb_scal(lm, kv(rk)); xs = pb_scal(lm, kv(sk));
      my(eq = !pb_nz(pb_sub(lt[1][4], xr)) && !pb_nz(pb_sub(lt[1][5], xs)), cj = !pb_nz(pb_add(lt[1][4], xr)) && !pb_nz(pb_add(lt[1][5], xs)));
      printf("  k=%d tail x_%d disc %d c %d s %d Xi %d: table branch (wh %s) at Xi: certified margin %d; = p21_46 liftP at Xi %d, opposite %d; = sigma(x_%d) (scale %d) %d, = conjugate (-r, -s) %d\n",
        k, ix, d, tb[2], tb[3], Xi, if (t[4], "r", "s"), lt[2], same46, opp46, ix, lm, eq, cj);
      ok(eq != cj, "tail lift is sigma(x_i) or its conjugate, exactly one");
      \\ finite differences: 2 (lam(Xi + h) - lam(Xi)) / h, h = 2^j, on the table's branch at both points
      D0 = bapm_phi(SB, lt[1]); L0 = lamlog(SB, D0, 300);
      gd = vector(6, i, red2(tb[10][i], 20));
      foreach ([20, 25, 30], j,
        my(h = 2^j, cq = cpt(d, Xi + h), lh = liftTab(cq[1], SB, QFK, t[4], rho), Dh = bapm_phi(SB, lh[1]), Lh = lamlog(SB, Dh, 300),
           g2 = vector(2, c, pb_scal(2 / h, pb_sub(Lh[c], L0[c]))), gc = lvec(g2), pr = vecmin(gc[2]), gp, gm, ap, am);
        chq(pr >= 20, "finite difference precision");
        gp = apply(c -> red2(c, 20), gc[1]~); gm = apply(c -> red2(-c, 20), gc[1]~);
        ap = gp == gd; am = gm == gd;
        listput(ests, [j, gc[1], pr, ap, am]);
        printf("    h = 2^%d: 2 (lam(Xi + h) - lam(Xi))/h mod 2^20 = %s (2-adic precision %d); Lean t.g mod 2^20 = %s; = +t.g: %d, = -t.g: %d\n", j, gp, pr, gd, ap, am));
      \\ stability of the estimates: 2-adic valuation of the differences between successive h
      my(E = Vec(ests), dv = vector(#E - 1, i, vecmin(vector(6, c, my(dd = E[i + 1][2][c] - E[i][2][c]); if (dd == 0, oo, valuation(dd, 2))))));
      printf("    2-adic valuation of the difference of the estimates between h = 2^20, 2^25, 2^30: %s\n", dv);
      ok(vecmin(apply(e -> e[4], E)) == 1, Str("2 w0 = +t.g at the tail x_", ix))));
}

\\ ---------------------------------------------------------------- (5) conventions and the normalization A
grepl(pat, file) = externstr(Str("grep -n -m 3 -F -e '", pat, "' ", file));
evid(lab, pat, file) = { my(r = grepl(pat, file)); printf("  [%s] %s:\n", lab, file); foreach (r, l, printf("      %s\n", l)); ok(#r > 0, Str("evidence ", lab)); }
frevB(k) = kvx(polrecip(if (k == 0, F0, F1)));
\\ [U, V] on y^2 = f -> [U', V'] on Y^2 = X^6 f(1/X): U' = U^rev / U(0), V' = X^3 V(1/X) mod U' (the same map back)
revD(D) = {
  my(U = D[1], V = pbx_pad(D[2], 2), ui, up, vp);
  chq(pb_nz(U[1]), "reversal: u(0) certified nonzero");
  ui = pb_inv(U[1]); up = [ui, pb_mul(U[2], ui), pb_one];
  vp = pbx_divrem([pb_zero, pb_zero, V[2], V[1]], up)[2];
  [up, pbx_pad(vp, 2)];
}
part5() = {
  print("\n== (5) conventions of the reversed model, and the linear normalization A against lane M4's pbj_log");
  print("  code evidence:");
  evid("pball: logarithm for (dx/y, x dx/y)", "Logarithm for (dx/y, x dx/y)", "../lib/pball.gp");
  evid("pball: tiny log, I1 = int g dz, I2 = int (x1 + z) g dz", "int_0^s (x1 + z) g dz", "../lib/pball.gp");
  evid("pball: chart at infinity, log = (-l2', -l1')", "(dx/y, x dx/y) = (-X dX/Y, -dX/Y)", "../lib/pball.gp");
  evid("pball: pbj_tinylog_inf returns (-l'_2, -l'_1)", "[1, [pb_neg(r[2][2]), pb_neg(r[2][1])], r[3]]", "../lib/pball.gp");
  evid("p21_46: f = F_k in pbj_log", "kvx(subst(Fk, t,", "centres_cert.gp");
  evid("p21_46: pbj_log(SB[8], ...)", "pbj_log(SB[8], D, 2^4 * NM, TGT)", "centres_cert.gp");
  evid("p21_45: f = F_k in pbj_log", "f = kvxx(subst(if (k == 0, F0, F1), t,", "lattice_cert.gp");
  evid("chart_lib: frev = polrecip", "frev = vector(2, k, polrecip(fk[k]));", "../local-group/chart_lib.gp");
  evid("Lean fRev = reverse of f_k", "theorem fRev_eq_reverse", Str(LEAN, "Discharge/M3a/Concrete.lean"));
  evid("ss_7: D_i on the reversed model", "on the reversed model Y^2 = g, g = (fRev k)^sigma", "../local-group/local_divisors_data.gp");
  evid("ss_7: D_i reversed u, v", "(reversed, t^3 v(1/t) mod U)", "../local-group/local_divisors_data.gp");
  evid("AbelPrymKnown: phi transported", "V(1/t) mod U", Str(LEAN, "Discharge/M3a/AbelPrymKnown.lean"));
  evid("Defs.lean: Amat", "(bK k)⁻¹ • !![aK k, 1 + aK k * g1K k; 1, g1K k]", Str(LEAN, "Discharge/M4Log/Defs.lean"));
  \\ numerics, at a larger cap (the tiny logarithm of chi(t) - E0 loses up to about 450 digits at MW = 1000 for some t)
  my(r5 = kv_init(MW5));
  printf("  numerics at MW = %d (local field re-initialized: E = %s)\n", PB_MW, r5[1]);
  my(PI = Mod(PBV, PB_EP), pts = [[PI^25 * (1 + PI), PI^26 * (3 + PI^2)], [PI^26 * (1 + PI^2), 5 * PI^25]]);
  for (k = 0, 1,
    my(SB8 = kvx(subst(if (k == 0, F0, F1), t, 'x)), Fr = frevB(k), a = k, fa = pbx_eval(Fr, pb_c(a)), bb = csqrt(fa), Fd, fp, v1, E0, A);
    chq(bb != 0, "F(a) is a square");
    Fd = vector(6, i, pb_scal(i, Fr[i + 1])); fp = pbx_eval(Fd, pb_c(a)); v1 = pb_div(fp, pb_scal(2, bb));
    E0 = [[pb_c(a^2), pb_c(-2 * a), pb_one], [pb_sub(bb, pb_scal(a, v1)), v1]];
    my(bi = pb_inv(bb), g1 = pb_neg(pb_mul(v1, bi)));
    A = [[pb_scal(a, bi), pb_mul(bi, pb_add(pb_one, pb_scal(a, g1)))], [bi, pb_mul(bi, g1)]];
    my(vs = (c -> my(w = pb_vc(c[1])); if (w >= PB_INF, "oo", Str(w))));
    printf("  twist %d: a = %d, v(b) = %d, v(v1) = %d, v(A) = [%s, %s; %s, %s] (oo: the entry a/b is 0)\n", k, a, pb_vc(bb[1]), pb_vc(v1[1]), vs(A[1][1]), vs(A[1][2]), vs(A[2][1]), vs(A[2][2]));
    foreach (pts, tq,
      my(t0 = pb(tq[1], PB_MW), t1 = pb(tq[2], PB_MW), U, V0, V, chi, Q, Lr, lamQ, Qo, Lo, At, dA, dW, vt);
      \\ u_t(X - a), X^2 + t0 X + t1 in the translated variable
      U = [pb_add(pb_sub(pb_c(a^2), pb_scal(a, t0)), t1), pb_sub(t0, pb_c(2 * a)), pb_one];
      V0 = [pb_sub(bb, pb_scal(a, v1)), v1];
      V = pbj_refine(Fr, U, V0, 12);
      chi = pbj_genuine(Fr, U, V); chq(chi != 0, "chi(t) certified");
      Q = pbj_add(Fr, chi, pbj_neg(E0));
      Lr = iferr(pbj_log(Fr, Q, 1, 250)[1], E, pbj_log(Fr, Q, LOGN, 250)[1]);
      lamQ = [pb_neg(Lr[2]), pb_neg(Lr[1])];
      \\ the same on the original model after the transport (x, y) -> (1/x, y/x^3)
      Qo = revD(Q);
      Lo = iferr(pbj_log(SB8, Qo, 1, 250)[1], E, pbj_log(SB8, Qo, LOGN, 250)[1]);
      At = vector(2, i, pb_add(pb_mul(A[i][1], t0), pb_mul(A[i][2], t1)));
      dA = min(pb_val(pb_sub(lamQ[1], At[1])), pb_val(pb_sub(lamQ[2], At[2])));
      dW = min(pb_val(pb_sub(Lr[1], At[1])), pb_val(pb_sub(Lr[2], At[2])));
      vt = min(pb_vc(t0[1]), pb_vc(t1[1]));
      my(dT = min(pb_val(pb_sub(Lo[1], lamQ[1])), pb_val(pb_sub(Lo[2], lamQ[2]))));
      printf("    t = (pi^%d u, pi^%d u'): v(t) = %d; v(lambda(Q)) = %d; v(lambda(Q) - A t) = %d (2 v(t) = %d); negative control, no swap (l1, l2 of the reversed model): v(l - A t) = %d; transport check v(log on the original model - (-l2, -l1)) >= %d (precisions %d, %d)\n",
        pb_vc(t0[1]), pb_vc(t1[1]), vt, min(pb_vc(lamQ[1][1]), pb_vc(lamQ[2][1])), dA, 2 * vt, dW, dT, min(Lr[1][2], Lr[2][2]), min(Lo[1][2], Lo[2][2]));
      ok(dA > vt + 10 && dW < dA - 10 && dT >= 100 && min(min(Lr[1][2], Lr[2][2]), min(Lo[1][2], Lo[2][2])) >= 2 * vt + 20, "part 5 normalization")));
}

\\ ---------------------------------------------------------------- main
{
  my(r0 = kv_init(MW));
  printf("setup: MW = %d, E = %s, embedding precision %d (%d ms)\n", MW, r0[1], r0[2], getabstime() - T00);
  if (haspart(1), part1());
  if (haspart(2), part2());
  if (haspart(3) || haspart(4) || haspart(5), part3());
  if (haspart(4), part4a(); part4b());
  if (haspart(5), part5());
  printf("\nRESULT: %s (parts %s, %d failures, %d ms)\n", if (NFAIL == 0, "all checks passed", "FAILURES"), PARTS, NFAIL, getabstime() - T00);
  print("END");
}
quit;
