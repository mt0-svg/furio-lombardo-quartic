\\ real_roots.gp: the real roots of fRev 0 at the real places 5 and 6 of K21.
\\ Data read from the Lean sources: fL (M1/Basic.lean), Dz, zkNum (M1/DataField.lean), FnData, qData, hData, qDen, hDen
\\ (Discharge/M3a/DataBruin.lean), epsL (Discharge/M3b/K21Defs.lean), Dr, rtA, rtB (Discharge/M3b/K21Real.lean).
\\ 1. Places: realEmb k (theta in (rtA k / Dr, rtB k / Dr)) is beta_(k+1), the (k+1)-th real root of fL, and nfinit's
\\    roots are sorted the same way, so places 5, 6 of selmer_bound_subsets / p21_29 (place 4 + i = beta_i) are realEmb 0, 1.
\\ 2. h 0 = hp * conj(hp) over L42 = K21(w), w^2 = eps: hp = X^2 + (p0 + p1 w) X + (r0 + r1 w), p_i, r_i in K21
\\    (resolvent cubic in u = eps p1^2, a root of it in K21 with u / eps a square), checked exactly.
\\ 3. At beta_1, beta_2: exact signs (Sturm on rational isolating intervals) of q 0 (s), h 0 (s) at simple rational
\\    separators s0..s4, of Delta1 and N(Delta) (Delta = p^2 - 4 r, disc of hp), and the resulting root layout.
\\ 4. Writes the Lean data file RealRootData.lean (zk lists scaled to integers; identities checked in Lean by checkK).
\\ Run from code/selmer-local-conditions: gp -q real_roots.gp < /dev/null (LEANOUT=<dir>/ writes RealRootData.lean to <dir> instead)
[x, b, w];
default(parisizemax, 900 * 10^6);
default(realprecision, 60);
default(nbthreads, 1);
NF = 0; RAN = List();
chq(c, msg) = listput(RAN, msg); if (c, printf("ok: %s\n", msg), NF++; printf("CHECK FAILED: %s\n", msg));
LEAN = "../../FurioLombardo/";
startswith(s, p) = my(A = Vecsmall(s), B = Vecsmall(p)); #A >= #B && A[1 .. #B] == B;
isblank(s) = my(A = Vecsmall(s)); #[c | c <- A, c != 32 && c != 9] == 0;
\\ the text of a Lean `def nm ... := <value>` (after ":=", up to a blank line), with the characters "!" removed
getraw(fn, nm) = {
  my(L = readstr(fn), pre = Str("def ", nm, " "), acc = "", on = 0);
  for (i = 1, #L, my(s = L[i]);
    if (!on,
      if (startswith(s, pre), on = 1; my(A = Vecsmall(s), p = 0);
        for (j = 1, #A - 1, if (A[j] == 58 && A[j + 1] == 61, p = j; break));
        if (p == 0, error("no := in ", s)); acc = Strchr(A[p + 2 .. #A])),
      if (isblank(s) || startswith(s, "/-") || startswith(s, "def ") || startswith(s, "theorem"), break);
      acc = Str(acc, s)));
  if (!on, error("no def ", nm, " in ", fn));
  Strchr([c | c <- Vecsmall(acc), c != 33]);
}
getdef(fn, nm) = eval(getraw(fn, nm));
fL = getdef(Str(LEAN, "M1/Basic.lean"), "fL");
Dz = getdef(Str(LEAN, "M1/DataField.lean"), "Dz");
zkNum = getdef(Str(LEAN, "M1/DataField.lean"), "zkNum");
FnData = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "FnData");
qData = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qData");
hData = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hData");
qDen = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "qDen");
hDen = getdef(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "hDen");
epsL = getdef(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL");
Dr = getdef(Str(LEAN, "Discharge/M3b/K21Real.lean"), "Dr");
rtA = getdef(Str(LEAN, "Discharge/M3b/K21Real.lean"), "rtA");
rtB = getdef(Str(LEAN, "Discharge/M3b/K21Real.lean"), "rtB");
chq(#fL == 22 && #zkNum == 21 && #epsL == 21 && #rtA == 3 && #rtB == 3, "Lean data parsed (fL, zkNum, FnData, qData, hData, qDen, hDen, epsL, Dr, rtA, rtB)");
fZ = Pol(Vecrev(fL), 'b);
chq(polisirreducible(fZ), "fZ irreducible");
W = vector(21, j, Pol(Vecrev(zkNum[j]), 'b) / Dz);
zkE(a) = Mod(sum(j = 1, 21, a[j] * W[j]), fZ);
Mz = matrix(21, 21, i, j, polcoef(W[j], i - 1, 'b));
Mzi = Mz^-1;
\\ zk coordinates of g in K21
zkc(g) = my(G = lift(Mod(1, fZ) * g)); (Mzi * vectorv(21, i, polcoef(G, i - 1, 'b)))~;
chq(zkc(zkE(epsL)) == epsL, "zkc inverts zkE");
\\ integral zk list of D * g and the denominator D
zkint(g) = my(v = zkc(g), D = denominator(v)); [D, D * v];
fRev0 = sum(j = 0, 6, zkE(FnData[1][7 - j]) / 4 * 'x^j);
q0 = 'x^2 + zkE(qData[1][2]) / qDen[1] * 'x + zkE(qData[1][1]) / qDen[1];
h0 = 'x^4 + sum(j = 0, 3, zkE(hData[1][j + 1]) / hDen[1] * 'x^j);
c0 = zkE(FnData[1][1]) / 4;
chq(fRev0 == c0 * q0 * h0, "fRev 0 = c q h over K21");
eps = zkE(epsL);
\\ ---------------------------------------------------------------- 1. places
RT = polrootsreal(fZ);
chq(#RT == 3, "K21 has exactly 3 real embeddings");
for (k = 1, 3, chq(rtA[k] / Dr < RT[k] && RT[k] < rtB[k] / Dr, Str("realEmb ", k - 1, " (root interval (rtA, rtB) / Dr) is beta_", k, " = ", precision(RT[k], 15))));
{
  my(nfK = nfinit([fZ, 10]));
  chq(nfK.r1 == 3 && vecmax(vector(3, i, abs(nfK.roots[i] - RT[i]))) < 10^-30, "nfinit(K21).roots[1..3] = beta_1 < beta_2 < beta_3, so place 4 + i = beta_i = realEmb (i - 1): places 5, 6 are realEmb 0, 1");
}
ISO = vector(3, i, my(lo = floor(RT[i] * 10^30) / 10^30, hi = lo + 1 / 10^30); [lo, hi]);
for (i = 1, 3, chq(polsturm(fZ, ISO[i]) == 1, Str("isolating interval of beta_", i)));
sgnK(g, i) = {
  my(G = lift(Mod(1, fZ) * g), I = ISO[i]);
  if (G == 0, error("sgnK: zero element"));
  if (type(G) != "t_POL", return(sign(G)));
  while (polsturm(G, I) > 0,
    my(m = (I[1] + I[2]) / 2); if (subst(fZ, 'b, m) == 0, error("rational root of fZ"));
    I = if (subst(fZ, 'b, I[1]) * subst(fZ, 'b, m) < 0, [I[1], m], [m, I[2]]));
  sign(subst(G, 'b, I[1]));
}
embC(g, i) = subst(lift(Mod(1, fZ) * g), 'b, RT[i]);
for (i = 1, 3, chq(sgnK(eps, i) == 1, Str("eps > 0 at beta_", i)));
\\ refined root intervals (rA2 / Dr2, rB2 / Dr2), Dr2 = 2^40, for the sign certificates of Lean (RealRoots.lean)
Dr2 = 2^40;
rA2 = vector(3, i, floor(RT[i] * Dr2)); rB2 = vector(3, i, rA2[i] + 1);
for (i = 1, 3, chq(subst(fZ, 'b, rA2[i] / Dr2) * subst(fZ, 'b, rB2[i] / Dr2) < 0 && rtA[i] * Dr2 < rA2[i] * Dr && rB2[i] * Dr < rtB[i] * Dr2, Str("refined interval of beta_", i, ": sign change of fL, inside (rtA, rtB) / Dr")));
\\ ---------------------------------------------------------------- 2. h = hp conj(hp) over L42
hc = vector(4, j, polcoef(h0, j - 1));
p0 = hc[4] / 2;
\\ u (h2 - p0^2 + u)^2 - (p0 (h2 - p0^2 + u) - h1)^2 - 4 u h0 = 0
res = 'y * (hc[3] - p0^2 + 'y)^2 - (p0 * (hc[3] - p0^2 + 'y) - hc[2])^2 - 4 * 'y * hc[1];
res = Pol(apply(c -> lift(Mod(1, fZ) * c), Vec(res)), 'y);
RU = nfroots(fZ, res);
printf("resolvent cubic: %d roots in K21\n", #RU);
cand = [];
{
  foreach (RU, u,
    my(sq = nfroots(fZ, 'y^2 - lift(Mod(1, fZ) * u / eps)));
    if (#sq > 0 && u != 0, cand = concat(cand, [[u, sq[1]]])));
}
chq(#cand >= 1, "a root u of the resolvent in K21 with u / eps a nonzero square in K21");
[uu, pp1] = cand[1];
p1 = Mod(pp1, fZ);
r0 = (hc[3] - p0^2 + Mod(uu, fZ)) / 2;
r1 = (2 * p0 * r0 - hc[2]) / (2 * eps * p1);
\\ exact check over K21[w]/(w^2 - eps): w has a lower priority than b, so an element of K21[w] is a polmod in b with
\\ coefficients in Q[w]; redw collects the coefficients of w^j and replaces w^2 by eps: P = g0 + g1 w, [g0, g1] in K21
redw(P) = { my(A = lift(P), g = [0, 0]); for (j = 0, poldegree(A, 'w), g[j % 2 + 1] += Mod(polcoef(A, j, 'w), fZ) * eps^(j \ 2)); g; }
chq(redw(Mod('w^2 * 'b, fZ)) == [Mod('b, fZ) * eps, 0] && redw(Mod(3 + 'w, fZ)) == [3, 1] && redw(Mod('w^3, fZ)) == [0, eps], "tool: redw on b w^2, 3 + w, w^3");
hp = 'x^2 + (p0 + p1 * 'w) * 'x + (r0 + r1 * 'w);
hm = 'x^2 + (p0 - p1 * 'w) * 'x + (r0 - r1 * 'w);
{
  my(D = hp * hm - h0, ok = 1, bad = 1);
  foreach (Vec(D), cf, if (redw(cf) != [0, 0], ok = 0));
  foreach (Vec(D + 'w * 'x), cf, if (redw(cf) != [0, 0], bad = 0));
  chq(ok && !bad, "h 0 = (X^2 + (p0 + p1 w) X + r0 + r1 w) (X^2 + (p0 - p1 w) X + r0 - r1 w) exactly, w^2 = eps (negative control: adding w X breaks it)");
}
{
  chq(p0 == hc[4] / 2 && hc[3] == 2 * r0 + p0^2 - eps * p1^2 && hc[2] == 2 * (p0 * r0 - eps * p1 * r1) && hc[1] == r0^2 - eps * r1^2,
    "the four K21 identities h3 = 2 p0, h2 = 2 r0 + p0^2 - eps p1^2, h1 = 2 (p0 r0 - eps p1 r1), h0 = r0^2 - eps r1^2");
}
\\ common denominator Dh: P0, P1, R0, R1 = Dh (p0, p1, r0, r1)
{
  my(v = concat([zkc(p0), zkc(p1), zkc(r0), zkc(r1)]));
  Dh = denominator(v);
}
P0 = Dh * zkc(p0); P1 = Dh * zkc(p1); R0 = Dh * zkc(r0); R1 = Dh * zkc(r1);
printf("Dh = %d, max |coordinate| of P0, P1, R0, R1: %d\n", Dh, vecmax(apply(abs, concat([P0, P1, R0, R1]))));
Dl0 = p0^2 + eps * p1^2 - 4 * r0;
Dl1 = 2 * p0 * p1 - 4 * r1;
NDl = Dl0^2 - eps * Dl1^2;
\\ Dh^2 Dl1 and Dh^4 N(Delta) as integral zk lists (the Lean identities use exactly these scalings)
LD1 = zkc(Dh^2 * Dl1); LN = zkc(Dh^4 * NDl);
chq(denominator(LD1) == 1 && denominator(LN) == 1, "Dh^2 Delta1 and Dh^4 N(Delta) have integral zk coordinates");
\\ ---------------------------------------------------------------- 3. the two places
SEP = [[-5, 0, 1, 6, 178], [-1, 0, 1/10, 1, 2]];
EXPECT = [["q", "h", "q", "h"], ["h", "q", "h", "q"]];
sgn3(g) = vector(3, i, sgnK(g, i));
LQ = vector(2); LH = vector(2); SQ = vector(2); SH = vector(2);
{
  for (k = 1, 2,
    my(sep = SEP[k], sq, sh, orig, sd1 = sgnK(Dl1, k), sN = sgnK(NDl, k), qR, hR, rq, rh, all, pos);
    printf("==== place %d = realEmb %d (beta_%d = %.12f)\n", 4 + k, k - 1, k, RT[k]);
    chq(sgnK(c0, k) == -1, "lc(fRev 0) = c < 0");
    sq = vector(5, j, sgnK(subst(q0, 'x, sep[j]), k)); sh = vector(5, j, sgnK(subst(h0, 'x, sep[j]), k));
    printf("  separators %s; signs of q 0: %s, of h 0: %s\n", sep, sq, sh);
    chq(sN == -1, "N(Delta) < 0: exactly one of the two quadratic factors of h over R has real roots");
    printf("  sign Delta1 = %d: the factor with real roots is X^2 + (p0 %s t p1) X + (r0 %s t r1), t = sqrt(eps) > 0\n", sd1, if (sd1 > 0, "+", "-"), if (sd1 > 0, "+", "-"));
    orig = vector(4, j, if (sq[j] != sq[j + 1] && sh[j] == sh[j + 1], "q", if (sh[j] != sh[j + 1] && sq[j] == sq[j + 1], "h", "?")));
    chq(orig == EXPECT[k], Str("root layout ", orig, " (expected (q, h, q, h) at 5, (h, q, h, q) at 6)"));
    chq(sq[1] == 1 && sq[5] == 1 && sh[1] == 1 && sh[5] == 1, "q, h > 0 at s0 and s4 (monic, roots inside)");
    \\ numerical cross-check: the real roots of fRev^sigma lie in the brackets
    qR = Pol(apply(c -> embC(c, k), Vec(q0)), 'x); hR = Pol(apply(c -> embC(c, k), Vec(h0)), 'x);
    rq = polrootsreal(qR); rh = polrootsreal(hR);
    all = vecsort(concat(rq, rh));
    chq(#rq == 2 && #rh == 2 && vecmin(vector(4, j, min(all[j] - sep[j], sep[j + 1] - all[j]))) > 0, Str("numerically the 4 real roots ", apply(z -> precision(z, 10), all), " interlace the separators"));
    SQ[k] = sq; SH[k] = sh;
    LQ[k] = vector(5, j, my(n = numerator(sep[j]), d = denominator(sep[j]), g = zkE(qData[1][1]) * d^2 + zkE(qData[1][2]) * n * d + qDen[1] * n^2); chq(g == d^2 * qDen[1] * subst(q0, 'x, sep[j]), "scaled q(s)"); zkc(g));
    LH[k] = vector(5, j, my(n = numerator(sep[j]), d = denominator(sep[j]), g = sum(i = 0, 3, zkE(hData[1][i + 1]) * n^i * d^(4 - i)) + hDen[1] * n^4); chq(g == d^4 * hDen[1] * subst(h0, 'x, sep[j]), "scaled h(s)"); zkc(g));
    printf("  signs at the three embeddings: Delta1 %s, N(Delta) %s\n", sgn3(Dl1), sgn3(NDl));
  );
}
\\ ---------------------------------------------------------------- 4. the Lean data file
lst(v) = Str("[", strjoin(apply(z -> Str(z), Vec(v)), ", "), "]");
{
  my(fn = Str(if (#getenv("LEANOUT"), getenv("LEANOUT"), "../../FurioLombardo/Discharge/SelmerBasis/"), "RealRootData.lean"), s);
  s = Str("import Mathlib\n\n/-!\n# Data for the real roots of `fRev 0` at the real places 5 and 6\n\nWritten by code/selmer-local-conditions/real_roots.gp (complete output real_roots.out); zk lists of\nintegers (lane M1's `zkE`). `rhDen * (p0, p1, r0, r1)` with `h 0 = hp conj(hp)` over `L42`,\n`hp = X^2 + (p0 + p1 w) X + (r0 + r1 w)`; `rhD1` = `rhDen^2 * Delta1`, `rhN` = `rhDen^4 * N(Delta)`;\n`sepN`, `sepD`: the separators `n / d` at places 5, 6 (index 0, 1); `sepQ`, `sepH`: the zk lists of\n`d^2 qDen q 0 (n / d)` and `d^4 hDen h 0 (n / d)`.\n-/\n\nnamespace FurioLombardo.Discharge.SelmerBasis.RealRootData\n\n");
  s = Str(s, "def rhDen : ℕ := ", Dh, "\n\n");
  s = Str(s, "def Dr2 : ℕ := ", Dr2, "\n\n", "def rA2 : List ℤ := ", lst(rA2), "\n\n", "def rB2 : List ℤ := ", lst(rB2), "\n\n");
  s = Str(s, "def rhP0 : List ℤ := ", lst(P0), "\n\n", "def rhP1 : List ℤ := ", lst(P1), "\n\n", "def rhR0 : List ℤ := ", lst(R0), "\n\n", "def rhR1 : List ℤ := ", lst(R1), "\n\n");
  s = Str(s, "def rhD1 : List ℤ := ", lst(LD1), "\n\n", "def rhN : List ℤ := ", lst(LN), "\n\n");
  s = Str(s, "def sepN : List (List ℤ) := [", strjoin(vector(2, k, lst(apply(numerator, SEP[k]))), ", "), "]\n\n");
  s = Str(s, "def sepD : List (List ℤ) := [", strjoin(vector(2, k, lst(apply(denominator, SEP[k]))), ", "), "]\n\n");
  s = Str(s, "def sepQ : List (List (List ℤ)) := [", strjoin(vector(2, k, Str("[", strjoin(vector(5, j, lst(LQ[k][j])), ", "), "]")), ",\n  "), "]\n\n");
  s = Str(s, "def sepH : List (List (List ℤ)) := [", strjoin(vector(2, k, Str("[", strjoin(vector(5, j, lst(LH[k][j])), ", "), "]")), ",\n  "), "]\n\n");
  s = Str(s, "end FurioLombardo.Discharge.SelmerBasis.RealRootData\n");
  system(Str("rm -f ", fn)); write1(fn, s);
  printf("wrote %s\n", fn);
}
printf("signs: q at separators %s, h at separators %s\n", SQ, SH);
\\ every check named here must have run (gp skips the rest of a block after an error and goes on)
{
  foreach (["Lean data parsed", "tool: redw", "exactly, w^2 = eps", "the four K21 identities", "integral zk coordinates", "root layout", "scaled h(s)"], r,
    if (#[m | m <- Vec(RAN), #strsplit(m, r) > 1] == 0, NF++; printf("CHECK NOT RUN: %s\n", r)));
}
printf("DONE, %d failed checks (%d checks ran)\n", NF, #RAN);
