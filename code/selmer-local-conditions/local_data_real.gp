\\ local_data_real.gp: the sign data of the generators at the real places 5 and 6 of twist 0 (for
\\ `RealRoots.signOK`), through the tower K21 < L42 = K21(w), w^2 = eps < N84 = L42(z), z^2 = eN.
\\ Data read from the Lean sources: fL (M1/Basic.lean), Dz, zkNum (M1/DataField.lean), epsL (M3b/K21Defs.lean),
\\ eaL, ebL (M3b/DataL.lean), gL_i, gN_j, alphaL, betaN (SelmerBasis/SUnitData.lean), Dr2, rA2, rB2
\\ (SelmerBasis/RealRootData.lean), SgRows (SelmerBasis/AssemblyData.lean), qIdx, hIdx (SelmerBasis/RealInst.lean).
\\ At sigma = realEmb k (theta -> beta_(k+1)), k = 0, 1:
\\   u = sAl sqrt(sigma eps) with u sigma(alphaR.im) < 0; u' = sEb sqrt(sigma eps) with u' sigma(eb) > 0, so that
\\   tau'(eN) > 0 for tau' = extendHom sigma u'; v = sV sqrt(tau'(eN)) with v tau'(betaR.im) < 0.
\\   gensL i = a0 + a1 w: sign at embQ b (w -> +-u) from sigma(a0^2 - eps a1^2) and sigma(a0) or u sigma(a1).
\\   gensN j = A + B' z, A = a0 + a1 w, B' = 2 (b0 + b1 w): M = A^2 - eN B'^2 = m0 + m1 w; sign at embH b (z -> +-v)
\\   from tau'(M) (by sigma(m0^2 - eps m1^2), sigma(m0) or u' sigma(m1)) and tau'(A) or v tau'(b0 + b1 w).
\\ Every sign is certified by an emulation of Lean's `elemCertAt` (RealRoots.lean: Moebius transform of
\\ combo a zkNum on the refined interval (rA2, rB2) / Dr2, all coefficients of s * mobL >= 0, one > 0), and the
\\ resulting sign bits are compared with SgRows (computed numerically by code/selmer-assembly/assembly_data.gp).
\\ Writes the Lean data file /tmp/sr1/RealSignData.lean.
\\ Run from code/selmer-local-conditions: gp -q local_data_real.gp < /dev/null
[x, w, z, y, b];
default(parisizemax, 1500 * 10^6);
default(realprecision, 120);
default(nbthreads, 1);
NF = 0; NOK = 0;
chq(c, msg) = if (c, NOK++; printf("ok: %s\n", msg), NF++; printf("CHECK FAILED: %s\n", msg));
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
epsL = getdef(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL");
eaL = getdef(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL");
ebL = getdef(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL");
SU = Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean");
gLd = vector(29, i, getdef(SU, Str("gL_", i - 1)));
gNd = vector(53, j, getdef(SU, Str("gN_", j - 1)));
alphaL = getdef(SU, "alphaL"); alphaDen = getdef(SU, "alphaDen");
betaN = getdef(SU, "betaN"); betaDen = getdef(SU, "betaDen");
RD = Str(LEAN, "Discharge/SelmerBasis/RealRootData.lean");
Dr2 = getdef(RD, "Dr2"); rA2 = getdef(RD, "rA2"); rB2 = getdef(RD, "rB2");
SgRows = getdef(Str(LEAN, "Discharge/SelmerBasis/AssemblyData.lean"), "SgRows");
qIdx = getdef(Str(LEAN, "Discharge/SelmerBasis/RealInst.lean"), "qIdx");
hIdx = getdef(Str(LEAN, "Discharge/SelmerBasis/RealInst.lean"), "hIdx");
{
chq(#fL == 22 && #zkNum == 21 && #epsL == 21 && #eaL == 21 && #ebL == 21 && #alphaL == 2 && #betaN == 4
  && #SgRows == 2 && #SgRows[1] == 82 && #SgRows[2] == 82 && qIdx == [[0, 2], [1, 3]] && hIdx == [[1, 3], [0, 2]],
  "Lean data parsed (fL, zkNum, epsL, eaL, ebL, 29 gL, 53 gN, alphaL, betaN, Dr2, rA2, rB2, SgRows, qIdx, hIdx)");
}
{
chq(vecmin(vector(29, i, #gLd[i] == 2 && #gLd[i][1] == 21 && #gLd[i][2] == 21)) == 1
  && vecmin(vector(53, j, #gNd[j] == 4 && vecmin(vector(4, c, #gNd[j][c] == 21)) == 1)) == 1, "gL: 2 zk lists, gN: 4 zk lists, each of length 21");
}
fZ = Pol(Vecrev(fL), 'b);
W = vector(21, j, Pol(Vecrev(zkNum[j]), 'b) / Dz);
zkE(a) = Mod(sum(j = 1, min(#a, 21), a[j] * W[j]), fZ);
Mz = matrix(21, 21, i, j, polcoef(W[j], i - 1, 'b));
Mzi = Mz^-1;
zkc(g) = my(G = lift(Mod(1, fZ) * g)); (Mzi * vectorv(21, i, polcoef(G, i - 1, 'b)))~;
chq(zkc(zkE(epsL)) == epsL, "zkc inverts zkE");
\\ integral zk list of g (error if not integral)
zkI(g) = my(v = zkc(g)); if (denominator(v) != 1, error("zkI: not integral")); v;
eps = zkE(epsL); ea = zkE(eaL); eb = zkE(ebL);
RT = polrootsreal(fZ);
chq(#RT == 3 && vecmin(vector(3, i, rA2[i] / Dr2 < RT[i] && RT[i] < rB2[i] / Dr2)) == 1, "beta_(k+1) in (rA2, rB2) / Dr2 (realEmb k)");
\\ ---------------------------------------------------------------- emulation of elemCertAt
\\ combo a zkNum (M1/Kron.lean): the shorter list decides the number of terms, addL keeps the longer tail
combo(a) = {
  my(n = min(#a, #zkNum), L = 0, c);
  for (j = 1, n, L = max(L, #zkNum[j]));
  c = vector(L);
  for (j = 1, n, for (i = 1, #zkNum[j], c[i] += a[j] * zkNum[j][i]));
  c;
}
\\ signCert s [lo, hi] [D, D] l = posCoeffL (s * mobL): mobL u v l = sum_k l_k u^k v^(L-1-k)
elemCert(a, s, k) = {
  my(c = combo(a), L = #c, lo = rA2[k + 1], hi = rB2[k + 1], u = lo + hi * 'y, v = Dr2 + Dr2 * 'y, p, V);
  p = s * sum(i = 1, L, c[i] * u^(i - 1) * v^(L - i));
  if (p == 0, return(0));
  V = Vec(p);
  vecmin(V) >= 0 && vecmax(V) > 0;
}
\\ numerical value at realEmb k
val(g, k) = subst(lift(Mod(1, fZ) * g), 'b, RT[k + 1]);
sgnv(r) = if (abs(r) < 10^-60, error("sgnv: value too close to 0: ", r), sign(r));
\\ negative controls of the emulation
chq(elemCert(epsL, 1, 0) && !elemCert(epsL, -1, 0) && elemCert(epsL, 1, 1), "elemCert: eps > 0 at realEmb 0, 1, and the wrong sign fails");
\\ ---------------------------------------------------------------- norms and M (exact, k-independent)
nL = vector(29, i, my(a0 = zkE(gLd[i][1]), a1 = zkE(gLd[i][2])); zkI(a0^2 - eps * a1^2));
eNw = (ea + eb * 'w) / 2;
redw(P) = my(Q = lift(Mod(1, 'w^2 - eps) * P)); [polcoef(Q, 0, 'w), polcoef(Q, 1, 'w)];
mN0 = vector(53); mN1 = vector(53); nMN = vector(53); nAN = vector(53); nBN = vector(53);
{
  my(okM = 1);
  for (j = 1, 53,
    my(g = gNd[j], a0 = zkE(g[1]), a1 = zkE(g[2]), b0 = zkE(g[3]), b1 = zkE(g[4]), A, Bp, Mw, m0, m1);
    A = a0 + a1 * 'w; Bp = 2 * (b0 + b1 * 'w);
    Mw = redw(A^2 - eNw * Bp^2);
    m0 = a0^2 + eps * a1^2 - 2 * ea * (b0^2 + eps * b1^2) - 4 * eps * eb * b0 * b1;
    m1 = 2 * a0 * a1 - 4 * ea * b0 * b1 - 2 * eb * (b0^2 + eps * b1^2);
    if (Mw[1] != m0 || Mw[2] != m1, okM = 0);
    mN0[j] = zkI(m0); mN1[j] = zkI(m1);
    nMN[j] = zkI(m0^2 - eps * m1^2); nAN[j] = zkI(a0^2 - eps * a1^2); nBN[j] = zkI(b0^2 - eps * b1^2));
  chq(okM, "M = A^2 - eN B'^2 over L42 (PARI arithmetic in K21[w]/(w^2 - eps)) equals the closed form m0 + m1 w, for the 53 gensN");
}
nBeta = zkI(zkE(betaN[3])^2 - eps * zkE(betaN[4])^2);
chq(1, Str("norms integral: max |coordinate| of nL ", vecmax(apply(v -> vecmax(abs(v)), nL)), ", of nM ", vecmax(apply(v -> vecmax(abs(v)), nMN))));
\\ ---------------------------------------------------------------- signs and certificates, k = 0, 1
bitSg(k, s, j) = bittest(SgRows[k + 1][s + 1], j);
sAl = vector(2); sEb = vector(2); sV = vector(2); posBeta = vector(2);
posL = vector(2, k, vector(29)); posM = vector(2, k, vector(53)); posMT = vector(2, k, vector(53)); posAB = vector(2, k, vector(53));
NCERT = 0;
cert(a, s, k, msg) = NCERT++; if (!elemCert(a, s, k), NF++; printf("CERT FAILED: %s (k = %d, s = %d)\n", msg, k, s); 0, 1);
{
  for (k = 0, 1,
    my(sE = sqrt(val(eps, k)), u, up, v, teN, okL = 1, okN = 1, okBits = 1, okSym = 1, nc0 = NCERT);
    sAl[k + 1] = -sgnv(val(zkE(alphaL[2]), k)); u = sAl[k + 1] * sE;
    cert(alphaL[2], -sAl[k + 1], k, "alphaR.im");
    sEb[k + 1] = sgnv(val(eb, k)); up = sEb[k + 1] * sE;
    cert(ebL, sEb[k + 1], k, "eb");
    teN = (val(ea, k) + val(eb, k) * up) / 2;
    chq(teN > 0 && val(ea, k)^2 - val(eps, k) * val(eb, k)^2 < 0, Str("realEmb ", k, ": N(eN) < 0 and tau'(eN) > 0"));
    my(b2 = zkE(betaN[3]), b3 = zkE(betaN[4]), tb = val(b2, k) + val(b3, k) * up);
    sV[k + 1] = -sgnv(tb); v = sV[k + 1] * sqrt(teN);
    posBeta[k + 1] = val(zkE(nBeta), k) > 0;
    cert(nBeta, if (posBeta[k + 1], 1, -1), k, "N(betaR.im)");
    if (posBeta[k + 1], cert(betaN[3], -sV[k + 1], k, "b2"), cert(betaN[4], -sV[k + 1] * sEb[k + 1], k, "b3"));
    \\ gensL
    for (i = 1, 29,
      my(a0 = zkE(gLd[i][1]), a1 = zkE(gLd[i][2]), e0 = val(a0, k) + u * val(a1, k), e1 = val(a0, k) - u * val(a1, k), t);
      if (bitSg(k, i - 1, qIdx[k + 1][1]) != (e0 < 0) || bitSg(k, i - 1, qIdx[k + 1][2]) != (e1 < 0), okBits = 0);
      if (bitSg(k, i - 1, hIdx[k + 1][1]) || bitSg(k, i - 1, hIdx[k + 1][2]), okBits = 0);
      t = sgnv(e0);
      posL[k + 1][i] = val(zkE(nL[i]), k) > 0;
      if ((sgnv(e0) == sgnv(e1)) != posL[k + 1][i], okSym = 0);
      if (posL[k + 1][i],
        okL = okL && cert(nL[i], 1, k, Str("nL ", i - 1)) && cert(gLd[i][1], t, k, Str("gL a0 ", i - 1)),
        okL = okL && cert(nL[i], -1, k, Str("nL ", i - 1)) && cert(gLd[i][2], t * sAl[k + 1], k, Str("gL a1 ", i - 1))));
    \\ gensN
    for (j = 1, 53,
      my(g = gNd[j], a0 = zkE(g[1]), a1 = zkE(g[2]), b0 = zkE(g[3]), b1 = zkE(g[4]),
         tA = val(a0, k) + up * val(a1, k), tB = val(b0, k) + up * val(b1, k),
         tM = val(zkE(mN0[j]), k) + up * val(zkE(mN1[j]), k), e0 = tA + v * 2 * tB, e1 = tA - v * 2 * tB, t, sM);
      if (abs(tM - (tA^2 - teN * 4 * tB^2)) > 10^-40 * (1 + abs(tM)), okN = 0; printf("tM mismatch at j = %d\n", j - 1));
      if (bitSg(k, 29 + j - 1, hIdx[k + 1][1]) != (e0 < 0) || bitSg(k, 29 + j - 1, hIdx[k + 1][2]) != (e1 < 0), okBits = 0);
      if (bitSg(k, 29 + j - 1, qIdx[k + 1][1]) || bitSg(k, 29 + j - 1, qIdx[k + 1][2]), okBits = 0);
      t = sgnv(e0); sM = sgnv(tM);
      posM[k + 1][j] = val(zkE(nMN[j]), k) > 0;
      posMT[k + 1][j] = sM > 0;
      if ((sgnv(e0) == sgnv(e1)) != posMT[k + 1][j], okSym = 0);
      okN = okN && cert(nMN[j], if (posM[k + 1][j], 1, -1), k, Str("nM ", j - 1));
      okN = okN && if (posM[k + 1][j], cert(mN0[j], sM, k, Str("m0 ", j - 1)), cert(mN1[j], sM * sEb[k + 1], k, Str("m1 ", j - 1)));
      if (posMT[k + 1][j],
        posAB[k + 1][j] = val(zkE(nAN[j]), k) > 0;
        okN = okN && cert(nAN[j], if (posAB[k + 1][j], 1, -1), k, Str("nA ", j - 1));
        okN = okN && if (posAB[k + 1][j], cert(g[1], t, k, Str("a0 ", j - 1)), cert(g[2], t * sEb[k + 1], k, Str("a1 ", j - 1))),
        posAB[k + 1][j] = val(zkE(nBN[j]), k) > 0;
        okN = okN && cert(nBN[j], if (posAB[k + 1][j], 1, -1), k, Str("nB ", j - 1));
        okN = okN && if (posAB[k + 1][j], cert(g[3], t * sV[k + 1], k, Str("b0 ", j - 1)), cert(g[4], t * sV[k + 1] * sEb[k + 1], k, Str("b1 ", j - 1)))));
    chq(okBits, Str("realEmb ", k, ": the tower signs of the 82 generators at the four roots equal the bits of SgRows"));
    chq(okSym, Str("realEmb ", k, ": the two roots of a factor have equal signs iff the relevant norm is positive"));
    chq(okL && okN, Str("realEmb ", k, ": all ", NCERT - nc0, " sign certificates pass (Lean elemCertAt emulation)")));
}
\\ negative control: flipping one bit of the table is detected
{
  my(k = 0, i = 1, a0 = zkE(gLd[i][1]), a1 = zkE(gLd[i][2]), e0 = val(a0, k) + sAl[1] * sqrt(val(eps, k)) * val(a1, k));
  chq(!elemCert(if (posL[1][i], gLd[i][1], gLd[i][2]), -sgnv(e0) * if (posL[1][i], 1, sAl[1]), k), "negative control: the certificate with the flipped sign fails");
}
printf("sAl = %s, sEb = %s, sV = %s\n", sAl, sEb, sV);
\\ ---------------------------------------------------------------- Lean output
lst(v) = Str("[", strjoin(apply(z -> Str(z), Vec(v)), ", "), "]");
lstB(v) = Str("[", strjoin(apply(z -> if (z, "true", "false"), Vec(v)), ", "), "]");
\\ one declaration per entry (a single large literal times out in elaboration), then the list of the names
defL(nm, V) = Str(strjoin(vector(#V, i, Str("def ", nm, "_", i - 1, " : List ℤ := ", lst(V[i]))), "\n\n"), "\n\ndef ", nm, " : List (List ℤ) :=\n  [", strjoin(vector(#V, i, Str(nm, "_", i - 1)), ", "), "]\n\n");
{
  my(fn = "/tmp/sr1/RealSignData.lean", s);
  system("mkdir -p /tmp/sr1");
  s = "import Mathlib\n\n/-!\n# Sign data at the real places 5 and 6 (generated by code/selmer-local-conditions/local_data_real.gp, output local_data_real.out)\n\n";
  s = Str(s, "zk lists of the norms `nL i = N(gensL i)` over `K21`; for `gensN j = A + B' z`: `M = A^2 - eN B'^2 = m0 + m1 w`\n");
  s = Str(s, "(`mN0`, `mN1`), `nMN = N(M)`, `nAN = N(A)`, `nBN = N(b0 + b1 w)`; `nBeta = N(betaR.im * betaDen)`. For `k = 0, 1`:\n");
  s = Str(s, "the signs `sAl`, `sEb`, `sV` of `u`, `u'`, `v` and the branch flags of the sign certificates. Every datum is\n");
  s = Str(s, "rechecked in Lean (RealSignCheck.lean).\n-/\n\nnamespace FurioLombardo.Discharge.SelmerBasis.RealSignData\n\n");
  s = Str(s, defL("nL", nL));
  s = Str(s, defL("mN0", mN0));
  s = Str(s, defL("mN1", mN1));
  s = Str(s, defL("nMN", nMN));
  s = Str(s, defL("nAN", nAN));
  s = Str(s, defL("nBN", nBN));
  s = Str(s, "def nBeta : List ℤ := ", lst(nBeta), "\n\n");
  s = Str(s, "def sAl : List ℤ := ", lst(sAl), "\n\n", "def sEb : List ℤ := ", lst(sEb), "\n\n", "def sV : List ℤ := ", lst(sV), "\n\n");
  s = Str(s, "def posBeta : List Bool := ", lstB(posBeta), "\n\n");
  s = Str(s, "def posL : List (List Bool) := [", strjoin(vector(2, k, lstB(posL[k])), ",\n  "), "]\n\n");
  s = Str(s, "def posM : List (List Bool) := [", strjoin(vector(2, k, lstB(posM[k])), ",\n  "), "]\n\n");
  s = Str(s, "def posMT : List (List Bool) := [", strjoin(vector(2, k, lstB(posMT[k])), ",\n  "), "]\n\n");
  s = Str(s, "def posAB : List (List Bool) := [", strjoin(vector(2, k, lstB(posAB[k])), ",\n  "), "]\n\n");
  s = Str(s, "end FurioLombardo.Discharge.SelmerBasis.RealSignData\n");
  system(Str("rm -f ", fn)); write1(fn, s);
  printf("wrote %s\n", fn);
}
printf("certificates emulated: %d\n", NCERT);
if (NF == 0, printf("DONE, 0 failed checks (%d ok)\n", NOK), printf("DONE, %d FAILED checks\n", NF));
quit;
