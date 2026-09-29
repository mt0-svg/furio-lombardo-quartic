\\ kappa_data.gp: the data of Kappa.lean's kappa_rel, the triviality of the classes kappa_t
\\ (t = 1 .. 15) in H(fRev k). kappa_t has the bits of Assembly.kapRows (t - 1) (AssemblyData.lean); its scalar is
\\ c_t = M1.gensL t (M1/DataGens.lean). Wanted, exactly and from the Lean text alone:
\\   c_t prod_{s < 29} gL_s^(a_s) = y1^2 in L42,   c_t prod_{j < 53} gN_j^(a_(29 + j)) = y2^2 in N84
\\ (gL_s, gN_s of SUnitData.lean, a = the bits of kappa_t). Then [prod_s gK k s ^ a_s] = [c_t^(-1) (y1, y2)^2] = 1 in
\\ H(fRev k) for both twists (GlobalGen.mk_eq_prod_of_components with z = 1). Output, per t (index t - 1):
\\   aK: the 82 bits; prodL, prodN: the products (L42 and N84 coordinates as zk lists, N84 in the Lean format of
\\   SUnitTower.lean, Omega = 2 omega_N); y1T = y1D y1, y2T = y2D y2 (zk lists, y1D, y2D the least denominators);
\\   precisions of the four Kronecker checks of KappaCheck.lean, from an exact emulation (w6_kernel_emulation_lib.gp):
\\     checkLC pPL (ofL prodL) (selProdL aK gL),  checkNC pPN (ofN prodN) (selProdN (aK.drop 29) gN),
\\     checkLC pSL (smulLC (y1D^2 c) (ofL prodL)) (mulLC (ofL y1T) (ofL y1T)),
\\     checkNC pSN (smulNC (y2D^2 c) (ofN prodN)) (mulNC (ofN y2T) (ofN y2T)).
\\ Negative controls: a flipped bit of kappa_1 leaves no square root in L42; -c_1 leaves none in L42 or N84.
\\ Run from code/earlier-computations:
\\   gp -q ../selmer-assembly/kappa_data.gp < /dev/null > ../selmer-assembly/kappa_data.out 2>&1
\\ Output: /tmp/sk1/KappaData.lean (installed into Discharge/SelmerBasis/ by hand, then compiled).
default(parisizemax, 3000 * 10^6); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
read("../selmer-global-bound/tower_lib.gp"); read("../selmer-local-conditions/w6_kernel_emulation_lib.gp");
LEAN = "../../FurioLombardo/";
SUD = Str(LEAN, "Discharge/SelmerBasis/SUnitData.lean");
OUTD = "/tmp/sk1/";
T00 = getabstime();
\\ keprec of local_data_v.gp (any passing precision is valid for the kernel check)
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
\\ ---------------------------------------------------------------- global data (Lean text)
nfK = nfinit(K21);
KZN = leandef5(Str(LEAN, "M1/DataField.lean"), "zkNum"); KDZ = leandef5(Str(LEAN, "M1/DataField.lean"), "Dz");
KFL = leandef5(Str(LEAN, "M1/Basic.lean"), "fL");
chk5(vector(21, j, Pol(Vecrev(KZN[j]), 'b) / KDZ) == nfK.zk, "nfK.zk = M1's zkNum / Dz");
chk5(Pol(Vecrev(KFL), 'b) == K21, "M1's fL = K21");
epsL = leandef5(Str(LEAN, "Discharge/M3b/K21Defs.lean"), "epsL");
eaL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "eaL"); ebL = leandef5(Str(LEAN, "Discharge/M3b/DataL.lean"), "ebL");
EPS = KofList(epsL); EN = [KofList(eaL) / 2, KofList(ebL) / 2];
gLs = vector(29, s1, leandef5(SUD, Str("gL_", s1 - 1))); gNs = vector(53, s1, leandef5(SUD, Str("gN_", s1 - 1)));
genL = apply(g -> [KofList(g[1]), KofList(g[2])], gLs);
genN = apply(g -> Nunfmt(vector(4, i, KofList(g[i]))), gNs);
gO = leandef5(Str(LEAN, "M1/DataGens.lean"), "gensL");
kapR = leandef5(Str(LEAN, "Discharge/SelmerBasis/AssemblyData.lean"), "kapRows");
chk5(#gO == 18 && #kapR == 15 && vecmax(apply(r -> #binary(r), kapR)) <= 82, "M1's gensL (18), Assembly.kapRows (15 rows of at most 82 bits)");
\\ ---------------------------------------------------------------- KE mirrors of SUnitTower.lean and MuTCert.lean
\\ A KE expression is represented by its summary [deg, len, bnd, val] (KE.deg, KE.len 21, KE.bnd Dz 21 zkWb, and
\\ KE.valN Dz at the numerators WN = zkNum evaluated at N = 2^k), computed by the rules of kedeg, kelen, kebnd, kevalN of
\\ w6_kernel_emulation_lib.gp; this is what checkK k reads (kecheck), without building the (exponentially repeated) trees of the
\\ nested products. The kernel evaluates the same DAG with sharing.
sLin(a) = [1, 21, sumabs(a) * KWB, sum(i = 1, min(#a, #WN), a[i] * WN[i])];
sInt(m) = [0, 1, abs(m), m];
sMul(x, y) = [x[1] + y[1], x[2] + y[2] - 1, x[2] * x[3] * y[3], x[4] * y[4]];
sAdd(x, y) = { my(d = max(x[1], y[1]), f1 = KDZ^(d - x[1]), f2 = KDZ^(d - y[1])); [d, max(x[2], y[2]), f1 * x[3] + f2 * y[3], f1 * x[4] + f2 * y[4]]; }
sSub(x, y) = { my(d = max(x[1], y[1]), f1 = KDZ^(d - x[1]), f2 = KDZ^(d - y[1])); [d, max(x[2], y[2]), f1 * x[3] + f2 * y[3], f1 * x[4] - f2 * y[4]]; }
\\ LC = [s0, s1], NC = [LC, LC]
ofLs(l) = [sLin(l[1]), sLin(l[2])];
ofNs(l) = [[sLin(l[1]), sLin(l[2])], [sLin(l[3]), sLin(l[4])]];
oneLCs() = [sInt(1), sInt(0)];
oneNCs() = [oneLCs(), [sInt(0), sInt(0)]];
addLCs(x, y) = [sAdd(x[1], y[1]), sAdd(x[2], y[2])];
smulLCs(c, x) = [sMul(c, x[1]), sMul(c, x[2])];
smulNCs(c, x) = [smulLCs(c, x[1]), smulLCs(c, x[2])];
mulLCs(x, y) = [sAdd(sMul(x[1], y[1]), sMul(sLin(epsL), sMul(x[2], y[2]))), sAdd(sMul(x[1], y[2]), sMul(x[2], y[1]))];
e4LCs() = [sMul(sInt(2), sLin(eaL)), sMul(sInt(2), sLin(ebL))];
mulNCs(x, y) = [addLCs(mulLCs(x[1], y[1]), mulLCs(e4LCs(), mulLCs(x[2], y[2]))), addLCs(mulLCs(x[1], y[2]), mulLCs(x[2], y[1]))];
selProdLs(a, g) = { my(r = oneLCs()); forstep (i = min(#a, #g), 1, -1, if (a[i] != 0, r = mulLCs(ofLs(g[i]), r))); r; }
selProdNs(a, g) = { my(r = oneNCs()); forstep (i = min(#a, #g), 1, -1, if (a[i] != 0, r = mulNCs(ofNs(g[i]), r))); r; }
\\ checkK k on a summary (kecheck of w6_kernel_emulation_lib.gp)
checkS(k, s) = {
  my(N = 2^k, v = s[4], gN = evalLN(N, KFL), q, Q);
  if (v % gN != 0, return(0));
  q = v / gN; Q = kedigits(k, s[2], q);
  evalLN(N, Q) == q && 2 * (s[3] + #KFL * maxabs(KFL) * maxabs(Q)) < 2^k;
}
setN(k) = WN = apply(l -> evalLN(2^k, l), KZN);
\\ f: a closure returning the list of component summaries (after setN); the least k found as keprec does, common
\\ to all components, then checked
okAll(k, f) = { setN(k); my(L = f()); vecmin(apply(s -> checkS(k, s), L)); }
precAll(f) = {
  my(L, b, k, k1, k2, Q, q, v, gN);
  setN(64); L = f(); b = vecmax(apply(s -> s[3], L)); k = max(8, #binary(2 * b));
  for (i = 0, 8, if (okAll(k + i, f), return(k + i)));
  k2 = 2 * k + 64;
  for (r = 1, 6,
    setN(k2); L = f(); my(mq = 0, good = 1);
    foreach (L, s, gN = evalLN(2^k2, KFL); v = s[4]; if (v % gN != 0, error("precAll: not divisible")); q = v / gN; Q = kedigits(k2, s[2], q);
      if (evalLN(2^k2, Q) != q || 4 * maxabs(Q) >= 2^k2, good = 0); mq = max(mq, maxabs(Q)));
    if (good, k1 = #binary(2 * (b + #KFL * maxabs(KFL) * mq)); for (i = 0, 40, if (okAll(k1 + i, f), return(k1 + i))));
    k2 *= 2);
  error("precAll: no precision found");
}
\\ the components of checkLC k x y (x.1 - y.1, x.2 - y.2) and of checkNC
subLC(x, y) = [sSub(x[1], y[1]), sSub(x[2], y[2])];
subNC(x, y) = concat(subLC(x[1], y[1]), subLC(x[2], y[2]));
\\ ---------------------------------------------------------------- square roots
prodL(aL) = { my(pr = [Kc(1), Kc(0)]); for (s1 = 1, 29, if (aL[s1], pr = Lmul(pr, genL[s1]))); pr; }
prodN(aN) = { my(pr = NofK(1)); for (s1 = 1, 53, if (aN[s1], pr = Nmul(pr, genN[s1]))); pr; }
REC = vector(15);
{
  my(t0 = getabstime());
  for (tt = 1, 15,
    my(c = KofList(gO[tt + 1]), bits = vector(82, s1, bittest(kapR[tt], s1 - 1)), aL = bits[1 .. 29], aN = bits[30 .. 82], pL, pN, y1, y2, t1 = getabstime());
    pL = prodL(aL); pN = prodN(aN);
    y1 = Lsqrt(Lsc(c, pL)); y2 = Nsqrt(Nsc(c, pN));
    if (y1 == 0 || y2 == 0, error(Str("kappa_", tt, ": no square root (L ", y1 != 0, ", N ", y2 != 0, ")")));
    chk5(Lmul(y1, y1) == Lsc(c, pL) && Nmul(y2, y2) == Nsc(c, pN) && !Lis0(y1) && !Nis0(y2),
      Str("kappa_", tt, ": c prod gL^a = y1^2 in L42, c prod gN^b = y2^2 in N84 (", vecsum(aL), " + ", vecsum(aN), " generators, ", getabstime() - t1, " ms)"));
    my(y1D = den5(y1), y2D = den5(Nfmt(y2)), y1T = [Klist(y1D * y1[1]), Klist(y1D * y1[2])], y2T = vector(4, i, Klist(y2D * Nfmt(y2)[i])),
       prL = [Klist(pL[1]), Klist(pL[2])], prN = vector(4, i, Klist(Nfmt(pN)[i])));
    REC[tt] = [bits, prL, prN, y1T, y1D, y2T, y2D, c]);
  printf("  square roots: %d ms\n", getabstime() - t0);
}
\\ negative controls
{
  my(c = KofList(gO[2]), bits = vector(82, s1, bittest(kapR[1], s1 - 1)), aL = bits[1 .. 29], aN = bits[30 .. 82]);
  my(aLb = aL); aLb[1] = 1 - aLb[1];
  chk5(Lsqrt(Lsc(c, prodL(aLb))) == 0, "negative control: kappa_1 with bit 0 flipped leaves no square root in L42");
  chk5(Lsqrt(Lsc(-c, prodL(aL))) == 0 || Nsqrt(Nsc(-c, prodN(aN))) == 0, "negative control: -c_1 leaves no square root in L42 or in N84");
}
\\ ---------------------------------------------------------------- the Kronecker checks, emulated
PREC = vector(15);
{
  my(t0 = getabstime());
  for (tt = 1, 15,
    my(R = REC[tt], bits = R[1], c = gO[tt + 1], fPL, fPN, fSL, fSN, pPL, pPN, pSL, pSN, t1 = getabstime());
    fPL = (() -> subLC(ofLs(R[2]), selProdLs(bits, gLs)));
    fPN = (() -> subNC(ofNs(R[3]), selProdNs(bits[30 .. 82], gNs)));
    fSL = (() -> subLC(smulLCs(sMul(sInt(R[5]^2), sLin(c)), ofLs(R[2])), mulLCs(ofLs(R[4]), ofLs(R[4]))));
    fSN = (() -> subNC(smulNCs(sMul(sInt(R[7]^2), sLin(c)), ofNs(R[3])), mulNCs(ofNs(R[6]), ofNs(R[6]))));
    pPL = precAll(fPL); pPN = precAll(fPN); pSL = precAll(fSL); pSN = precAll(fSN);
    chk5(okAll(pPL, fPL) && okAll(pPN, fPN) && okAll(pSL, fSL) && okAll(pSN, fSN),
      Str("kappa_", tt, ": the four checks pass at precisions ", [pPL, pPN, pSL, pSN], " (", getabstime() - t1, " ms)"));
    PREC[tt] = [pPL, pPN, pSL, pSN]);
  printf("  Kronecker emulation: %d ms\n", getabstime() - t0);
  my(R = REC[1], bb = R[1]); bb[1] = 1 - bb[1];
  chk5(!okAll(PREC[1][1], (() -> subLC(ofLs(R[2]), selProdLs(bb, gLs)))), "negative control: the product check of kappa_1 fails with bit 0 flipped");
  chk5(!okAll(PREC[1][3], (() -> subLC(smulLCs(sMul(sInt(R[5]^2), sLin(-gO[2])), ofLs(R[2])), mulLCs(ofLs(R[4]), ofLs(R[4]))))), "negative control: the square check of kappa_1 fails with -c_1");
}
\\ ---------------------------------------------------------------- Lean output
lst(v) = Str(v);
{
  system(Str("mkdir -p ", OUTD));
  my(f = Str(OUTD, "KappaData.lean"));
  system(Str("rm -f ", f));
  write(f, "import Mathlib\n\n/-!\n# The square roots of the classes `κ_t` (generated)\n\nWritten by code/selmer-assembly/kappa_data.gp (output kappa_data.out). For `t < 15` (the class `κ_(t+1)` of\n`Assembly.kapRows t`, scalar `M1.gensL (t + 1)`):\n\n* `aK t`: the 82 bits; `prodL t`, `prodN t`: the products of the selected `gL`, `gN` (zk lists);\n* `y1T t`, `y1D t`, `y2T t`, `y2D t`: the square roots `y1 = y1T / y1D` in `L42`, `y2 = y2T / y2D` in `N84`;\n* `pPL t`, `pPN t`, `pSL t`, `pSN t`: the precisions of the four Kronecker checks of KappaCheck.lean.\n-/\n\nnamespace FurioLombardo.Discharge.SelmerBasis.KappaData\n");
  write(f, "/-- The bits of `κ_(t+1)`. -/\ndef aK : List (List ℕ) := ", lst(vector(15, tt, apply(b -> if (b, 1, 0), REC[tt][1]))), "\n");
  write(f, "/-- The products in `L42`. -/\ndef prodL : List (List (List ℤ)) := ", lst(vector(15, tt, REC[tt][2])), "\n");
  write(f, "/-- The products in `N84`. -/\ndef prodN : List (List (List ℤ)) := ", lst(vector(15, tt, REC[tt][3])), "\n");
  write(f, "/-- The numerators of the square roots in `L42`. -/\ndef y1T : List (List (List ℤ)) := ", lst(vector(15, tt, REC[tt][4])), "\n");
  write(f, "/-- Their denominators. -/\ndef y1D : List ℕ := ", lst(vector(15, tt, REC[tt][5])), "\n");
  write(f, "/-- The numerators of the square roots in `N84`. -/\ndef y2T : List (List (List ℤ)) := ", lst(vector(15, tt, REC[tt][6])), "\n");
  write(f, "/-- Their denominators. -/\ndef y2D : List ℕ := ", lst(vector(15, tt, REC[tt][7])), "\n");
  write(f, "/-- Precisions. -/\ndef pPL : List ℕ := ", lst(vector(15, tt, PREC[tt][1])), "\n");
  write(f, "def pPN : List ℕ := ", lst(vector(15, tt, PREC[tt][2])), "\n");
  write(f, "def pSL : List ℕ := ", lst(vector(15, tt, PREC[tt][3])), "\n");
  write(f, "def pSN : List ℕ := ", lst(vector(15, tt, PREC[tt][4])), "\n");
  write(f, "end FurioLombardo.Discharge.SelmerBasis.KappaData");
  printf("  wrote %s\n", f);
  printf("  sizes: y1T up to %d bits, y2T up to %d bits, prodL up to %d bits, prodN up to %d bits; precisions %s\n",
    vecmax(vector(15, tt, bits5(REC[tt][4]))), vecmax(vector(15, tt, bits5(REC[tt][6]))), vecmax(vector(15, tt, bits5(REC[tt][2]))), vecmax(vector(15, tt, bits5(REC[tt][3]))), PREC);
}
printf("DONE kappa_data: %d checks passed, %d failed (%d ms)\n", SB5_NOK, SB5_NFAIL, getabstime() - T00);
quit(0);
