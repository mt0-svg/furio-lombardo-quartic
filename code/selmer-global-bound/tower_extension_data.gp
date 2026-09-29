\\ tower_extension_data.gp: data on L = K21(sqrt eps) and N = L(sqrt e') for the M3b discharge (found here, rechecked by Lean).
\\ e = disc_t(G2), G2 = A - sqrt(d) B (class_group_n84_two.gp), sqrt(d) = j delta, delta^2 = eps; e' = e / c^2 with (e') prime;
\\ x_L with (x_L^2 - e') / 4 integral; m = N_{L/K21}(e') = unit * pi7. bnfinit (GRH) is used only to FIND c.
\\ Run from code/descent: gp -q ../selmer-global-bound/tower_extension_data.gp < /dev/null
default(parisizemax, 6*10^9); default(nbthreads, 1);
LEANDIR = if (type(getenv("LEANOUT")) == "t_STR", getenv("LEANOUT"), "../../");  \\ LEANOUT=<dir>/ writes the Lean file under <dir> instead of lean/
read("descent_search_lib.gp");
read("../earlier-computations/richelot_data.gp");
read("../earlier-computations/field_l42_polynomial.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
dv(u, v) = { my(r = zv(nfeltdiv(nf, u, v))); if (denominator(content(r)) != 1, error("not integral")); r };
dig(v) = vecmax(apply(n -> #digits(abs(numerator(n)) + 1) + #digits(denominator(n)), Vec(v)));
eps = G[1]; foreach([2, 5, 7, 10, 11], i, eps = mulz(eps, G[i]));
epsA = nfbasistoalg(nf, eps);
R1 = RIN[1]; Ap = R1[3]; Bp = R1[4]; dr = Mod(R1[5], K21);
chk(poldegree(Ap, t) <= 2 && poldegree(Bp, t) <= 2, "A, B have degree <= 2 in t");
jj = nfroots(nf, X^2 - lift(dr / epsA)); chk(#jj == 2, "d / eps is a square in K21"); jr = Mod(jj[1], K21);
Ak = vector(3, k, Mod(polcoef(Ap, k - 1, t), K21)); Bk = vector(3, k, Mod(polcoef(Bp, k - 1, t), K21));
\\ G2 = sum_k (A_k - jr delta B_k) t^k, e = g1^2 - 4 g0 g2 = e0 + e1 delta
e0 = Ak[2]^2 + dr * Bk[2]^2 - 4 * Ak[1] * Ak[3] - 4 * dr * Bk[1] * Bk[3];
e1 = jr * (-2 * Ak[2] * Bk[2] + 4 * (Ak[1] * Bk[3] + Ak[3] * Bk[1]));
\\ absolute field
nfL = nfinit([Lpol, [2, 7]]);
chk(nfcertify(nfL) == [], "maximal order of L certified");
emb = nfisincl(K21, Lpol); chk(#emb == 1, "K21 embeds into L"); bL = Mod(emb[1], Lpol);
toL(xk) = subst(lift(xk), b, bL);
sq = nfroots(nfL, X^2 - lift(toL(epsA))); chk(#sq == 2, "eps is a square in L"); dL = Mod(sq[1], Lpol);
rel2abs(a0, a1) = toL(a0) + toL(a1) * dL;
eA = rel2abs(e0, e1);
\\ relative coordinates of an absolute element: x = a0(bL) + a1(bL) dL, solve the 42 x 42 system over Q
Mrel = matconcat([Mat(vector(21, k, Colrev(lift(bL^(k-1)), 42))), Mat(vector(21, k, Colrev(lift(bL^(k-1) * dL), 42)))]);
abs2rel(xA) = { my(s = matsolve(Mrel, Colrev(lift(Mod(xA, Lpol)), 42))); [Mod(Polrev(s[1..21], b), K21), Mod(Polrev(s[22..42], b), K21)] };
tst = abs2rel(eA); chk(tst[1] == e0 && tst[2] == e1, "abs2rel inverts rel2abs on e");
bnfL = bnfinit(nfL, 1);
print("class group of L (GRH): ", bnfL.cyc);
fe = idealfactor(nfL, lift(eA));
print("(e) = ", vector(#fe~, i, [fe[i,1].p, fe[i,1].e, fe[i,1].f, fe[i,2]]));
odd = [i | i <- [1..#fe~], fe[i,2] % 2 == 1];
chk(#odd == 1 && fe[odd[1],1].p == 7, "exactly one prime with odd exponent in (e), above 7");
P7a = fe[odd[1], 1];
Jc = idealfactorback(nfL, fe[,1], fe[,2] \ 2);
cg = bnfisprincipal(bnfL, Jc, 1); chk(cg[1] == 0 || cg[1] == []~ || cg[1] == vector(#cg[1])~, "the square root ideal is principal");
cA = nfbasistoalg(nfL, cg[2]);
epA = eA / cA^2;
chk(idealval(nfL, lift(epA), P7a) == 1 && abs(idealnorm(nfL, lift(epA))) == 7^3, "(e') = P7a exactly");
\\ make e' small: multiply by squares of units (LLL on the unit logs is overkill; try the reduction below)
print("e' size (bytes): ", sizebyte(epA));
ep = abs2rel(epA); print("e' relative coordinates digits: ", dig(zkc(lift(ep[1]))), " ", dig(zkc(lift(ep[2]))));
m = ep[1]^2 - epsA * ep[2]^2;
p7 = G[16]; eps = zv(eps);
um = zv(nfeltdiv(nf, zkc(lift(m)), p7));
chk(unitq(um), "m = N(e') is a unit times pi7");
print("signs of m: ", nfeltsign(nf, zkc(lift(m))), "; of eps: ", nfeltsign(nf, eps));
\\ x_L with x_L^2 = e' mod 4
bid4 = idealstar(nfL, 4, 2);
lg = ideallog(nfL, lift(epA), bid4);
print("cyc of (O_L/4)^x: ", bid4.cyc, " log of e': ", lg~);
hf = vector(#lg, i, my(c = bid4.cyc[i]); if (c % 2 == 1, lift(Mod(lg[i], c) / 2), if (lg[i] % 2, error("e' is not a square mod 4"), lg[i] / 2)));
xL = nfeltreduce(nfL, nffactorback(nfL, bid4.gen, hf~), idealhnf(nfL, 4));
xLA = nfbasistoalg(nfL, xL);
nLA = (xLA^2 - epA) / 4;
chk(denominator(content(nfalgtobasis(nfL, nLA))) == 1, "n_L = (x_L^2 - e') / 4 is integral in L");
xr = abs2rel(xLA); nr = abs2rel(nLA);
print("x_L relative denominators: ", denominator(content(lift(xr[1]))), " ", denominator(content(lift(xr[2]))), " (in zk coordinates: ", denominator(content(zkc(lift(xr[1])))), " ", denominator(content(zkc(lift(xr[2])))), ")");
print("n_L relative zk denominators: ", denominator(content(zkc(lift(nr[1])))), " ", denominator(content(zkc(lift(nr[2])))));
\\ ---- output for Lean (relative coordinates over K21 on the basis 1, delta; zk coordinates)
zi(xk) = { my(v = zkc(lift(xk))); if (denominator(content(v)) != 1, error("not integral")); v };
ea = zi(2 * ep[1]); eb = zi(2 * ep[2]);   \\ e' = (ea + eb delta) / 2
mz = zkc(lift(m));
umi = inv(um);
al = zi(2 * xr[1]); be = zi(2 * xr[2]);
nx = zv(nfeltdiv(nf, mulz(al, al) - mulz(eps, mulz(be, be)), zkc(4)));
chk(denominator(content(nx)) == 1, "N(x_L) = (al^2 - eps be^2) / 4 is integral");
aln = zi(2 * nr[1]); ben = zi(2 * nr[2]);
nn = zv(nfeltdiv(nf, mulz(aln, aln) - mulz(eps, mulz(ben, ben)), zkc(4)));
chk(denominator(content(nn)) == 1, "N(n_L) = (aln^2 - eps ben^2) / 4 is integral");
\\ identities rechecked here: al^2 + eps be^2 - 4 ea = 8 aln, al be - 2 eb = 4 ben
chk(mulz(al, al) + mulz(eps, mulz(be, be)) - 2 * ea == 8 * aln, "x_L^2 - e' = 4 n_L (delta-free part)");
chk(mulz(al, be) - eb == 4 * ben, "x_L^2 - e' = 4 n_L (delta part)");
chk(mulz(ea, ea) - mulz(eps, mulz(eb, eb)) == 4 * mz, "4 m = ea^2 - eps eb^2");
chk(mulz(um, p7) == mz, "m = um pi7");
print("digits: ea ", dig(ea), " eb ", dig(eb), " m ", dig(mz), " um ", dig(um), " um^-1 ", dig(umi), " al ", dig(al), " be ", dig(be), " nx ", dig(nx), " aln ", dig(aln), " ben ", dig(ben), " nn ", dig(nn));
out = Str(LEANDIR, "FurioLombardo/Discharge/M3b/DataL.lean");
system(Str("rm -f ", out));
write(out, "import Mathlib\n\n/-! Data of the M3b discharge on L = K21(δ), δ² = ε (generated by code/selmer-global-bound/tower_extension_data.gp, PARI/GP;\nevery datum is rechecked by the kernel). An element (a + b δ) / 2 of L is given by the zk coordinates of a, b. -/\n\nnamespace FurioLombardo.Discharge.M3b\n");
write(out, "/-- `e' = (ea + eb δ) / 2`: disc(G2) divided by a square, `(e')` the prime of L above 7 ramified in N. -/\ndef eaL : List ℤ := ", lst(ea~), "\n");
write(out, "/-- See `eaL`. -/\ndef ebL : List ℤ := ", lst(eb~), "\n");
write(out, "/-- `m = N_{L/K21}(e') = (ea² - ε eb²) / 4`. -/\ndef mL : List ℤ := ", lst(mz~), "\n");
write(out, "/-- `um = m / pi7`, a unit. -/\ndef umL : List ℤ := ", lst(um~), "\n");
write(out, "/-- `um⁻¹`. -/\ndef umInvL : List ℤ := ", lst(umi~), "\n");
write(out, "/-- `x_L = (al + be δ) / 2` with `x_L² ≡ e' mod 4 O_L`. -/\ndef alL : List ℤ := ", lst(al~), "\n");
write(out, "/-- See `alL`. -/\ndef beL : List ℤ := ", lst(be~), "\n");
write(out, "/-- `N(x_L) = (al² - ε be²) / 4`. -/\ndef nxL : List ℤ := ", lst(nx~), "\n");
write(out, "/-- `n_L = (x_L² - e') / 4 = (aln + ben δ) / 2`. -/\ndef alnL : List ℤ := ", lst(aln~), "\n");
write(out, "/-- See `alnL`. -/\ndef benL : List ℤ := ", lst(ben~), "\n");
write(out, "/-- `N(n_L) = (aln² - ε ben²) / 4`. -/\ndef nnL : List ℤ := ", lst(nn~), "\n");
write(out, "end FurioLombardo.Discharge.M3b");
print("written ", out);
