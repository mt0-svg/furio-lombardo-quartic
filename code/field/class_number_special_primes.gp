\\ class_number_special_primes.gp: data and kernel checks for the special primes 2, 7, 45613 of M2, written as
\\ FurioLombardo/M2/SpecialData.lean of the Lean package (checked by FurioLombardo.M2.mulCheck, comboEq, facCheckE,
\\ homogL). Every check the kernel runs is replayed here first. Run from code/field:
\\ gp -q class_number_special_primes.gp
default(parisizemax, 4*10^9); default(nbthreads, 1);
LEANDIR = if (type(getenv("LEANOUT")) == "t_STR", getenv("LEANOUT"), "../../");  \\ LEANOUT=<dir>/ writes the Lean file under <dir> instead of the Lean package
read("class_number_prime_certs.gp"); g4init();
outfile = Str(LEANDIR, "FurioLombardo/M2/SpecialData.lean");
W2 = 2^512; Fk2 = subst(f, x, W2);
lstr(v) = { my(s = "["); for (i = 1, #v, s = concat(s, Str(v[i])); if (i < #v, s = concat(s, ", "))); concat(s, "]"); }
elt2pol(a) = sum(j = 1, n, a[j] * Wp[j]);
\\ replay of mulCheck a b z: bounds, A B - D Z = f Q with |Q_i| <= 2^480
mulrep(a, b, z) = {
  if (#a != n || #b != n || #z != n, error("length"));
  if (maxabs(a) > 2^100 || maxabs(b) > 2^100 || maxabs(z) > 2^200, error("coordinate bound ", [maxabs(a), maxabs(b), maxabs(z)]));
  my(H = elt2pol(a) * elt2pol(b) - D * elt2pol(z), Q = H \ f);
  if (H - Q * f != 0, error("mul identity"));
  if (polbound(Q) > 2^480, error("quotient bound"));
  if (poldegree(Q) > 19, error("quotient degree"));
}
\\ replay of comboEq a l: sum a_j W_j = D * l
comborep(a, l) = if (elt2pol(a) != D * Pol(Vecrev(l)), error("comboEq ", l));
names = List(); checks = List();
defl(name, v) = listput(names, Strprintf("def %s : List ℤ := %s", name, lstr(v)));
mulchk(tname, na, a, nb, b, nz, z) = { mulrep(a, b, z); listput(checks, Strprintf("theorem %s : mulCheck %s %s %s = true := by decide +kernel", tname, na, nb, nz)); }
combochk(tname, na, a, l) = { comborep(a, l); listput(checks, Strprintf("theorem %s : comboEq %s %s = true := by decide +kernel", tname, na, lstr(l))); }
one = nfalgtobasis(nf, 1); th = nfalgtobasis(nf, Mod(x, f)); thm1 = nfalgtobasis(nf, Mod(x - 1, f));
pw(a, k) = nfeltpow(nf, a, k);
ml(a, b) = nfeltmul(nf, a, b);
dv(a, b) = nfeltdiv(nf, a, b);
isint(a) = denominator(content(a)) == 1;
defl("oneL", one); defl("thL", th); defl("thm1L", thm1);
combochk("one_eq", "oneL", one, [1]); combochk("th_eq", "thL", th, [0, 1]); combochk("thm1_eq", "thm1L", thm1, [-1, 1]);
\\ ---- p = 2: (2) = P1^3 P2^12 P3^6, (theta) = P2^2, (theta - 1) = P1^4 P3^3
dec2 = idealprimedec(nf, 2);
es = apply(pr -> pr.e, dec2); if (es != [3, 12, 6], error("decomposition of 2 ", es));
al = vector(3, i, my(g = bnfisprincipal(bnf, dec2[i], 1)); if (#g[1] > 0 && g[1] != 0, error("2")); g[2]);
for (i = 1, 3, if (idealhnf(nf, al[i]) != idealhnf(nf, dec2[i]), error("gen of P", i)));
b2 = ml(al[2], al[2]); v = dv(th, b2); vi = dv(one, v);
if (!isint(v) || !isint(vi), error("v unit"));
a12 = ml(al[1], al[1]); a14 = ml(a12, a12); a32 = ml(al[3], al[3]); a33 = ml(a32, al[3]); m2 = ml(a14, a33);
w = dv(thm1, m2); wi = dv(one, w);
if (!isint(w) || !isint(wi), error("w unit"));
defl("al1", al[1]); defl("al2", al[2]); defl("al3", al[3]); defl("b2", b2); defl("v2", v); defl("v2i", vi);
defl("a12", a12); defl("a14", a14); defl("a32", a32); defl("a33", a33); defl("m2", m2); defl("w2", w); defl("w2i", wi);
mulchk("mul_b2", "al2", al[2], "al2", al[2], "b2", b2);
mulchk("mul_v2", "v2", v, "b2", b2, "thL", th);
mulchk("mul_v2i", "v2", v, "v2i", vi, "oneL", one);
mulchk("mul_a12", "al1", al[1], "al1", al[1], "a12", a12);
mulchk("mul_a14", "a12", a12, "a12", a12, "a14", a14);
mulchk("mul_a32", "al3", al[3], "al3", al[3], "a32", a32);
mulchk("mul_a33", "a32", a32, "al3", al[3], "a33", a33);
mulchk("mul_m2", "a14", a14, "a33", a33, "m2", m2);
mulchk("mul_w2", "w2", w, "m2", m2, "thm1L", thm1);
mulchk("mul_w2i", "w2", w, "w2i", wi, "oneL", one);
\\ f = X^12 (X + 1)^9 + 2 h2
P12 = x^12 * (x + 1)^9; h2 = (f - P12) / 2; if (!isint(Vec(h2)), error("f mod 2"));
listput(names, Strprintf("def mod2L : List ℤ := %s", lstr(Vecrev(P12))));
listput(names, Strprintf("def h2L : List ℤ := %s", lstr(Vecrev(h2))));
listput(checks, "theorem f_mod_two : allZero (addZ fL (smulZ (-1) (addZ mod2L (smulZ 2 h2L)))) = true := by decide +kernel");
\\ ---- p = 7: (7) = P^7, f(P) = 3, alpha^7 eps = 7
dec7 = idealprimedec(nf, 7); if (#dec7 != 1 || dec7[1].e != 7 || dec7[1].f != 3, error("7"));
g7 = bnfisprincipal(bnf, dec7[1], 1); al7 = g7[2];
b72 = ml(al7, al7); b74 = ml(b72, b72); b76 = ml(b74, b72); b77 = ml(b76, al7);
seven = nfalgtobasis(nf, 7); eps = dv(seven, b77); epsi = dv(one, eps);
if (!isint(eps) || !isint(epsi), error("eps unit"));
defl("al7", al7); defl("b72", b72); defl("b74", b74); defl("b76", b76); defl("b77", b77); defl("sevenL", seven);
defl("eps7", eps); defl("eps7i", epsi);
combochk("seven_eq", "sevenL", seven, [7]);
mulchk("mul_b72", "al7", al7, "al7", al7, "b72", b72);
mulchk("mul_b74", "b72", b72, "b72", b72, "b74", b74);
mulchk("mul_b76", "b74", b74, "b72", b72, "b76", b76);
mulchk("mul_b77", "b76", b76, "al7", al7, "b77", b77);
mulchk("mul_eps7", "b77", b77, "eps7", eps, "sevenL", seven);
mulchk("mul_eps7i", "eps7", eps, "eps7i", epsi, "oneL", one);
\\ no factor of f mod 7 of degree 1 or 2: s_e (X^(7^e) - X) = 1 mod (f, 7)
sE(p, g, e, He) = {
  my(gp = Mod(1, p) * g, Re = lift(Mod(Mod(1, p) * x, gp)^(p^e)), uv = gcdext(Re - x, gp), s);
  if (poldegree(uv[3]) != poldegree(He), error("gcd degree ", p, " ", e));
  if (uv[3] / pollead(uv[3]) != Mod(1, p) * He, error("gcd ", p, " ", e));
  s = (uv[1] * Mod(1, p) * He / uv[3]) % gp;
  if ((s * (Re - x) - He) % gp != 0, error("s check"));
  vector(n, i, lift(polcoef(s, i - 1)));
}
s71 = sE(7, f, 1, 1); s72 = sE(7, f, 2, 1);
listput(names, Strprintf("def s71 : List ℕ := %s", lstr(s71)));
listput(names, Strprintf("def s72 : List ℕ := %s", lstr(s72)));
listput(checks, "theorem fac7_1 : facCheckE 7 (negLow 7 fLow) (mkTable 7 21 (negLow 7 fLow) 20 (negLow 7 fLow)) [] 1 s71 = true := by decide +kernel");
listput(checks, "theorem fac7_2 : facCheckE 7 (negLow 7 fLow) (mkTable 7 21 (negLow 7 fLow) 20 (negLow 7 fLow)) [] 2 s72 = true := by decide +kernel");
\\ ---- p = 45613: the prime of degree 1 is (gam), N(gam) = +-p, chi(gam) = 0, theta = H(gam) / M
p45 = 45613; dec45 = idealprimedec(nf, p45);
d1 = select(pr -> pr.f == 1, dec45); if (#d1 != 1, error("45613 degree 1"));
gam = bnfisprincipal(bnf, d1[1], 1)[2];
gp45 = nfbasistoalg(nf, gam); chi = charpoly(gp45);
if (!polisirreducible(chi), error("chi"));
if (abs(polcoef(chi, 0)) != p45, error("norm"));
if (maxabs(gam) > 2^100, error("gam bound"));
Hm = lift(modreverse(gp45)); M = denominator(content(Hm)); Hn = M * Hm;
if (subst(Hn, x, gp45) != M * Mod(x, f), error("modreverse"));
if (poldegree(Hn) > 20, error("H degree"));
\\ replay of the homogL checks: D^21 chi(G/D) = 0 mod f, D^20 Hn(G/D) = M D^20 x mod f
Gp = elt2pol(gam);
if (subst(chi, x, Mod(Gp / D, f)) != 0, error("chi check"));
if (subst(Hn, x, Mod(Gp / D, f)) != M * Mod(x, f), error("H check"));
defl("gam", gam); defl("gamW", Vecrev(Gp, n));
listput(names, Strprintf("def chiG : List ℤ := %s", lstr(Vecrev(chi)[1..n])));
listput(names, Strprintf("def HG : List ℤ := %s", lstr(Vecrev(Hn, n))));
listput(names, Strprintf("def MG : ℤ := %d", M));
listput(checks, "theorem gamW_eq : allZero (addZ (comboK gam WL) (smulZ (-1) gamW)) = true := by decide +kernel");
listput(checks, "theorem chi_gam : allZero (homogL fLow gamW DD (chiG ++ [1])) = true := by decide +kernel");
listput(checks, "theorem H_gam : allZero (addZ (homogL fLow gamW DD HG) [0, -(MG * DD ^ 20)]) = true := by decide +kernel");
listput(checks, "theorem chiG_len : chiG.length = 21 ∧ HG.length = 21 := by decide +kernel");
\\ the only root of chi mod p in F_p is 0: s (X^p - X) = X mod (chi, p)
s45 = sE(p45, chi, 1, x);
listput(names, Strprintf("def s45 : List ℕ := %s", lstr(s45)));
listput(names, "def facX : Fac := ⟨1, [0, 1], [], [], [], []⟩");
listput(checks, "theorem fac45 : facCheckE 45613 (negLow 45613 chiG) (mkTable 45613 21 (negLow 45613 chiG) 20 (negLow 45613 chiG)) [facX] 1 s45 = true := by decide +kernel");
\\ ---- output
system(concat("rm -f ", outfile));
write(outfile, "import FurioLombardo.M2.Check2");
write(outfile, "");
write(outfile, "/-! Data and kernel checks for the special primes 2, 7, 45613 (generated by code/field/class_number_special_primes.gp). -/");
write(outfile, "");
write(outfile, "namespace FurioLombardo.M2.Special");
write(outfile, "");
write(outfile, "open FurioLombardo.M2");
write(outfile, "");
for (i = 1, #names, write(outfile, names[i]); write(outfile, ""));
for (i = 1, #checks, write(outfile, checks[i]); write(outfile, ""));
write(outfile, "end FurioLombardo.M2.Special");
print("written ", #names, " definitions, ", #checks, " checks; max coordinate bits: ", vecmax(apply(v -> if (type(v) == "t_COL", exponent(maxabs(v) + 1), 0), [al[1], al[2], al[3], b2, v, vi, a14, a33, m2, w, wi, al7, b77, eps, epsi, gam])));
print("M = ", M, " (", #Str(M), " digits), H max digits ", vecmax(apply(c -> #Str(abs(c)), Vec(Hn))));
quit
