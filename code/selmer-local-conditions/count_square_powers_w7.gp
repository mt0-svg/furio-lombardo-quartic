\\ count_square_powers_w7.gp: the powers al7^(2^i), i = 1 .. 6, in M1's integral basis, for the square
\\ certificate of Count/At7.lean. The certificate of count_certs.gp (Y - T^2 = al7^65 A, T^2 = al7^64 B) is kept;
\\ al7^64 enters the kernel checks as the atom w7P64 instead of a chain of 64 products (memory: the chain costs
\\ over 7 GB in the kernel). Checks: every P_{2^(i+1)} = P_{2^i}^2 in K21, both certificate identities with the
\\ atoms, the Lean data read back. Writes /tmp/sp7/At7Pow.lean (Lean defs, pasted into Count/At7.lean).
\\ Run from code/selmer-local-conditions: gp -q count_square_powers_w7.gp < /dev/null > count_square_powers_w7.out 2>&1
default(parisizemax, 10^9); default(nbthreads, 1);
read("../descent/descent_data_lib.gp");
read("../selmer-global-bound/tower_lib.gp");
LEAN = "../../FurioLombardo/";
CD = Str(LEAN, "Discharge/SelmerBasis/Count/CertData.lean");
o = Mod(1, K21);
el(l) = Mod(lift(nfbasistoalg(nf, l~)), K21);
cz(z) = {my(v = nfalgtobasis(nf, lift(z))); if (denominator(v) != 1, error("not integral")); Vec(v)};
nfail = 0;
chk(c, s) = if (c, printf("ok   %s\n", s), nfail++; printf("FAIL %s\n", s));
al = el(leandef5(Str(LEAN, "M2/SpecialData.lean"), "al7"));
p7 = idealprimedec(nf, 7)[1];
chk(idealval(nf, lift(al), p7) == 1 && idealnorm(nf, lift(al)) == 7^3, "al7 generates p7 (v = 1, norm 343)");
P = vector(7); P[1] = al;
for (i = 2, 7, P[i] = P[i - 1]^2);
for (i = 2, 7, chk(P[i] == P[i - 1]^2 && P[i] == al^(2^(i - 1)), Str("P", 2^(i - 1), " = P", 2^(i - 2), "^2 = al7^", 2^(i - 1))));
\\ the certificate of count_certs.gp, read from CertData.lean
X = el(leandef5(CD, "w7k1x")); T = el(leandef5(CD, "w7k1sqT")); A = el(leandef5(CD, "w7k1sqA")); B = el(leandef5(CD, "w7k1sqB"));
Bi = el(leandef5(CD, "w7k1sqBi")); Cb = el(leandef5(CD, "w7k1sqCb"));
chk(leandef5(CD, "w7k1sqn") == 65 && leandef5(CD, "w7k1sqm") == 64, "n = 65, m = 64");
FND = leandef5(Str(LEAN, "Discharge/M3a/DataBruin.lean"), "FnData");
\\ 4 fRev_1(t) = sum_i FE 1 i t^(6 - i) (count_certs.gp: fr4)
fr4 = sum(i = 0, 6, el(FND[2][7 - i]) * t^i);
Y = subst(lift(fr4), t, lift(X)) * o;
chk(Y - T^2 == P[7] * al * A, "Y - T^2 = P64 al A (Y = 4 fRev_1(w7k1x))");
chk(T^2 == P[7] * B, "T^2 = P64 B");
chk(B * Bi == 1 + al * Cb, "B Bi = 1 + al Cb");
chk(idealval(nf, lift(Y), p7) == 64 && idealval(nf, lift(B), p7) == 0, "v(Y) = 64, B a unit");
\\ negative control: a wrong power fails
chk(T^2 != P[6] * B, "negative control: T^2 != P32 B");
out = "";
for (i = 2, 7, out = Str(out, "def w7P", 2^(i - 1), " : List ℤ := ", lst(cz(P[i])), "\n\n"));
system("mkdir -p /tmp/sp7"); f = "/tmp/sp7/At7Pow.lean"; system(Str("rm -f ", f)); write1(f, out);
for (i = 2, 7, chk(el(cz(P[i])) == P[i], Str("P", 2^(i - 1), " read back")));
printf("max digits of the P coordinates: %s\n", vector(6, i, #Str(vecmax(abs(cz(P[i + 1]))))));
printf("checks failed: %d\n", nfail);
print("DONE");
