\\ fake_selmer_group_check.gp: referee computation of the fake 2-Selmer group of the two-descent, directly with
\\ nfislocalpower and nfeltsign (no hand-made square class map): every one of the 256 classes of O_S^x/O_S^x2 is
\\ tested against the norm condition and the local conditions at 2, 7 and infinity.
\\ Needs algebra_arithmetic_check.dat (basis of O_S^x/squares) and local_image_2_check.dat (three generators of Im_2).
\\ Run: gp -q -D parisizemax=4000000000 fake_selmer_group_check.gp

FAIL = 0;
chk(name, c) = if(c, print("ok   ", name), FAIL++; print("FAIL ", name));
\\ variable priorities fixed before any varlower: x > y > z > X > Y > w > a > u
[x, y, z, 'X, 'Y];
w = varlower("w"); a = varlower("a"); u = varlower("u");
A3pol = a^8+2*a^7+7*a^4-14*a^2-8*a+5;
gens = apply(g -> Mod(g, A3pol), read("algebra_arithmetic_check.dat")[1]);
IM2 = apply(g -> Mod(g, A3pol), read("local_image_2_check.dat")[1]);

\\ local conditions, each a direct test
condN(al) = issquare(norm(al));
condInf(al) = my(s = nfeltsign(nf, lift(al))); s[1] == s[2];
cond7(al) = my(ok = 0); foreach([1, 3, 7, 21], d, if(!ok && nfislocalpower(nf, P7a, lift(al*d), 2) && nfislocalpower(nf, P7b, lift(al*d), 2), ok = 1)); ok;
cond2(al) =
{
  my(ok = 0);
  forvec(e = vector(3, j, [0,1]), foreach([1, -1, 2, -2], d,
    if(!ok && nfislocalpower(nf, P2, lift(al * d * prod(j = 1, 3, IM2[j]^e[j])), 2), ok = 1)));
  ok;
}
\\ exponent vector of r on the basis gens modulo squares (0 if none)
expo(r) = my(res = 0); forvec(e = vector(8, j, [0,1]), if(res == 0 && #nfroots(nf, x^2 - lift(r * prod(j = 1, 8, gens[j]^e[j]))) > 0, res = e)); res;
\\ valuation part of the condition at 7 only (FL's version)
cond7val(al) = (nfeltval(nf, al, P7a) - nfeltval(nf, al, P7b)) % 2 == 0;

{
nf = nfinit(A3pol);
P2 = idealprimedec(nf, 2)[1];
P7 = idealprimedec(nf, 7); P7a = if(P7[1].e == 1, P7[1], P7[2]); P7b = if(P7[1].e == 7, P7[1], P7[2]);
chk("8 S-unit generators and 3 generators of Im_2 loaded", #gens == 8 && #IM2 == 3);
chk("-3 is a non-square mod 7 (so 1, 3, 7, 21 represent Q_7^x/Q_7^x2)", kronecker(3, 7) == -1);

print("== 256 classes of O_S^x/O_S^x2");
cnt = Map(); els = List(); sel = List();
tot = vector(6);
forvec(e = vector(8, j, [0,1]),
  al = prod(j = 1, 8, gens[j]^e[j]);
  n = condN(al); i2 = cond2(al); i7 = cond7(al); ii = condInf(al); v7 = cond7val(al);
  tot[1] += n; tot[2] += n && i2; tot[3] += n && i2 && i7; tot[4] += n && i2 && i7 && ii; tot[5] += n && i2 && v7; tot[6] += n && ii && i7;
  if(n && i2 && i7 && ii, listput(sel, e)));
print("   classes satisfying: norm ", tot[1], "; norm, 2 ", tot[2], "; norm, 2, 7 ", tot[3], "; norm, 2, 7, inf ", tot[4],
      "; norm, 2, valuation part at 7 (FL) ", tot[5], "; norm, 7, inf (no condition at 2) ", tot[6]);
\\ the subgroup <-1, 2, 7> inside O_S^x/O_S^x2: exponent vectors of -1, 2, 7
Er = [expo(Mod(-1, A3pol)), expo(Mod(2, A3pol)), expo(Mod(7, A3pol))];
print("   exponent vectors of -1, 2, 7 on the basis: ", Er);
chk("-1, 2, 7 lie in O_S^x/squares and are independent there", Er[1] != 0 && Er[2] != 0 && Er[3] != 0 && matrank(Mat([Er[1]~, Er[2]~, Er[3]~]) * Mod(1,2)) == 3);
selset = Set(Vec(sel));
chk("<-1, 2, 7> is contained in the set of classes satisfying all conditions",
    setsearch(selset, lift(Mod(Er[1],2))) && setsearch(selset, lift(Mod(Er[2],2))) && setsearch(selset, lift(Mod(Er[3],2))) &&
    setsearch(selset, lift(Mod(Er[1]+Er[2],2))) && setsearch(selset, lift(Mod(Er[1]+Er[3],2))) && setsearch(selset, lift(Mod(Er[2]+Er[3],2))) &&
    setsearch(selset, lift(Mod(Er[1]+Er[2]+Er[3],2))));
chk("the classes satisfying all conditions form a subgroup (closed under addition)",
    vecmin(concat([1], [setsearch(selset, lift(Mod(s1 + s2, 2))) > 0 | s1 <- Vec(selset); s2 <- Vec(selset)])) == 1);
dimAll = valuation(#selset, 2);
chk("its order is a power of 2", 2^dimAll == #selset);
print("   dimension of the classes satisfying all conditions: ", dimAll, ", modulo <-1, 2, 7>: ", dimAll - 3);
chk("dim Sel_fake = 2 (norm, 2, 7, infinity)", dimAll - 3 == 2);
chk("FL's conditions (norm, 2, valuation part at 7) also give dimension 2", tot[5] == 32);
chk("without the condition at 2 the dimension would be larger (the condition at 2 is doing the work)", tot[6] > 32);
print("   Sel_fake representatives modulo <-1,2,7> (exponent vectors): ", Vec(selset));

print("== summary: ", FAIL, " failure(s)");
system("rm -f fake_selmer_group_check.dat"); write("fake_selmer_group_check.dat", [Vec(selset), Er]);
}
