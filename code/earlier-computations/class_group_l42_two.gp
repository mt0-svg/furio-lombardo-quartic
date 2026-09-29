\\ class_group_l42_two.gp: removing GRH from L(S,2) in the Richelot descent over K21 (L = K21(sqrt d), degree 42).
\\
\\ Claim 1 (Cl(L)[2] = 0, given h(K21) odd). Ambiguous class number formula for the quadratic extension L/K:
\\   |Cl(L)^G| = h(K) 2^(t-1) / [E_K : E_K cap N(L^x)],  t = number of places of K ramified in L (finite and real).
\\ A unit is a norm from L iff it is a local norm at every place (Hasse), and at unramified finite places units are
\\ local norms, so [E_K : E_K cap N] = size of the image of E_K/E_K^2 -> (+-1)^t, u -> ((u, d)_v)_v ramified.
\\ If that image has size 2^(t-1) and h(K) is odd, |Cl(L)^G| is odd; a nontrivial 2-group with an action of a group
\\ of order 2 has a nontrivial fixed point, so the 2-part of Cl(L) is trivial.
\\ E_K/E_K^2 unconditionally: dim = r1 + r2 = 12 (Dirichlet, -1 included); any 12 units of K independent modulo
\\ squares (certified by quadratic characters at auxiliary primes: a character matrix of rank 12) span it.
\\ Claim 2 (L(S,2) = O_{L,S}^x / squares, spanned by explicit S-units). With Cl(L)[2] = 0, the exact sequence
\\ 0 -> O_S^x/squares -> L(S,2) -> Cl_S(L)[2] gives equality, of dimension r1(L) + r2(L) + #S_L (Dirichlet, -1
\\ included). The S-units computed by bnfsunit (under GRH) are exact elements; if they are independent modulo squares
\\ (character matrix of full rank) and their number equals that dimension, they span L(S,2) unconditionally.
\\ Remaining input: h(K21) odd (bnfcertify in p21_15_k21cert.gp, or GRH).
\\ Run from code/earlier-computations: gp -q class_group_l42_two.gp < /dev/null
default(parisizemax, 6*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
read("richelot_data.gp");
read("field_l42_polynomial.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
d = Mod(RIN[1][5], K21);
d = d * denominator(content(lift(d)))^2;   \\ integral representative of the same square class (rnfdisc needs an integral polynomial)
bnfK = bnfinit(nfinit([K21, [2, 7]]), 1); nfK = bnfK.nf;
\\ quadratic characters of elements of a number field at degree one primes p (not dividing the elements), as F2 rows
charmat(nf, els, nprimes) = {
  my(rows = List(), cnt = 0);
  forprime(p = 101, 10^7,
    if (cnt >= nprimes, break);
    my(dec = idealprimedec(nf, p));
    for (j = 1, #dec, my(pr = dec[j]);
      if (pr.f != 1 || pr.e != 1 || cnt >= nprimes, next);
      my(ok = 1, row = vector(#els));
      for (i = 1, #els, my(v = idealval(nf, els[i], pr)); if (v != 0, ok = 0; break);
        my(r = nfmodpr(nf, els[i], nfmodprinit(nf, pr)));
        row[i] = if (issquare(r), 0, 1));
      if (ok, listput(rows, row); cnt++)));
  matrix(#rows, #els, i, j, rows[i][j]);
}
\\ Claim 1
EK = concat([bnfK.tu[2]], bnfK.fu);
chk(#EK == nfK.sign[1] + nfK.sign[2], Str("E_K/E_K^2 candidate basis of size r1 + r2 = ", #EK));
for (i = 1, #EK, if (abs(norm(Mod(lift(EK[i]), K21))) != 1, error("not a unit")));
Mk = charmat(nfK, apply(e -> lift(e), EK), 3 * #EK);
chk(matrank(Mod(Mk, 2)) == #EK, "the 12 units are independent modulo squares (character matrix of rank 12): they span E_K/E_K^2");
rd = rnfdisc(nfK, u^2 - lift(d));
ramf = idealfactor(nfK, rd[1]);
ramfin = vector(#ramf~, j, ramf[j, 1]);
print("finite primes of K21 ramified in L: ", vector(#ramfin, j, [ramfin[j].p, ramfin[j].f, ramfin[j].e]));
emb = nfeltsign(nfK, lift(d));
ramreal = [j | j <- [1..#emb], emb[j] < 0];
print("real places of K21 ramified in L (d < 0): ", ramreal);
tt = #ramfin + #ramreal;
\\ symbol matrix: rows = units, columns = ramified places, entries in F2
Hs = matrix(#EK, tt);
{
for (i = 1, #EK, for (j = 1, tt,
  Hs[i, j] = if (j <= #ramfin, (1 - nfhilbert(nfK, lift(EK[i]), lift(d), ramfin[j])) / 2, nfeltsign(nfK, lift(EK[i]), ramreal[j - #ramfin]) < 0)));
}
rk = matrank(Mod(Hs, 2));
print("t = ", tt, " ramified places; rank of the unit symbol matrix = ", rk);
chk(rk == tt - 1, "[E_K : E_K cap N(L^x)] = 2^(t-1): |Cl(L)^G| = h(K21), so Cl(L)[2] = 0 as soon as h(K21) is odd");
\\ Claim 2
bnfL = bnfinit(nfinit([Lpol, [2, 7]]), 1); nfL = bnfL.nf;
SL = concat(idealprimedec(nfL, 2), idealprimedec(nfL, 7));
su = bnfsunit(bnfL, SL);
gens = concat(concat([bnfL.tu[2]], bnfL.fu), su[1]);
dimexp = nfL.sign[1] + nfL.sign[2] + #SL;
print("L: signature ", nfL.sign, ", #S_L = ", #SL, " (above 2: ", #idealprimedec(nfL, 2), ", above 7: ", #idealprimedec(nfL, 7), "); expected dim L(S,2) = ", dimexp, "; generators ", #gens);
chk(#gens == dimexp, "number of S-unit generators = r1 + r2 + #S_L");
for (i = 1, #gens, my(fa = idealfactor(nfL, gens[i])); for (j = 1, #fa~, if (fa[j, 1].p != 2 && fa[j, 1].p != 7, error("generator not an S-unit"))));
ML = charmat(nfL, apply(e -> lift(e), gens), 2 * #gens + 20);
chk(matrank(Mod(ML, 2)) == #gens, Str("the ", #gens, " S-units are independent modulo squares: they span O_S^x/squares = L(S,2) (given Cl(L)[2] = 0)"));
quit;
