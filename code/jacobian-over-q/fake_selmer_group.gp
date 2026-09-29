\\ Step 4 of the 2-descent: the fake 2-Selmer group.
\\ Run from code/jacobian-over-q:  gp -q -D parisizemax=4000000000 two_descent_lib.gp two_descent_local_images.gp fake_selmer_group.gp
\\ (two_descent_local_images.gp provides Im2, Im7, Iminf: bases of the local images plus the images of Q_p^x.)
chk(b, s) = if (!b, error("CHECK FAILED: ", s), print("ok  ", s));
print("== global data");
chk(bnf.no == 1, "h(A3) = 1");
chk(bnfcertify(bnf) == 1, "bnfcertify: class group and units certified (no GRH)");
chk(#Sgens == 8, "O_S^x / squares has dimension 8 (3 S-generators, 4 fundamental units, -1)");
chk(Sgens[8] == -1 || Sgens[8] == Mod(-1, A3), "the torsion generator is -1");
\\ exponent vectors of -1, 2, 7 (no rational normalisation here)
rat = [-1, 2, 7];
ratv = vector(3, i, lift(bnfisunit(bnf, rat[i], Uobj)~ * Mod(1, 2)));
chk(f2rank(Mat(apply(v -> v~, ratv))) == 3, "-1, 2, 7 are independent in A3^x / squares (A3 has no quadratic subfield)");
print("   A(S,2) = O_S^x/O_S^x2 (h = 1), and the classes of A3^x/A3^x2 Q^x unramified outside {2,7} form A(S,2)/<-1,2,7>, dim 5");

print("== conditions");
\\ norm character: N(b) in Q^x / Q^x2, restricted to {+-2^i 7^j}: (sign, v_2 mod 2, v_7 mod 2)
normv(b) = { my(n = nfeltnorm(bnf, b)); [n < 0, valuation(n, 2) % 2, valuation(n, 7) % 2]; }
{
  my(Y2 = annih(Im2), Y7 = annih(Im7), Yi = annih(Iminf), rows = List(), cond, K, nr, n2, n7, ni);
  for (k = 1, 3, listput(rows, vector(8, i, normv(Sgens[i])[k])));
  nr = #rows;
  for (k = 1, #Y2~, listput(rows, vector(8, i, (Y2[k, ] * cl2(Sgens[i])~) % 2)));
  n2 = #rows;
  for (k = 1, #Y7~, listput(rows, vector(8, i, (Y7[k, ] * cl7(Sgens[i])~) % 2)));
  n7 = #rows;
  for (k = 1, #Yi~, listput(rows, vector(8, i, (Yi[k, ] * clinf(Sgens[i])~) % 2)));
  ni = #rows;
  print("   number of linear conditions: norm ", nr, ", at 2 ", n2 - nr, ", at 7 ", n7 - n2, ", at infinity ", ni - n7);
  cond = matrix(#rows, 8, i, j, rows[i][j]);
  \\ the rational classes satisfy all conditions
  chk(cond * Mat(apply(v -> v~, ratv)) % 2 == 0, "-1, 2, 7 satisfy every condition (as they must)");
  K = lift(matker(cond * Mod(1, 2)));
  SelK = K;
  print("   kernel in A(S,2): dimension ", #K);
  chk(#K - 3 == 2, "dim Sel_fake = dim(kernel) - dim <-1,2,7> = 2");
  \\ the same with fewer conditions, for comparison
  my(sub = (r1, r2) -> #matker(matrix(r2 - r1 + 1, 8, i, j, rows[r1 + i - 1][j]) * Mod(1, 2)) - 3);
  print("   norm only: ", sub(1, nr), "; norm + at 2: ", sub(1, n2), "; norm + at 2 + at 7: ", sub(1, n7), "; all: ", sub(1, ni));
  \\ Furio-Lombardo's version: norm, condition at 2, and only the valuation part of the condition at 7
  my(val7 = vector(8, i, (nfeltval(bnf, Sgens[i], P7a) + nfeltval(bnf, Sgens[i], P7b)) % 2), M);
  M = matrix(n2 + 1, 8, i, j, if (i <= n2, rows[i][j], val7[j]));
  print("   norm + at 2 + (v_P7a = v_P7b mod 2), the conditions of DoDescent.m: dimension ", #matker(M * Mod(1, 2)) - 3);
}
print("step 4 done");
