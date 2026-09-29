\\ Kernel timing probe data for the F_2 bitmask checkers of Echelon.lean at the size of the
\\ global system (164 x 82): a random full column rank matrix (leftInvOK) and a random matrix of
\\ rank 63 (kerSpanOK with the kernel basis as W). Output: Lean definitions on stdout.
setrand(20260928);
m = 164; n = 82;
bits(v) = sum(j = 1, #v, lift(v[j]) * 2^(j-1));
rowmask(M, i) = bits(M[i, ]);
\\ full column rank
until(matrank(A) == n, A = matrix(m, n, i, j, Mod(random(2), 2)));
\\ left inverse: for each k, c with c * A = e_k (c on m bits)
Ix = matindexrank(A)[1]; B = matrix(n, n, a, j, A[Ix[a], j]); L = B^(-1);
T = vector(n, k, sum(a = 1, n, lift(L[k, a]) * 2^(Ix[a]-1)));
\\ check in gp: xor of rows selected by T[k] equals 2^(k-1)
ok = 1; for (k = 1, n, my(s = 0); for (i = 1, m, if (bittest(T[k], i-1), s = bitxor(s, rowmask(A, i)))); if (s != 2^(k-1), ok = 0));
print("-- leftInvOK data: ", if (ok, "gp check passed", "gp check FAILED"));
print("def pR : ℕ → ℕ := fun i => [", strjoin(vector(m, i, Str(rowmask(A, i))), ", "), "].getD i 0");
print("def pT : ℕ → ℕ := fun k => [", strjoin(vector(n, k, Str(T[k])), ", "), "].getD k 0");
\\ kerSpanOK data: rank 63
q = 63;
until(matrank(M) == q, M = matrix(m, q, i, j, Mod(random(2), 2)) * matrix(q, n, i, j, Mod(random(2), 2)));
cr = matindexrank(M); piv = cr[2]; rows = cr[1];
Mp = matrix(q, q, a, b, M[rows[a], piv[b]]); L = Mp^(-1);
TK = vector(q, k, sum(a = 1, q, lift(L[k, a]) * 2^(rows[a]-1)));
Rp = vector(q, k, sum(a = 1, q, L[k, a] * M[rows[a], ]));
free = setminus([1..n], Set(piv));
fv(j) = my(s = 2^(j-1)); for (k = 1, q, if (Rp[k][j] == 1, s = bitxor(s, 2^(piv[k]-1)))); s;
W = vector(#free, a, fv(free[a]));
\\ check: every W vector is in the kernel of M
okk = 1; for (a = 1, #free, my(x = vectorv(n, j, Mod(bittest(W[a], j-1), 2))); if (M * x != 0, okk = 0));
print("-- kerSpanOK data: q = ", q, ", free columns ", #free, ", kernel check ", if (okk, "passed", "FAILED"));
U = vector(n, j, my(ix = setsearch(Set(free), j)); if (ix, 2^(ix-1), 0));
print("def kM : ℕ → ℕ := fun i => [", strjoin(vector(m, i, Str(rowmask(M, i))), ", "), "].getD i 0");
print("def kT : ℕ → ℕ := fun k => [", strjoin(vector(q, k, Str(TK[k])), ", "), "].getD k 0");
print("def kpiv : ℕ → ℕ := fun k => [", strjoin(vector(q, k, Str(piv[k]-1)), ", "), "].getD k 0");
print("def kW : ℕ → ℕ := fun l => [", strjoin(vector(#free, a, Str(W[a])), ", "), "].getD l 0");
print("def kU : ℕ → ℕ := fun j => [", strjoin(vector(n, j, Str(U[j])), ", "), "].getD j 0");
