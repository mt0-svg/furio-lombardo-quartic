\\ dyadic_nonnorm_kat.gp: known-answer counts for the Lean certificate DyadicCert.lean (R = (Z/4)[x]/(x^3 + 2), D = 1 + 2 x^2).
\\ Run from code/selmer-global-bound: gp -q dyadic_nonnorm_kat.gp < /dev/null. Output: 128, 0, 504.
default(parisizemax, 10^8); default(nbthreads, 1);
Er = Mod(x^3 + 2, 4);
rmul(p, q) = { my(r = lift(lift(Mod(Pol(Mod(Vecrev(p), 4), 'x) * Pol(Mod(Vecrev(q), 4), 'x), subst(Er, variable(Er), 'x))))); vector(3, i, lift(Mod(polcoef(r, i - 1, 'x), 4))); }
radd(p, q) = vector(3, i, (p[i] + q[i]) % 4);
rneg(p) = vector(3, i, (4 - p[i]) % 4);
one = [1, 0, 0]; U = [3,3,3]; D = [1,0,2];
R = List(); forvec(c = [[0, 3], [0, 3], [0, 3]], listput(R, c)); R = Vec(R);
\\ normalised solutions with c = 1, u = 1: 1 = a^2 - D b^2
n1 = 0; for (ia = 1, 64, for (ib = 1, 64, if (one == radd(rmul(R[ia], R[ia]), rneg(rmul(D, rmul(R[ib], R[ib])))), n1++)));
print("u = 1, c = 1: ", n1);
\\ with u = U, c = 1 (must be 0)
n2 = 0; for (ia = 1, 64, for (ib = 1, 64, if (U == radd(rmul(R[ia], R[ia]), rneg(rmul(D, rmul(R[ib], R[ib])))), n2++)));
print("u = U, c = 1: ", n2);
\\ total normalised for u = 1
n3 = 0; for (ia = 1, 64, for (ib = 1, 64, for (ic = 1, 64, if (R[ia] == one || R[ib] == one || R[ic] == one, if (rmul(R[ic], R[ic]) == radd(rmul(R[ia], R[ia]), rneg(rmul(D, rmul(R[ib], R[ib])))), n3++)))));
print("u = 1 total normalised: ", n3);
quit;
