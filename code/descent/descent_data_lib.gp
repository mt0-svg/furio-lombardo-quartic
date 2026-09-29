\\ descent_data_lib.gp: shared setup for the M1 Lean certificate generators (code/descent/m1_p_*.gp).
\\ K21 = Q[b]/(K21(b)) from ../earlier-computations/bruin_form.gp; nf = nfinit (maximal order used only to FIND data,
\\ every datum is rechecked in Lean); zk = PARI's integral basis, used as the Z-lattice Lambda of the Lean files.
\\ (the caller sets parisizemax and nbthreads: a default() inside read() aborts the read)
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
nf = nfinit(K21);
zk = nf.zk;
Dz = lcm(vector(21, j, denominator(content(zk[j]))));
zkNum = vector(21, j, Vecrev(zk[j] * Dz, 21));            \\ power basis numerators over Dz, constant first
zkc(e) = nfalgtobasis(nf, lift(Mod(e, K21)));             \\ zk coordinates (column)
zkr(v) = nfbasistoalg(nf, if (type(v) == "t_VEC", v~, v));  \\ element from zk coordinates
zv(v) = if (type(v) == "t_COL", v, nfalgtobasis(nf, v));
tab = vector(21, i, vector(21, j, zv(nfeltmul(nf, vectorv(21, k, k == i), vectorv(21, k, k == j)))));
mulz(u, v) = zv(nfeltmul(nf, u, v));
powz(u, n) = zv(nfeltpow(nf, u, n));
\\ Lean list syntax
lst(v) = { my(s = "["); for (i = 1, #v, s = Str(s, v[i], if (i < #v, ", ", ""))); Str(s, "]") };
lstl(V) = { my(s = "["); for (i = 1, #V, s = Str(s, lst(V[i]), if (i < #V, ",\n  ", ""))); Str(s, "]") };
\\ the quadric coefficients on x^2, xy, xz, y^2, yz, z^2
mons2 = [[2,0,0], [1,1,0], [1,0,1], [0,2,0], [0,1,1], [0,0,2]];
cf(Q, i, j, k) = polcoef(polcoef(polcoef(Q, i, x), j, y), k, z);
coefs2(Q) = vector(6, j, Mod(cf(Q, mons2[j][1], mons2[j][2], mons2[j][3]), K21));
Qs = [Q1, Q2, Q3]; Qc = vector(3, i, coefs2(Qs[i]));
QcZ = vector(3, i, vector(6, j, zkc(Qc[i][j])));
