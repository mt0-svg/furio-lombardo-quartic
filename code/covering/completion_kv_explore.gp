\\ completion_kv_explore.gp: the Eisenstein cubic E of completion_kv.gp, the embedding theta*, and valuations (exploration for the
\\ Lean model of K_v in lean/FurioLombardo/Discharge/M4Cert). Run from code/earlier-computations.
default(parisizemax, 2*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("bruin_form.gp");
nfK = nfinit([K21, [2, 7]]);
pr = [q | q <- idealprimedec(nfK, 2), q.e == 3][1];
read("completion_kv.gp");
r = kv_init(400);
print("E = ", r[1]);
print("prec of theta = ", r[2], "  vK = ", r[3], "  vD = ", r[4]);
E = r[1];
print("E integral: ", denominator(content(E)) == 1, "  coeffs: ", Vec(E));
print("pr.gen[2] = ", nfbasistoalg(nfK, pr.gen[2]));
print("delta0 val at pr: ", nfeltval(nfK, d0, pr), "  delta1: ", nfeltval(nfK, d1, pr));
print("den(d0) = ", denominator(content(lift(d0))), " den Q1 = ", denominator(content(lift(Q1))));
