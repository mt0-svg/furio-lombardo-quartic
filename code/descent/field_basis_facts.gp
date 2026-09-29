\\ field_basis_facts.gp: basic data of K21 for the Lean files of M1 (index, integral basis, factorization patterns).
default(parisizemax, 2*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
nf = nfinit(K21);
print("disc(f) = ", factor(poldisc(K21)));
print("disc(K) = ", factor(nf.disc));
print("index = ", factor(nf.index));
print("zk denominators = ", vector(21, i, denominator(content(nf.zk[i]))));
print("sign = ", nf.sign);
print("real roots (polsturm) = ", polsturm(K21));
print("coeffs = ", Vec(K21));
forprime(p = 3, 200, if (p == 7, next); my(fa = factormod(K21, p, 1)); print(p, ": ", vecsort(vector(#fa~, i, poldegree(fa[i,1])))));
