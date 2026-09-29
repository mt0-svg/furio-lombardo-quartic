\\ field_small_index_search.gp: look for a presentation of K21 with small index (Lean M1 planning).
default(parisizemax, 2*10^9); default(nbthreads, 1);
[x, y, z, X, u, w, a, t, b];
read("../earlier-computations/bruin_form.gp");
nf = nfinit(K21);
R = polredabs(K21, 1); g = R[1]; print("polredabs: ", g);
nfg = nfinit(g); print("index of polredabs = ", factor(nfg.index), " disc(g) = ", factor(poldisc(g)));
L = polredbest(K21, 1); print("polredbest: ", L[1]); print("index = ", factor(nfinit(L[1]).index));
V = polred(K21); for (i = 1, #V, my(n = nfinit(V[i])); if (poldegree(V[i]) == 21, print(i, ": index ", factor(n.index), "  maxcoef ", vecmax(abs(Vec(V[i]))))));
