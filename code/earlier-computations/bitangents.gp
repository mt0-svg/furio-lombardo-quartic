\\ Bitangents of C: lines y = m x + k (chart z = 1) with F(x, m x + k, 1) = g4 (x^2 + p x + q)^2.
\\ Exact polynomial of the slopes, then numerical bitangents at high precision.
\\ Run: gp -q bitangents.gp < /dev/null
default(parisizemax, 4*10^9); default(nbthreads, 1);
[x, y, z, m, k, X];
F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
g = subst(subst(F, z, 1), y, m*x + k);
gc = vector(5, i, polcoef(g, i - 1, x));      \\ g0..g4
[g0, g1, g2, g3, g4] = gc;
\\ p = g3/(2 g4), q = (g2/g4 - p^2)/2;  g1 = 2 g4 p q, g0 = g4 q^2
\\ multiply out: with P = g3, 8 g4^2 q = 4 g2 g4 - g3^2
E1 = 8*g4^2*g1 - g3*(4*g2*g4 - g3^2);          \\ = 8 g4^2 (g1 - 2 g4 p q)
E0 = 64*g4^3*g0 - (4*g2*g4 - g3^2)^2;          \\ = 64 g4^3 (g0 - g4 q^2)
print("degrees in k: ", poldegree(E1, k), " ", poldegree(E0, k));
Rm = polresultant(E1, E0, k);
fa = factor(Rm);
print("factors of the resultant in m: ", vector(#fa~, i, [poldegree(fa[i,1]), fa[i,2]]));
quit;
