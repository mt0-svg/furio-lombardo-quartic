\\ irreducibility_eisenstein7.gp: identities for the irreducibility of f by the generalized Eisenstein criterion at 7.
default(parisizemax, 10^9); default(nbthreads, 1);
f = x^21 - 7*x^20 + 14*x^19 - 84*x^16 + 98*x^15 + 2*x^14 + 175*x^13 - 609*x^12 + 980*x^11 - 770*x^10 - 280*x^9 + 1008*x^8 - 1072*x^7 + 560*x^6 + 28*x^5 - 336*x^4 + 252*x^3 - 112*x^2 + 28*x - 4;
q = x^3 + 2*x^2 - x - 4;
h = (f - q^7)/7; if (denominator(content(h)) != 1, error("h"));
print("h = ", h);
s = f \ q; r = f % q; print("s = ", s); print("r = ", r);
print("r coeffs mod 49: ", Vec(r) % 49);
[U, V, R] = polresultantext(f, deriv(f)); print("R = ", R, " denominators ", denominator(content(U)), " ", denominator(content(V)));
d = lcm(denominator(content(U)), denominator(content(V))); print("d = ", factor(d));
quit
