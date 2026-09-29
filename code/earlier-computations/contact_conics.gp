\\ Contact conics of C through the rational point P0 = (0:0:1): conics Q with Q.C = 2E, P0 in E.
\\ One for each nonzero 2-torsion point eta ([E - H] = eta), 63 in all, in Galois orbits 28 + 14 + 21.
\\ Chart z = 1; tangent line of C at P0 is 2x + 5y = 0; Q = 2x + 5y + q3 x^2 + q4 x y + q5 y^2 (P0 on no
\\ bitangent assumed, then no genuine solution is singular at P0 and double lines are excluded).
\\ Condition: R(x) = Res_y(f, Q) = x^2 * lc * S(x)^2, S = x^3 + a2 x^2 + a1 x + a0.
\\ Writes the msolve input contact_conics_p0.ms.  Run: gp -q contact_conics.gp < /dev/null
default(parisizemax, 2*10^9); default(nbthreads, 1);
[x, y, z, q3, q4, q5, a0, a1, a2];
F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
f = subst(F, z, 1);
print("linear part of f at P0: ", polcoef(polcoef(f,1,x),0,y)*x + polcoef(polcoef(f,0,x),1,y)*y);
Q = 2*x + 5*y + q3*x^2 + q4*x*y + q5*y^2;
R = polresultant(f, Q, y);
print("x^2 divides R: ", polcoef(R, 0, x) == 0 && polcoef(R, 1, x) == 0);
R2 = R \ x^2;
d = poldegree(R2, x); print("degree of R/x^2 in x: ", d);
lc = polcoef(R2, 6, x);
S = x^3 + a2*x^2 + a1*x + a0;
E = R2 - lc*S^2;
eqs = vector(6, i, polcoef(E, i-1, x));
{
  my(fn = "contact_conics_p0.ms");
  write1(fn, "q3,q4,q5,a0,a1,a2\n0\n");
  for (i = 1, 6, write1(fn, Str(eqs[i]), if (i < 6, ",\n", "\n")));
}
print("written; total degrees: ", vector(6, i, poldegree(subst(subst(subst(subst(subst(subst(eqs[i], q3, 'T*q3), q4, 'T*q4), q5, 'T*q5), a0, 'T*a0), a1, 'T*a1), a2, 'T*a2), 'T)));
quit;
