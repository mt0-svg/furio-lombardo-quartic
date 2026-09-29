\\ divisor_r_comparison.gp: comparison of the referee's R with the degree 3 divisor R printed by Furio-Lombardo
\\ (in the file Output/DoDescent.out of their code 7-adic-representations, X_{E_3}); FL's coordinates (X, Y, Z) = (x, z, y).
\\ Needs geometry_check.dat. Run: gp -q divisor_r_comparison.gp
FAIL = 0;
chk(name, c) = if(c, print("ok   ", name), FAIL++; print("FAIL ", name));
[x, y, z, 'X, 'Y];
w = varlower("w"); a = varlower("a"); u = varlower("u");
GEOM = read("geometry_check.dat"); r3 = GEOM[3]; yR = GEOM[4];
{
FLI = ['X^2 + 19/242*'X*'Z - 625/242*'Y*'Z + 205/121*'Z^2, 'X*'Y + 47/242*'X*'Z - 145/242*'Y*'Z + 125/121*'Z^2,
       'X*'Z + 30250/13463*'Y^2 - 18725/13463*'Y*'Z + 4346/13463*'Z^2];
pt = [Mod(u, subst(r3, x, u)), 1, Mod(yR, subst(r3, x, u))];   \\ (X, Y, Z) = (x, z, y) at the points of R
chk("the three points of the referee's R satisfy FL's three quadrics", vecmax(apply(q -> q != 0, [subst(subst(subst(q, 'X, pt[1]), 'Y, pt[2]), 'Z, pt[3]) | q <- FLI])) == 0);
FLF = 'X^4 + 3*'X^3*'Z - 3*'X^2*'Y^2 - 3*'X^2*'Y*'Z - 2*'X*'Y^3 + 3*'X*'Y^2*'Z - 6*'X*'Y*'Z^2 + 6*'X*'Z^3 - 5*'Y^3*'Z + 2*'Y*'Z^3 + 4*'Z^4;
F = x^4+3*x^3*y-3*x^2*y*z-3*x^2*z^2+6*x*y^3-6*x*y^2*z+3*x*y*z^2-2*x*z^3+4*y^4+2*y^3*z-5*y*z^3;
chk("FL's quartic is F with y and z swapped", subst(subst(subst(FLF, 'X, x), 'Y, z), 'Z, y) == F);
print("== summary: ", FAIL, " failure(s)");
}
